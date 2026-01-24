-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.
{-# LANGUAGE FlexibleContexts, BlockArguments, LambdaCase, DerivingStrategies, OverloadedStrings, NondecreasingIndentation #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
module HTML.Backend
  ( compileOneModule
  , defaultHtmlOptions
  ) where

import HTML.Base

import Prelude hiding ((!!), concatMap)

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.List.NonEmpty (NonEmpty((:|)))
import Data.IntMap.Strict (IntMap)
import Data.Foldable
import Data.Text (Text)
import Data.Set (Set)

import Agda.Compiler.Backend hiding (topLevelModuleName)
import Agda.Compiler.Common

import Control.DeepSeq

import qualified Agda.Syntax.Internal.Generic as I
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Common.Aspect as Asp
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract as A

import Agda.Syntax.Translation.InternalToAbstract ( Reify(reify) )
import Agda.Syntax.Abstract.Pretty (prettyATop)
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Abstract hiding (Type)
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Info

import qualified Agda.TypeChecking.Monad.Base as I
import qualified Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.Records (isRecord)
import Agda.TypeChecking.Reduce (normalise)

import HTML.Render

genModTypes :: HtmlOptions -> [Definition] -> IntMap Identifier -> TCM (IntMap Identifier)
genModTypes opts (def:defs) !acc
  | not (htmlOptGenTypes opts) = genModTypes opts defs acc
  | Just (pos, mn) <- definitionAnchor def = do
    (tooltip, ty) <- typeToText def
    let
      ident = Identifier
        { idAnchor  = mn
        , idIdent   = Text.pack (render (pretty (qnameName (defName def))))
        , idType    = ty
        , idTooltip = tooltip
        }
    rnf tooltip `seq` rnf ty `seq` genModTypes opts defs (IntMap.insert pos ident acc)
  | otherwise = genModTypes opts defs acc
genModTypes _opts [] !acc = pure acc

-- | Compile a single module, given an existing set of types.
compileOneModule
  :: FilePath
  -> HtmlOptions
  -> Interface -- ^ The interface to compile.
  -> TCM ()
compileOneModule _pn opts iface = do
  setInterface iface

  defs <- map snd . sortDefs <$> curDefs
  types <- genModTypes opts defs mempty

  let
    mod = HtmlModule types (map (render . pretty . fst) (iImportedModules iface))

  defaultPageGen opts mod $ srcFileOfInterface iface

getClass :: QName -> TCM (Set QName)
getClass q = isRecord q >>= \case
  Just RecordData{ _recFields = f } -> pure $! Set.fromList (map I.unDom f)
  _ -> pure mempty

usedInstances :: I.TermLike a => a -> TCM (Set QName)
usedInstances = I.foldTerm \case
  I.Def q _ -> do
    def <- getConstInfo q
    case Agda.Compiler.Backend.defInstance def of
      Just c  -> Set.insert q <$> getClass (instanceClass c)
      Nothing -> pure mempty
  _ -> pure mempty

typeToText :: Definition -> TCM (Text, Text)
typeToText d = do
  ui <- usedInstances (I.unEl (defType d))

  ty <- locallyReduceDefs (OnlyReduceDefs ui) $ normalise (defType d)

  let
    n k = Asp.Name (Just k) False
    asp = \case
      I.Axiom{}          -> n Asp.Postulate
      DataOrRecSig{}     -> n Asp.Datatype
      GeneralizableVar{} -> n Asp.Generalizable
      AbstractDefn d     -> asp d
      d@Function{}
        | isProperProjection d -> n Asp.Field
        | otherwise -> n Asp.Function
      Datatype{}         -> n Asp.Datatype
      Record{}           -> n Asp.Record{}
      Constructor{conSrcCon = c} ->
        n $ Asp.Constructor (I.conInductive c)
      I.Primitive{} -> n Asp.Primitive
      PrimitiveSort{} -> Asp.PrimitiveType

    aspect = asp (theDef d)

    a = Asp.Aspects
      { Asp.aspect         = Just aspect
      , Asp.otherAspects   = mempty
      , Asp.note           = ""
      , Asp.definitionSite = Nothing
      , Asp.tokenBased     = Asp.TokenBased
      }

  expr <- removeImpls <$> reify ty

  tooltip <- fmap renderToHtml $ P.vcat
    [ annotate a <$> P.pretty (qnameName (defName d))
    , P.nest 2 (P.colon P.<+> prettyATop expr)
    ]
  plain <- Text.pack . render <$> prettyATop expr
  pure (tooltip, plain)

removeImpls :: A.Expr -> A.Expr
removeImpls (A.Pi _ (x :| xs) e) =
  let
    fixup :: TypedBinding -> TypedBinding
    fixup q@(TBind rng inf as _)
      | Hidden <- getHiding q = TBind rng inf as underscore
      | otherwise = q
    fixup q = q
  in makePi (map (A.mapExpr removeImpls) $ map fixup (x:xs)) (removeImpls e)
removeImpls (A.Fun span arg ret) =
  A.Fun span (removeImpls <$> arg) (removeImpls ret)
removeImpls e = e

makePi :: [A.TypedBinding] -> A.Expr -> A.Expr
makePi [] e = e
makePi (b:bs) (A.Pi _ bs' e') = makePi (b:bs ++ toList bs') e'
makePi (b:bs) e = A.Pi exprNoRange (b `mergeTBinds` bs) e

mergeTBinds :: A.TypedBinding -> [A.TypedBinding] -> NonEmpty A.TypedBinding
mergeTBinds (A.TBind r i as Underscore{}) (A.TBind _ _ as' Underscore{}:bs) =
  mergeTBinds (A.TBind r i (as <> as') underscore) bs
mergeTBinds x xs = x :| xs

definitionAnchor :: Definition -> Maybe (Int, Text)
definitionAnchor def
  | defCopy def                        = Nothing
  | isExtendedLambdaName (defName def) = Nothing
  | isAbsurdLambdaName (defName def)   = Nothing
  | isWithFunction (theDef def)        = Nothing
definitionAnchor def = f =<< go where
  go :: Maybe FilePath
  go = do
    let name = defName def
    case rangeModule (nameBindingSite (qnameName name)) of
      Just f -> Just (modToFile f "html")
      Nothing -> Nothing
  f modn =
    case rStart (nameBindingSite (qnameName (defName def))) of
      Just pn ->
        let out = Text.pack (modn <> "#" <> show (posPos pn))
         in rnf out `seq` pure (fromIntegral (posPos pn), out)
      Nothing -> Nothing
