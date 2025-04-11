-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.
{-# LANGUAGE FlexibleContexts, BlockArguments, LambdaCase, OverloadedStrings, NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
module HTML.Backend
  ( compileOneModule
  , defaultHtmlOptions
  ) where

import HTML.Base

import Prelude hiding ((!!), concatMap)

import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader ()
import Control.Exception
import Control.Monad

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.IntMap.Strict (IntMap)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Map.Strict (Map)
import Data.Foldable
import Data.HashSet (HashSet)
import Data.String
import Data.Aeson
import Data.Maybe
import Data.IORef
import Data.Text (Text)
import Data.List
import Data.Set (Set)

import Agda.Compiler.Backend hiding (topLevelModuleName)
import Agda.Compiler.Common

import Control.DeepSeq

import qualified Agda.Syntax.Concrete.Generic as Con
import qualified Agda.Syntax.Internal.Generic as I
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Common.Aspect as Asp
import qualified Agda.Syntax.Scope.Base as Scope
import qualified Agda.Syntax.Concrete as Con
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C

import Agda.Syntax.Translation.InternalToAbstract ( Reify(reify) )
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_, abstractToConcreteCtx)
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Abstract.Pretty (prettyA, prettyATop)
import Agda.Syntax.Internal.Names
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Scope.Monad (modifyCurrentScope, getCurrentModule, freshConcreteName)
import Agda.Syntax.Abstract hiding (Type)
import Agda.Syntax.Position
import Agda.Syntax.Internal (Type, domName)
import Agda.Syntax.Fixity (Precedence(TopCtx))
import Agda.Syntax.Common
import Agda.Syntax.Info

import qualified Agda.TypeChecking.Monad.Base as I
import qualified Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records (isRecord)
import Agda.TypeChecking.Reduce (instantiateFull, reduceDefCopyTCM, normalise)
import Agda.TypeChecking.Level (reallyUnLevelView)

import Agda.Interaction.BasicOps

import qualified Agda.Utils.Maybe.Strict as S
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Size
import Agda.Utils.Null

import System.FilePath hiding (normalise)

import Text.Show.Pretty (ppShow)

import HTML.Render
import Debug.Trace (traceShow)
import Agda.Syntax.Internal.Names (namesIn')
import Agda.Interaction.Response (Response_boot(Resp_RunningInfo))
import Agda.Interaction.Options.Lenses (LensVerbosity(setVerbosity))

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
genModTypes opts [] !acc = pure acc

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
    ins Nothing       = id
    ins (Just (a, b)) = IntMap.insert a b

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
typeToText d = atTopLevel do
  ui <- usedInstances (I.unEl (defType d))
  () <- liftIO $ evaluate (rnf ui)

  fv <- getDefFreeVars (defName d)
  ty <- locallyReduceDefs (OnlyReduceDefs ui) $ {-# SCC "typeToText/normalise" #-} normalise (defType d)

  topm <- topLevelModuleName (qnameModule (defName d))

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

  {-# SCC "typeToText/render" #-} do
  here <- currentTopLevelModule
  tooltip <- renderToHtml <$> P.vcat
    [ annotate a <$> P.pretty (qnameName (defName d))
    , P.nest 2 (P.colon P.<+> prettyATop expr)
    ]
  plain <- Text.pack . render <$> prettyATop expr
  pure (tooltip, plain)

toDefinitionSite :: TopLevelModuleName -> Range -> Maybe Asp.DefinitionSite
toDefinitionSite topm r = do
  p <- fmap (fromIntegral . posPos) . rStart $ r
  pure $ Asp.DefinitionSite
    { Asp.defSiteModule = topm
    , Asp.defSitePos    = fromIntegral p
    , Asp.defSiteHere   = True
    , Asp.defSiteAnchor = Nothing
    }

removeImpls :: A.Expr -> A.Expr
removeImpls (A.Pi _ (x :| xs) e) =
  let
    fixup :: TypedBinding -> TypedBinding
    fixup q@(TBind rng inf as _)
      | Hidden <- getHiding q = TBind rng inf as underscore
      | otherwise = q
  in makePi (map (A.mapExpr removeImpls . fixup) (x:xs)) (removeImpls e)
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
