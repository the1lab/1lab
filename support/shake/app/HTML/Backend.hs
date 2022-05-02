-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.
{-# LANGUAGE DeriveGeneric, FlexibleContexts, ViewPatterns #-}
module HTML.Backend
  ( htmlBackend
  , builtinModules
  , moduleName
  , defaultHtmlOptions
  ) where

import HTML.Base

import Prelude hiding ((!!), concatMap)
import Control.Monad.Except

import qualified Data.HashMap.Strict as Hm
import qualified Data.Text as Text
import Data.HashMap.Strict (HashMap)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.IORef
import Data.Maybe
import Data.Text (Text)
import Data.List
import Data.Map (Map)

import Data.Generics (everywhere, mkT)

import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.Translation.InternalToAbstract ( Reify(reify) )
import Agda.Syntax.Internal (Type, Dom, domName)
import qualified Agda.Utils.Maybe.Strict as S
import qualified Agda.Syntax.Concrete as Con
import Agda.Syntax.Abstract.Views
import Agda.Compiler.Backend
import Agda.Syntax.Abstract
import Agda.Compiler.Common
import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Syntax.Common
import Agda.Utils.Pretty
import Agda.Syntax.Info

import System.FilePath
import System.IO

data HtmlCompileEnv = HtmlCompileEnv
  { htmlCompileEnvOpts  :: HtmlOptions
  , htmlCompileTypes    :: IORef (HashMap Text String)
  , htmlCompileBasePath :: FilePath
  }

data HtmlModuleEnv = HtmlModuleEnv
  { htmlModEnvCompileEnv :: HtmlCompileEnv
  , htmlModEnvName       :: ModuleName
  }

data HtmlModule = HtmlModule

htmlBackend :: FilePath -> HtmlOptions -> Backend
htmlBackend = (Backend .) . htmlBackend'

htmlBackend'
  :: FilePath
  -> HtmlOptions
  -> Backend' (FilePath, HtmlOptions) HtmlCompileEnv HtmlModuleEnv HtmlModule
      (Maybe (Text, String))
htmlBackend' basepn opts = Backend'
  { backendName = "HTML"
  , backendVersion = Nothing
  , options = (basepn, opts)
  , commandLineFlags = []
  , isEnabled = const True
  , preCompile = preCompileHtml
  , preModule = preModuleHtml
  , compileDef = compileDefHtml
  , postModule = postModuleHtml
  , postCompile = postCompileHtml
  , scopeCheckingSuffices = False
  , mayEraseType = const $ return False
  }

runLogHtmlWithMonadDebug :: MonadDebug m => LogHtmlT m a -> m a
runLogHtmlWithMonadDebug = runLogHtmlWith $ reportS "html" 1

preCompileHtml
  :: (MonadIO m, MonadDebug m)
  => (FilePath, HtmlOptions)
  -> m HtmlCompileEnv
preCompileHtml (pn, opts) = do
  ref <- liftIO (newIORef mempty)
  runLogHtmlWithMonadDebug $ pure $ HtmlCompileEnv opts ref pn

preModuleHtml
  :: (MonadIO m, ReadTCState m)
  => HtmlCompileEnv
  -> IsMain
  -> ModuleName
  -> Maybe FilePath
  -> m (Recompile HtmlModuleEnv HtmlModule)
preModuleHtml cenv _isMain modName _ifacePath
  | htmlOptGenTypes (htmlCompileEnvOpts cenv) = do
    liftIO . putStrLn $ "Entering module " <> render (pretty modName)
    pure $ Recompile (HtmlModuleEnv cenv modName)
-- When types are being skipped we can safely only re-render modules
-- whose interface file have changed:
preModuleHtml cenv _ modName mifile =
  do
    ft <- iFileType <$> curIF
    let
      topl = toTopLevelModuleName modName
      ext = highlightedFileExt (htmlOptHighlight (htmlCompileEnvOpts cenv)) ft
      path = htmlOptDir (htmlCompileEnvOpts cenv) </> modToFile topl ext

    liftIO $ do
      uptd <- uptodate path
      if uptd
        then do
          putStrLn $ "HTML for module " <> render (pretty modName) <> " is up-to-date"
          pure $ Skip HtmlModule
        else pure $ Recompile (HtmlModuleEnv cenv modName)

  where
    uptodate of_ = case mifile of
      Nothing -> pure False
      Just ifile -> isNewerThan of_ ifile

compileDefHtml
  :: HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> Definition
  -> TCM (Maybe (Text, String))
compileDefHtml env _ _ _
  | not (htmlOptGenTypes (htmlCompileEnvOpts env)) = pure Nothing
compileDefHtml env _menv _isMain def = do
  liftIO $ do
     putStr $ "\027[2K\rRendering type for " ++ render (pretty (defName def))
     hFlush stdout
  case definitionAnchor env def of
    Just mn -> do
      ty <- typeToText def
      pure (Just (mn, ty))
    Nothing -> pure Nothing

postModuleHtml
  :: (MonadIO m, MonadDebug m, ReadTCState m)
  => HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> ModuleName
  -> [Maybe (Text, String)]
  -> m HtmlModule
postModuleHtml env menv _isMain _modName _defs = do
  liftIO $ putStrLn ""
  let
    ins Nothing = id
    ins (Just (a, b)) = Hm.insert a b

  types <- liftIO $ atomicModifyIORef' (htmlCompileTypes env) $
    \mp -> let mp' = foldr ins mp _defs in (mp', mp')

  let
    generatePage =
        defaultPageGen types
      . htmlCompileEnvOpts
      . htmlModEnvCompileEnv
      $ menv
  htmlSrc <- srcFileOfInterface (toTopLevelModuleName . htmlModEnvName $ menv) <$> curIF
  runLogHtmlWithMonadDebug $ generatePage htmlSrc
  return HtmlModule

postCompileHtml
  :: Applicative m
  => HtmlCompileEnv
  -> IsMain
  -> Map ModuleName HtmlModule
  -> m ()
postCompileHtml _cenv _isMain _modulesByName = pure ()

killDomainNames :: Type -> Type
killDomainNames = everywhere (mkT unDomName) where
  unDomName :: Dom Type -> Dom Type
  unDomName m = m{ domName = Nothing }

killQual :: Con.Expr -> Con.Expr
killQual = everywhere (mkT unQual) where
  unQual :: Con.QName -> Con.QName
  unQual (Con.Qual _ x) = unQual x
  unQual x = x

typeToText :: Definition -> TCM String
typeToText d = do
  expr <- reify . killDomainNames $ defType d
  fmap (render . pretty . killQual) .
    abstractToConcrete_ . removeImpls $ expr

removeImpls :: Expr -> Expr
removeImpls (Pi _ (x :| xs) e) =
  makePi (map (mapExpr removeImpls) $ filter ((/= Hidden) . getHiding) (x:xs)) (removeImpls e)
removeImpls (Fun span arg ret) =
  Fun span (removeImpls <$> arg) (removeImpls ret)
removeImpls e = e

makePi :: [TypedBinding] -> Expr -> Expr
makePi [] = id
makePi (b:bs) = Pi exprNoRange (b :| bs)

definitionAnchor :: HtmlCompileEnv -> Definition -> Maybe Text
definitionAnchor _ def | defCopy def = Nothing
definitionAnchor htmlenv def = f =<< go where
  basepn = htmlCompileBasePath htmlenv
  go :: Maybe FilePath
  go = do
    let name = defName def
    case rangeFile (nameBindingSite (qnameName name)) of
      S.Just (filePath -> f)
        | ("Agda/Builtin" `isInfixOf` f) || ("Agda/Primitive" `isInfixOf` f) ->
          fakePath name
        | otherwise -> do
          let
            f' = moduleName $ dropExtensions (makeRelative basepn f)
            modMatches = f' `isPrefixOf` render (pretty name)

          unless modMatches Nothing
          pure (f' <.> "html")
      S.Nothing -> Nothing
  f modn =
    case rStart (nameBindingSite (qnameName (defName def))) of
      Just pn -> pure $ Text.pack (modn <> "#" <> show (posPos pn))
      Nothing -> Nothing

fakePath :: QName -> Maybe FilePath
fakePath (QName (MName xs) _) =
  listToMaybe
    [ l <.> "html"
    | l <- map (intercalate ".") (inits (map (render . pretty . nameConcrete) xs))
    , l `elem` builtinModules
    ]

builtinModules :: [String]
builtinModules =
  [ "Agda.Builtin.Bool"
  , "Agda.Builtin.Char"
  , "Agda.Builtin.Cubical.HCompU"
  , "Agda.Builtin.Cubical.Path"
  , "Agda.Builtin.Cubical.Sub"
  , "Agda.Builtin.Float"
  , "Agda.Builtin.FromNat"
  , "Agda.Builtin.FromNeg"
  , "Agda.Builtin.Int"
  , "Agda.Builtin.List"
  , "Agda.Builtin.Maybe"
  , "Agda.Builtin.Nat"
  , "Agda.Builtin.Reflection"
  , "Agda.Builtin.Sigma"
  , "Agda.Builtin.String"
  , "Agda.Builtin.Unit"
  , "Agda.Builtin.Word"
  , "Agda.Primitive.Cubical"
  , "Agda.Primitive"
  ]

-- | Determine the name of a module from a file like @1Lab/HIT/Torus@.
moduleName :: FilePath -> String
moduleName = intercalate "." . splitDirectories
