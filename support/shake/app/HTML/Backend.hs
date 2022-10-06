-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.
{-# LANGUAGE FlexibleContexts, ViewPatterns, DeriveDataTypeable, StandaloneDeriving #-}
module HTML.Backend
  ( htmlBackend
  , compileOneModule
  , moduleName
  , defaultHtmlOptions
  ) where

import HTML.Base

import Prelude hiding ((!!), concatMap)
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.HashMap.Strict as Hm
import qualified Data.Text as Text
import Data.HashMap.Strict (HashMap)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Aeson
import Data.IORef
import Data.Maybe
import Data.Data (Data)
import Data.Text (Text)
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.Translation.InternalToAbstract ( Reify(reify) )
import Agda.Syntax.Internal (Type, Dom, domName)
import Agda.TypeChecking.Reduce (instantiateFull)
import qualified Agda.Syntax.Internal.Generic as I
import qualified Agda.Utils.Maybe.Strict as S
import qualified Agda.Syntax.Concrete as Con
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Views
import Agda.Compiler.Backend
import Agda.Syntax.Abstract hiding (Type)
import Agda.Compiler.Common
import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Syntax.Common
import Agda.Utils.Pretty
import Agda.Syntax.Info

import System.FilePath

data HtmlCompileEnv = HtmlCompileEnv
  { htmlCompileEnvOpts     :: HtmlOptions
  , htmlCompileTypes       :: IORef (HashMap Text Identifier)
    -- ^ Hashmap from anchor→identifier for finding types while emitting
    -- HTML, and for search after
  , htmlCompileBasePath    :: FilePath
  }

data HtmlModuleEnv = HtmlModuleEnv
  { htmlModEnvCompileEnv :: HtmlCompileEnv
  , htmlModEnvName       :: ModuleName
  }

newtype HtmlModule = HtmlModule { getHtmlModule :: HashMap Text Identifier }

htmlBackend :: FilePath -> HtmlOptions -> Backend
htmlBackend = (Backend .) . htmlBackend'

htmlBackend'
  :: FilePath
  -> HtmlOptions
  -> Backend'
      (FilePath, HtmlOptions)
      HtmlCompileEnv
      HtmlModuleEnv
      HtmlModule
      (Maybe (Text, Identifier))
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
  types <- liftIO (newIORef mempty)
  runLogHtmlWithMonadDebug $ pure $ HtmlCompileEnv opts types pn

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
          pure $ Skip (HtmlModule mempty)
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
  -> TCM (Maybe (Text, Identifier))
compileDefHtml env _ _ _
  | not (htmlOptGenTypes (htmlCompileEnvOpts env)) = pure Nothing
compileDefHtml env _menv _isMain def = do
  case definitionAnchor env def of
    Just mn -> do
      ty <- typeToText def
      let
        ident = Identifier
          { idAnchor = mn
          , idIdent = Text.pack (render (pretty (qnameName (defName def))))
          , idType = Text.pack ty
          }
      pure (Just (mn, ident))
    Nothing -> do
      pure Nothing

postModuleHtml
  :: (MonadIO m, MonadDebug m, ReadTCState m)
  => HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> ModuleName
  -> [Maybe (Text, Identifier)]
  -> m HtmlModule
postModuleHtml env menv _isMain _modName _defs = do
  let
    ins Nothing       = id
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
  pure $ HtmlModule $ foldr ins mempty _defs

postCompileHtml
  :: MonadIO m
  => HtmlCompileEnv
  -> IsMain
  -> Map ModuleName HtmlModule
  -> m ()
postCompileHtml cenv _isMain _modulesByName = liftIO $ do
  case htmlOptDumpIdents (htmlCompileEnvOpts cenv) of
    Just fp -> encodeFile fp (Map.elems _modulesByName >>= Hm.elems . getHtmlModule)
    Nothing -> pure ()

-- | Compile a single module, given an existing set of types.
compileOneModule
  :: FilePath -> HtmlOptions
  -> HashMap Text Identifier -- ^ Existing map of identifiers to their types.
  -> Interface -- ^ The interface to compile.
  -> TCM ()
compileOneModule pn opts types iface = do
  types <- liftIO (newIORef types)
  let cEnv = HtmlCompileEnv opts types pn
      mEnv = HtmlModuleEnv cEnv (iModuleName iface)

  setInterface iface

  defs <- map snd . sortDefs <$> curDefs
  res  <- mapM (compDef cEnv mEnv <=< instantiateFull) defs
  _ <- postModuleHtml cEnv mEnv NotMain (iModuleName iface) res
  pure ()

  where
    compDef env menv def = setCurrentRange (defName def) $
      compileDefHtml env menv NotMain def


prettifyTerm :: Type -> Type
prettifyTerm = runIdentity . I.traverseTermM unDomName where
  unDomName :: I.Term -> Identity I.Term
  unDomName (I.Pi d x) = pure $ I.Pi d{domName = Nothing} x
  unDomName (I.Def q x) = pure $ I.Def q{qnameModule = MName []} x
  unDomName x = pure x

-- killQual :: Con.Expr -> Con.Expr
-- killQual = everywhere (mkT unQual) where
--   unQual :: Con.QName -> Con.QName
--   unQual (Con.Qual _ x) = unQual x
--   unQual x = x

typeToText :: Definition -> TCM String
typeToText d = do
  expr <- reify . prettifyTerm $ defType d
  fmap (render . pretty) .
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
      S.Just (filePath -> f) -> do
        let f' = moduleName $ dropExtensions (makeRelative basepn f)
        pure (f' <.> "html")
      S.Nothing -> Nothing
  f modn =
    case rStart (nameBindingSite (qnameName (defName def))) of
      Just pn -> pure $ Text.pack (modn <> "#" <> show (posPos pn))
      Nothing -> Nothing

-- | Determine the name of a module from a file like @1Lab/HIT/Torus@.
moduleName :: FilePath -> String
moduleName = intercalate "." . splitDirectories
