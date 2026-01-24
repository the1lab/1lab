{-# LANGUAGE BlockArguments, ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Shake.AgdaCompile (agdaRules) where

import System.FilePath

import Control.Monad.Except
import Control.Monad

import qualified Data.IntMap.Strict as IntMap
import qualified Data.List.NonEmpty as List1
import qualified Agda.Utils.BiMap as BiMap
import qualified Data.Binary as Binary
import qualified Data.Aeson as Aeson
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Foldable
import Data.Functor
import Data.Maybe (fromMaybe)
import Data.IORef

import Development.Shake.Classes
import Development.Shake

import Shake.Options (getSkipTypes, getWatching, getBaseUrl, getSkipAgda)

import Agda.Compiler.Backend hiding (getEnv)
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.Errors
import Agda.Interaction.Imports hiding (getInterface)
import Agda.Interaction.Options
import Agda.Syntax.Common (Cubical(CFull))
import Agda.Syntax.Common.Pretty
import Agda.Syntax.TopLevelModuleName
  ( TopLevelModuleName'(..)
  , RawTopLevelModuleName(..)
  , hashRawTopLevelModuleName
  )
import Agda.Syntax.Position (noRange)
import Agda.Utils.FileName
import Agda.Utils.Hash (Hash)
import Agda.Utils.Lens ((^.))

import HTML.Backend
import HTML.Render
import HTML.Base

import Shake.Modules

------------------------------------------------------------------------
-- Oracles
------------------------------------------------------------------------

-- | A non-serialisable compile "answer".
data CompileA = CompileA
  { _cState  :: TCState
  , cHash   :: Hash
  }
  deriving Typeable

instance Show CompileA where
  show CompileA{} = "CompileA"

instance Eq CompileA where
  a == b = cHash a == cHash b

instance Hashable CompileA where
  hashWithSalt salt x = hashWithSalt salt (cHash x)

instance Binary CompileA where
  put _ = error "Cannot encode CompileA"
  get = fail "Cannot decode CompileA"

instance NFData CompileA where
  rnf x = cHash x `seq` ()

newtype MainCompileQ = MainCompileQ ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult MainCompileQ = CompileA

newtype ModuleCompileQ = ModuleCompileQ T.Text
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult ModuleCompileQ = CompileA

------------------------------------------------------------------------
-- Rules and actual compilation
------------------------------------------------------------------------

agdaRules :: Rules ()
agdaRules = do
  -- Add an oracle to compile Agda
  ref <- liftIO $ newIORef Nothing
  _ <- addOracleHash \(MainCompileQ ()) -> do
    sa <- getSkipAgda
    when sa $ error $ "--skip-agda build depended on MainCompileQ"
    compileAgda ref

  -- Add a 'projection' oracle which compiles Agda and then uses the per-module
  -- hash instead. This ensures we only rebuild HTML/types when the module
  -- changes.
  _ <- addOracleHash \(ModuleCompileQ m) -> do
    (CompileA state _) <- askOracle (MainCompileQ ())

    let hash = iFullHash . getInterface state $ toTopLevel state m
    pure (CompileA state hash)

  "_build/html0/*.bin" %> \file -> do
    let modName = T.pack . dropExtension $ takeFileName file
    compileResult <- askOracle (ModuleCompileQ modName)
    emitAgda compileResult modName

  -- Add a couple of forwarding rules for emitting the actual HTML/MD
  "_build/html0/*.html" %> \file -> need [file -<.> "bin"]
  "_build/html0/*.md"   %> \file -> need [file -<.> "bin"]

  let
    decodeModule mn = do
      let it = "_build/html0/" </> mn <.> "bin"
      need [it]
      quietly $ traced "decoding" do
        inp :: Either a HtmlModule <- Binary.decodeFileOrFail it
        out <- either (fail . show) pure inp
        rnf out `seq` pure out

  "_build/html/types/*.json" %> \out -> do
    let mn = dropExtension (takeFileName out)
    mod <- decodeModule mn
    quietly $ traced "encoding json" do
      Aeson.encodeFile ("_build/html/types/" </> mn <.> "json") $ Map.fromDistinctAscList
        [ (k, idTooltip id) | (k, id) <- IntMap.toAscList (htmlModIdentifiers mod) ]

  -- Generating the all-types JSON requires chasing the import tree
  -- reported in the all-pages 'HtmlModule'.
  "_build/all-types.json" %> \file -> do
    mods <- getOurModules
    need [ "_build/html0" </> mod <.> "bin" | mod <- Map.keys mods ]

    mod <- decodeModule "all-pages"

    let
      visit !seen !out (other:mods) | other `Set.member` seen = visit seen out mods
      visit !seen !out (other:mods) = do
        HtmlModule{htmlModIdentifiers = ids, htmlModImports = imps} <- decodeModule other
        let elts = IntMap.elems ids <&> \t -> t{ idTooltip = "" }
        visit
          (Set.insert other seen)
          (foldr Set.insert out elts)
          (mods ++ imps)
      visit !_seen !out [] = pure out

    idents <- Set.toList <$> visit mempty mempty (htmlModImports mod)
    traced "encoding json" $ Aeson.encodeFile file idents

-- | Compile the top-level Agda file.
compileAgda :: IORef (Maybe TCState) -> Action CompileA
compileAgda stateVar = do
  files <- map ("src" </>) <$> getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]
  changed <- needHasChanged $ "_build/all-pages.agda":files

  watching <- getWatching

  traced "agda" do
    baseDir <- absolute "_build"

    -- Reuse the old TC state so we don't reload interfaces each time.
    oldState <- readIORef stateVar

    -- On the initial build, always build everything. Otherwise try to only
    -- rebuild the files which have changed.
    let (target, state) =
          case oldState of
            Nothing ->
              -- HACK: As of https://github.com/agda/agda/pull/7719, Agda has the
              -- Agda data directory baked into the binary. This causes massive headaches
              -- when working with nix, as that path points to the read-only nix store.
              -- Moreover, we don't even *need* anything in the data directory, as
              -- we always use --no-load-primitives.
              --
              -- Unfortunately, initStateIO checks for the existence of the data directory,
              -- even if we will never actually use it. We do have to pass in *something* though,
              -- so we just use the build directory: it's the closest 'AbsolutePath' we have at hand.
              (["_build/all-pages.agda"], initState baseDir)
            Just state | watching -> (changed, state)
                       | otherwise -> (["_build/all-pages.agda"], state)

    ((), state) <- runTCMPrettyErrors initEnv state do
      -- We preserve the old modules and restore them at the end, as otherwise
      -- we forget them, and will fail if we need to rebuild other HTML pages.
      oldVisited <- useTC stVisitedModules

      resetState

      -- Force Cubical even if we've not got a --cubical header.
      stPragmaOptions `modifyTCLens` \ o -> o { _optCubical = Just CFull }
      setCommandLineOptions' baseDir defaultOptions

      for_ target \source -> do
        absPath <- liftIO $ absolute source
        source <- parseSource =<< srcFromPath absPath
        typeCheckMain TypeCheck source

      modifyTCLens stVisitedModules (`Map.union` oldVisited)

    writeIORef stateVar (Just state)

    -- TODO: Catch errors and pretty-print failures

    pure (CompileA state 0)


-- | Emit an Agda file as HTML or Markdown.
emitAgda :: CompileA -> T.Text -> Action ()
emitAgda (CompileA tcState _) modName = do
  basepn <- filePath <$> liftIO (absolute "src/")

  baseUrl   <- getBaseUrl
  skipTypes <- getSkipTypes

  let
    tlModName = toTopLevel tcState modName
    iface = getInterface tcState tlModName
    opts = (defaultHtmlOptions baseUrl) { htmlOptGenTypes = not skipTypes }

  ((), _) <- traced "generating html"
    . runTCM initEnv tcState
    . evalWithScope (iInsideScope iface)
    . locallyTC eActiveBackendName (const $ Just "HTML") $ do
      compileOneModule basepn opts iface

  pure ()

-- | Convert a module name to an internal Agda name.
--
-- This ia a very cut down version of topLevelModuleName. We sacrifice all the
-- extra checking for the benefit of not having to run a TCM monad.
toTopLevel :: TCState -> T.Text -> TopLevelModuleName
toTopLevel tcState name =
  let
    qname = List1.fromList (T.split (== '.') name)
    raw = RawTopLevelModuleName noRange qname False
    hash = BiMap.lookup raw (tcState ^. stTopLevelModuleNames)
    hash' = fromMaybe (hashRawTopLevelModuleName raw) hash
  in
  TopLevelModuleName noRange hash' qname False

getInterface :: TCState -> TopLevelModuleName -> Interface
getInterface tcState name =
  let modules = tcState ^. stVisitedModules in
  case Map.lookup name modules of
    Just iface -> miInterface iface
    Nothing -> error $ "Cannot find interface for module " ++ prettyShow name

runTCMPrettyErrors :: TCEnv -> TCState -> TCM a -> IO (a, TCState)
runTCMPrettyErrors env state tcm = do
  (r, state) <- runTCM env state $ (Just <$> tcm) `catchError` \err -> do
    warnings <- fmap (map show) . prettyTCWarnings' =<< getAllWarningsOfTCErr err
    errors  <- show <$> prettyError err
    let everything = filter (not . null) $ warnings ++ [errors]
    unless (null errors) . liftIO . putStr $ unlines everything
    pure Nothing

  case r of
    Just r -> pure (r, state)
    Nothing -> fail "Agda compilation failed"
