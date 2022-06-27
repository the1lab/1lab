{-# LANGUAGE BlockArguments, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies #-}
module Shake.AgdaCompile (agdaRules) where

import qualified System.Directory as Dir
import System.FilePath

import qualified Data.List.NonEmpty as List1
import qualified Data.HashMap.Strict as Hm
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Aeson (eitherDecodeFileStrict', encodeFile)
import Data.Maybe

import Development.Shake.Classes
import Development.Shake

import Agda.Compiler.Backend hiding (getEnv)
import Agda.Compiler.Common
import Agda.Interaction.FindFile (SourceFile(..))
import Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.Syntax.Common (Cubical(CFull))
import Agda.Syntax.Concrete.Name (TopLevelModuleName(..))
import Agda.Syntax.Position (noRange)
import Agda.Utils.FileName
import Agda.Utils.Hash (Hash)
import Agda.Utils.Pretty
import Agda.Utils.Lens ((^.))

import HTML.Backend
import HTML.Base

------------------------------------------------------------------------
-- Oracles
------------------------------------------------------------------------

-- | A non-serialisable compile "answer".
data CompileA = CompileA
  { _cState  :: TCState
  , _cResult :: CheckResult
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

newtype ModuleCompileQ = ModuleCompileQ String
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult ModuleCompileQ = CompileA

------------------------------------------------------------------------
-- Rules and actual compilation
------------------------------------------------------------------------

agdaRules :: Rules ()
agdaRules = do
  -- Add an oracle to compile Agda
  _ <- addOracleHash \(MainCompileQ ()) -> compileAgda

  -- Add a 'projection' oracle which compiles Agda and then uses the per-module
  -- hash instead. This ensures we only rebuild HTML/types when the module
  -- changes.
  _ <- addOracleHash \(ModuleCompileQ m) -> do
    (CompileA state result _) <- askOracle (MainCompileQ ())

    let hash = iFullHash . getInterface state $ toTopLevel m
    pure (CompileA state result hash)

  -- Create a cache for the per-module type information.
  getTypes <- newCache \modName -> do
    let path = "_build/html0" </> modName <.> ".json"
    need [path]

    result :: Either String (Hm.HashMap T.Text Identifier) <-
      quietly . traced "read types" $ eitherDecodeFileStrict' path
    either fail pure result

  -- In order to write the JSON, we first compile the required module (which
  -- gives us the TC environment) and then emit the HTML/Markdown and type JSON.
  "_build/html0/*.json" %> \file -> do
    let modName = dropExtension (takeFileName file)
    compileResult <- askOracle (ModuleCompileQ modName)
    emitAgda compileResult getTypes modName

  -- Add a couple of forwarding rules for emitting the actual HTML/MD
  "_build/html0/*.html" %> \file -> need [file -<.> "json"]
  "_build/html0/*.md" %> \file -> need [file -<.> "json"]

  -- We generate the all-types JSON from the all-pages types JSON - it's just a
  -- schema change.
  "_build/all-types.json" %> \file -> do
    types <- getTypes "all-pages"
    liftIO $ encodeFile file (Hm.elems types)

-- | Compile the top-level Agda file.
compileAgda :: Action CompileA
compileAgda = do
  files <- map ("src" </>) <$> getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]
  need $ "_build/all-pages.agda":files

  traced "agda" do
    baseDir <- absolute "_build"
    absPath <- absolute "_build/all-pages.agda"

    (result, state) <- runTCM initEnv initState do
      -- Force Cubical even if we've not got a --cubical header.
      stPragmaOptions `modifyTCLens` \ o -> o { optCubical = Just CFull }
      setCommandLineOptions' baseDir defaultOptions

      source <- parseSource (SourceFile absPath)
      typeCheckMain TypeCheck source

    -- TODO: Catch errors and pretty-print failures

    let hash = iFullHash . miInterface . crModuleInfo $ result
    pure (CompileA state result hash)


-- | Emit an Agda file as HTML or Markdown.
emitAgda
  :: CompileA
  -> (String -> Action (Hm.HashMap T.Text Identifier))
  -> String -> Action ()
emitAgda (CompileA tcState checkResult _) getTypes modName = do
  liftIO $ Dir.createDirectoryIfMissing True "_build/html0"

  basepn <- filePath <$> liftIO (absolute "src/")

  let tlModName = toTopLevel modName
      iface = getInterface tcState tlModName

  types <- parallel . map (getTypes . render . pretty . toTopLevelModuleName . fst) $ iImportedModules iface

  skipTypes <- fmap isJust . getEnv $ "SKIP_TYPES"
  ((), _) <- quietly . traced "agda html"
    . runTCM initEnv tcState
    . inCompilerEnv checkResult
    . locallyTC eActiveBackendName (const $ Just "HTML") $ do
      compileOneModule basepn defaultHtmlOptions { htmlOptGenTypes = not skipTypes }
        (mconcat types)
        iface

  pure ()

toTopLevel :: String -> TopLevelModuleName
toTopLevel = TopLevelModuleName noRange . List1.fromList . split where
  split "" = []
  split ('.':xs) = split xs
  split xs =
    let (here, there) = span (/= '.') xs in
    here:split there

getInterface :: TCState -> TopLevelModuleName -> Interface
getInterface tcState name = miInterface . fromJust . Map.lookup name $ tcState ^. stVisitedModules
