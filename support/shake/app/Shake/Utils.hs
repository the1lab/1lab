{-# LANGUAGE CPP #-}
module Shake.Utils
  ( nodeCommand
  , nodeProc
  , readJSONFile
  ) where

import Data.Aeson
import Data.List.Split
import Data.Maybe

import System.Process (CreateProcess)
import System.Process qualified as Process

import Development.Shake
import Development.Shake.FilePath

-- | Invoke a Node command.
nodeCommand :: CmdResult r => [CmdOption] -> String -> [String] -> Action r
nodeCommand opts path args = do
  nodePath <- getEnv "NODE_PATH"
  let paths = map (</> ".bin") (fromMaybe [] (splitOn ":" <$> nodePath) ++ ["node_modules"])
  command (opts ++ [AddPath paths []]) path args

-- | Construct a @CreateProcess@ for a node script.
nodeProc
  :: FilePath
  -- ^ Path to the node script.
  -> [String]
  -- ^ Arguments to pass to the node script.
  -> CreateProcess
nodeProc path opts = Process.proc "node" (path:opts)

-- | Read and decode JSON from a file, tracking it as a dependency.
readJSONFile :: FromJSON b => FilePath -> Action b
readJSONFile path = need [path] >> liftIO (eitherDecodeFileStrict' path) >>= either fail pure
