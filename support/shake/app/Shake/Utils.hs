{-# LANGUAGE CPP #-}
module Shake.Utils
  ( nodeCommand
  , nodeProc
  , readJSONFile
  ) where

import Data.Aeson

import System.Process (CreateProcess)
import System.Process qualified as Process

import Development.Shake

-- | Invoke a Node command. On Nix builds (more generally, if the
-- @NODE_BIN_PATH@ preprocessor macro is set while compiling), this will
-- look for the command in a statically-known path. Otherwise, it'll try
-- from @node_modules/.bin@ or your @PATH@.
nodeCommand :: CmdResult r => [CmdOption] -> String -> [String] -> Action r
#ifdef NODE_BIN_PATH

nodeCommand opts path = command opts ( NODE_BIN_PATH ++ "/" ++ path )

#else

nodeCommand opts = command (opts ++ [AddPath [] ["node_modules/.bin"]])

#endif

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
