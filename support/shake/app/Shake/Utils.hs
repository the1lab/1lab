{-# LANGUAGE CPP #-}
module Shake.Utils
  ( nodeCommand
  , nodeProc
  , readJSONFile
  ) where

import Data.Aeson

import System.Process (CreateProcess)
import System.Process qualified as Process
import System.IO

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
-- See 'nodeCommand' for more information on the resolution
-- of node-related paths.
nodeProc
  :: FilePath
  -- ^ Path to the node script.
  -> [String]
  -- ^ Arguments to pass to the node script.
  -> CreateProcess
nodeProc path opts =
  let nodeLibPath =
#ifdef NODE_LIB_PATH
        NODE_LIB_PATH
#else
        "node_modules/"
#endif
  in
  (Process.proc "node" (path:opts))
  { Process.env = Just [("NODE_PATH", nodeLibPath)]
  }

-- | Read and decode JSON from a file, tracking it as a dependency.
readJSONFile :: FromJSON b => FilePath -> Action b
readJSONFile path = need [path] >> liftIO (eitherDecodeFileStrict' path) >>= either fail pure
