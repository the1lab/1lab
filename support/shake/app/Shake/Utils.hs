module Shake.Utils
  ( nodeCommand
  , readJSONFile
  ) where

import Data.Aeson

import Development.Shake

-- | Invoke a command either from `PATH` or from `node_modules/.bin`
nodeCommand :: CmdResult r => [CmdOption] -> String -> [String] -> Action r
nodeCommand opts = command (opts ++ [AddPath [] ["node_modules/.bin"]])

-- | Read and decode JSON from a file, tracking it as a dependency.
readJSONFile :: FromJSON b => FilePath -> Action b
readJSONFile path = need [path] >> liftIO (eitherDecodeFileStrict' path) >>= either fail pure
