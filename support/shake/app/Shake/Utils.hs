module Shake.Utils
  ( nodeCommand
  ) where

import Development.Shake

-- | Invoke a command either from `PATH` or from `node_modules/.bin`
nodeCommand :: CmdResult r => [CmdOption] -> String -> [String] -> Action r
nodeCommand opts = command (opts ++ [AddPath [] ["node_modules/.bin"]])
