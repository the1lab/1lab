module Shake.Utils
  ( gitCommand
  , nodeCommand
  ) where

import Development.Shake

-- | Invoke a command either from `PATH` or from `node_modules/.bin`
nodeCommand :: CmdResult r => [CmdOption] -> String -> [String] -> Action r
nodeCommand opts = command (opts ++ [AddPath [] ["node_modules/.bin"]])

-- | Set `--git-dir` explicitly to turn off repository discovery and work
-- around https://github.blog/2022-04-12-git-security-vulnerability-announced/
gitCommand :: CmdResult r => [String] -> Action r
gitCommand args = command [] "git" (["--git-dir", ".git"] ++ args)
