{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

module Shake.Git
  ( gitFiles
  , gitCommit
  , gitAuthors
  , gitRules
  , gitCommand
  ) where

import qualified Data.Text.Encoding as Text
import qualified Data.Text as Text
import Data.Char (isSpace, isDigit)
import Data.Text (Text)
import Data.List (sort)
import Data.Typeable

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

-- | Set `--git-dir` explicitly to turn off repository discovery and work
-- around https://github.blog/2022-04-12-git-security-vulnerability-announced/
gitCommand :: CmdResult r => [String] -> Action r
gitCommand args = command [NoProcessGroup] "git" (["--git-dir", ".git"] ++ args)

newtype GitFiles = GitFiles ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult GitFiles = [FilePath]

-- | Get the list of files tracked by git.
gitFiles :: Action [FilePath]
gitFiles = askOracle (GitFiles ())

newtype GitCommit = GitCommit ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult GitCommit = String

-- | Get the current git commit.
gitCommit :: Action String
gitCommit = askOracle (GitCommit ())

newtype GitAuthors = GitAuthors FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult GitAuthors = [Text]

-- | Get the authors for a particular commit.
gitAuthors :: FilePath -> Action [Text]
gitAuthors = askOracle . GitAuthors

doGitAuthors :: GitAuthors -> Action [Text]
doGitAuthors (GitAuthors path) = do
  _commit <- gitCommit -- We depend on the commit, but don't actually need it.

  Stdout authors <- gitCommand
    [ "shortlog", "-ns"
    -- Exclude chore commits (for example, trivial reformattings or treewide changes).
    , "--invert-grep", "--grep=^chore:", "--grep=^NOAUTHOR"
    -- Include both authors and coauthors.
    , "--group=author", "--group=trailer:co-authored-by"
    , "HEAD", "--", path
    ]

  pure . sort . map dropCounts . Text.lines . Text.decodeUtf8 $ authors

  where
    --- Given a line of the format "  123   Author", convert it to "Author".
    dropCounts = Text.dropWhile isSpace . Text.dropWhile isDigit . Text.dropWhile isSpace

-- | Shake rules required for reading Git information.
gitRules :: Rules()
gitRules = versioned 1 do
  _ <- addOracle \(GitFiles ()) -> do
    Stdout t <- gitCommand ["ls-files", "--full-name"]
    pure (lines t)

  _ <- addOracle \(GitCommit ()) -> do
    Stdout t <- gitCommand ["rev-parse", "--verify", "HEAD"]
    pure (head (lines t))

  _ <- addOracleCache doGitAuthors

  pure ()
