{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

module Shake.Git
  ( gitCommit
  , gitAuthors
  , gitRules
  ) where

import qualified Data.Text.Encoding as Text
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Char (isSpace, isDigit)
import Data.Text (Text)
import Data.List (sort)
import Data.Generics

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

-- | Set `--git-dir` explicitly to turn off repository discovery and work
-- around https://github.blog/2022-04-12-git-security-vulnerability-announced/
gitCommand :: CmdResult r => [String] -> Action r
gitCommand args = command [] "git" (["--git-dir", ".git"] ++ args)

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
    -- Exclude commits containing the word NOAUTHOR (for example, trivial
    -- reformattings or treewide changes).
    , "--invert-grep", "--grep=NOAUTHOR"
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
  _ <- addOracle \(GitCommit ()) -> do
    Stdout t <- gitCommand ["rev-parse", "--verify", "HEAD"]
    pure (head (lines t))

  _ <- addOracleCache doGitAuthors

  pure ()
