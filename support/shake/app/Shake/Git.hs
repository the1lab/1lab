{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

module Shake.Git
  ( gitCommit
  , gitAuthors
  , gitRules
  ) where

import qualified Data.Text.Encoding as Text
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Generics

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

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

  -- Sort authors list and make it unique.
  Stdout authors <- command [] "git" ["log", "--format=%aN", "--", path]
  let authorSet = Set.fromList . Text.lines . Text.decodeUtf8 $ authors

  Stdout coauthors <-
    command [] "git" ["log", "--format=%(trailers:key=Co-authored-by,valueonly)", "--", path]

  let
    coauthorSet = Set.fromList
      . map dropEmail
      . filter (not . Text.null . Text.strip)
      . Text.lines
      . Text.decodeUtf8 $ coauthors

    dropEmail = Text.unwords . init . Text.words

  pure . Set.toList $ authorSet <> coauthorSet

-- | Shake rules required for reading Git information.
gitRules :: Rules()
gitRules = versioned 1 do
  _ <- addOracle \(GitCommit ()) -> do
    Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"]
    pure (head (lines t))

  _ <- addOracleCache doGitAuthors

  pure ()
