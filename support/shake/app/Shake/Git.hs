{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies #-}

module Shake.Git
  ( gitCommit
  , gitAuthors
  , GitAuthors(..)
  ) where

import qualified Data.Text.Encoding as Text
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Generics

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

-- | Get the current git commit.
gitCommit :: () -> Action String
gitCommit () = do
  Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"]
  pure (head (lines t))

newtype GitAuthors = GitAuthors FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult GitAuthors = [Text]

-- | Get the authors for a particular commit.
gitAuthors :: Action String -> GitAuthors -> Action [Text]
gitAuthors commit (GitAuthors path) = do
  _commit <- commit -- We depend on the commit, but don't actually need it.

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
