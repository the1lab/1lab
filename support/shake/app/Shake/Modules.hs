-- | Rules for working with our Agda modules.

{-# LANGUAGE BlockArguments #-}
module Shake.Modules
  ( ModName
  , ModKind(..)
  , moduleRules
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Development.Shake.FilePath
import Development.Shake

import HTML.Backend (moduleName, builtinModules)

type ModName = String

-- | The kind of a module.
data ModKind = WithText | CodeOnly deriving (Eq, Ord, Show)

-- | Get all modules used within 1Lab
moduleRules :: Rules
  ( Action (Map ModName ModKind) -- ^ Get all 1Lab modules
  , Action (Map ModName ModKind) -- ^ Get all Agda modules used within the project.
  )
moduleRules = do
  getOurModules <- newCache \() -> do
    let
      toOut x | takeExtensions x == ".lagda.md"
              = (moduleName (dropExtensions x), WithText)
      toOut x = (moduleName (dropExtensions x), CodeOnly)

    Map.fromList . map toOut <$> getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]

  let
    getAllModules :: Action (Map ModName ModKind)
    getAllModules = do
      our <- getOurModules ()
      pure $ Map.singleton "all-pages" CodeOnly
          <> Map.fromList [(x, CodeOnly) | x <- builtinModules]
          <> our

  pure (getOurModules (), getAllModules)
