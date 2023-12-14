-- | Rules for working with our Agda modules.

{-# LANGUAGE BlockArguments, TypeFamilies, DeriveGeneric #-}
module Shake.Modules
  ( ModName
  , ModKind(..)
  , moduleRules
  , getOurModules
  , getAllModules
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Development.Shake.Classes
import Development.Shake.FilePath
import Development.Shake

import GHC.Generics (Generic)

import HTML.Backend (moduleName)

import Shake.Git
import Shake.Options

type ModName = String

data ModulesQ = ModulesQ
  deriving (Eq, Show, Typeable, Generic)

instance Hashable ModulesQ where
instance Binary ModulesQ where
instance NFData ModulesQ where

-- | The kind of a module.
data ModKind
  = WithText
  | CodeOnly
  deriving (Eq, Ord, Show, Typeable, Generic)

instance Hashable ModKind where
instance Binary ModKind where
instance NFData ModKind where

newtype ModulesA = ModulesA { unModulesA :: Map ModName ModKind }
  deriving (Eq, Ord, Show, Typeable, Generic)

instance Hashable ModulesA where
  hashWithSalt salt (ModulesA mod) = hashWithSalt salt (Map.toAscList mod)

instance Binary ModulesA where
instance NFData ModulesA where

type instance RuleResult ModulesQ = ModulesA

-- | Define oracles to get the modules used within 1Lab.
moduleRules :: Rules ()
moduleRules = do
  _ <- addOracle \ModulesQ -> do
    gitOnly <- getGitOnly

    let
      isAgda x = any (?== x) ["src//*.agda", "src//*.lagda.md"]
      getFiles = if gitOnly
        then map dropDirectory1 . filter isAgda <$> gitFiles
        else getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]

      toOut x | takeExtensions x == ".lagda.md"
              = (moduleName (dropExtensions x), WithText)
      toOut x = (moduleName (dropExtensions x), CodeOnly)

    ModulesA . Map.fromList . map toOut <$> getFiles
  pure ()

-- | Get all 1Lab modules.
getOurModules :: Action (Map ModName ModKind)
getOurModules = unModulesA <$> askOracle ModulesQ

-- | Get all Agda modules used within the project.
getAllModules :: Action (Map ModName ModKind)
getAllModules = do
  our <- getOurModules
  pure $ Map.singleton "all-pages" CodeOnly
      <> our
