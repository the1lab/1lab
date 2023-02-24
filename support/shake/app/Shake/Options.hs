{-# LANGUAGE BlockArguments, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE DeriveGeneric, TypeFamilies #-}

-- | Global build options.
module Shake.Options
  ( Option(..)
  , setOptions
  , getSkipTypes
  , getSkipAgda
  , getWatching
  ) where

import Development.Shake.Classes
import Development.Shake

import GHC.Generics (Generic)

data Option
  = SkipTypes -- ^ Skip generating types when emitting HTML.
  | SkipAgda -- ^ Skip typechecking Agda, emitting the markdown directly.
  | Watching -- ^ Launch in watch mode. Prevents some build tasks running.
  deriving (Eq, Show, Typeable, Generic)

instance Hashable Option where
instance Binary Option where
instance NFData Option where

type instance RuleResult Option = Bool

-- | Set which option flags are enabled.
setOptions :: [Option] -> Rules ()
setOptions options = do
  _ <- addOracle (pure . getOption)
  pure ()
  where
    getOption SkipTypes = SkipTypes `elem` options
                       || SkipAgda `elem` options
                       || Watching `elem` options
    getOption SkipAgda = SkipAgda `elem` options
    getOption Watching = Watching `elem` options

getSkipTypes, getSkipAgda, getWatching :: Action Bool
getSkipTypes = askOracle SkipTypes
getSkipAgda = askOracle SkipAgda
getWatching = askOracle Watching
