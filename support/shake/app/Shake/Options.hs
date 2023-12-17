{-# LANGUAGE BlockArguments, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE DeriveGeneric, TypeFamilies, DerivingStrategies #-}

-- | Global build options.
module Shake.Options
  ( Options(..), _1LabOptDescrs
  , defaultOptions
  , setOptions

  , getSkipTypes
  , getSkipAgda
  , getWatching
  , getBaseUrl
  , getGitOnly
  ) where

import Development.Shake.Classes
import Development.Shake

import Data.Maybe

import GHC.Generics (Generic)

import System.Console.GetOpt

data Options = Options
  { _optSkipTypes :: !Bool
    -- ^ Skip generating types when emitting HTML.
  , _optSkipAgda  :: !Bool
    -- ^ Skip typechecking Agda, emitting the markdown directly.
  , _optWatching  :: Maybe (Maybe String)
    -- ^ Launch in watch mode. Prevents some build tasks running.
  , _optBaseUrl   :: String
    -- ^ Base URL for absolute paths
  , _optGitOnly   :: Bool
    -- ^ Whether to only build files tracked by git.
  }
  deriving (Eq, Show, Typeable, Generic)

instance Hashable Options
instance Binary Options
instance NFData Options

defaultOptions :: Options
defaultOptions = Options
  { _optSkipTypes = False
  , _optSkipAgda  = False
  , _optWatching  = Nothing
  , _optBaseUrl   = ""
  , _optGitOnly   = False
  }

data GetOptions = GetOptions deriving (Eq, Show, Typeable, Generic)

instance Hashable GetOptions
instance Binary GetOptions
instance NFData GetOptions

type instance RuleResult GetOptions = Options

-- | Set which option flags are enabled.
setOptions :: Options -> Rules ()
setOptions options = do
  _ <- addOracle $ \GetOptions -> pure options
  pure ()

getSkipTypes, getSkipAgda, getWatching, getGitOnly :: Action Bool
getSkipTypes = _optSkipTypes <$> askOracle GetOptions
getSkipAgda  = _optSkipAgda  <$> askOracle GetOptions
getGitOnly   = _optGitOnly   <$> askOracle GetOptions
getWatching  = isJust . _optWatching <$> askOracle GetOptions

getBaseUrl :: Action String
getBaseUrl = _optBaseUrl <$> askOracle GetOptions

_1LabOptDescrs :: [OptDescr (Options -> Options)]
_1LabOptDescrs =
  [ Option "w" ["watch"] (OptArg (\s r -> r { _optWatching = Just s, _optSkipTypes = True }) "COMMAND")
      "Start 1lab-shake in watch mode. Starts a persistent process which runs a subset of build tasks for \
      \interactive editing. Implies --skip-types.\nOptionally takes a command to run after the build has finished."
  , Option [] ["skip-types"] (NoArg (\r -> r { _optSkipTypes = True }))
      "Skip generating type tooltips when compiling Agda to HTML."
  , Option [] ["skip-agda"] (NoArg (\r -> r { _optSkipAgda = True, _optSkipTypes = True }))
      "Skip typechecking Agda. Markdown files are read from src/ directly."
  , Option "b" ["base-url"] (ReqArg (\s r -> r { _optBaseUrl = s }) "URL")
      "The base URL to use for absolute links. Should include the protocol."
  , Option [] ["git-only"] (NoArg (\r -> r { _optGitOnly = True }))
      "Only build files tracked by git."
  ]
