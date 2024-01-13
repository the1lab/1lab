{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | Compute a truncated hash of a file, useful for computing cache-busters
-- (or other unique ids) for a file.
module Shake.Digest (digestRules, getFileDigest) where

import qualified Data.ByteString.Lazy as LazyBS
import Data.Digest.Pure.SHA
import Data.Typeable

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

newtype FileDigest = FileDigest FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult FileDigest = String

-- | Shake rules required for computing file digest.
digestRules :: Rules ()
digestRules = versioned 1 do
  _ <- addOracle \(FileDigest f) -> do
    need [f]
    take 8 . showDigest . sha256 <$> liftIO (LazyBS.readFile f)
  pure ()

-- | Compute a short digest of a file.
getFileDigest :: FilePath -> Action String
getFileDigest = askOracle . FileDigest
