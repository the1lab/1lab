{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

-- | Read and write data for site-wide search.
module Shake.SearchData where

import Data.Text (Text)
import Data.Aeson
import GHC.Generics (Generic)

import Development.Shake

-- | Data about a searchable term. This is designed to be compatible with the
-- type information written by our Agda HTML backend.
data SearchTerm = SearchTerm
  { idIdent  :: Text
  , idAnchor :: Text
  , idType   :: Maybe Text
  , idDesc   :: Maybe Text
  }
  deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON)

-- | Read search data from a file.
readSearchData :: FilePath -> Action [SearchTerm]
readSearchData path = need [path] >> liftIO (eitherDecodeFileStrict' path) >>= either fail pure

-- | Write search data to a file.
writeSearchData :: FilePath -> [SearchTerm] -> Action ()
writeSearchData path xs = liftIO $ encodeFile path xs
