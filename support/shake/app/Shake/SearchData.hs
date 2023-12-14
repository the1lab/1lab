{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

-- | Read and write data for site-wide search.
module Shake.SearchData where

import Data.Text (Text)
import Data.Aeson
import GHC.Generics (Generic)

-- | Data about a searchable term. This is designed to be compatible with the
-- type information written by our Agda HTML backend.
data SearchTerm = SearchTerm
  { idIdent   :: Text
  , idAnchor  :: Text
  , idType    :: Maybe Text
  , idDefines :: Maybe [Text]
  }
  deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON)
