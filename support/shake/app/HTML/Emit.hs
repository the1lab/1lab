{-# LANGUAGE OverloadedStrings #-}
module HTML.Emit
  ( renderHTML5
  , overHTML
  ) where

import Data.Text (Text)
import Text.HTML.TagSoup

-- | Write a HTML file, correctly handling the closing of some tags.
renderHTML5 :: [Tag Text] -> Text
renderHTML5 = renderTagsOptions renderOptions{ optMinimize = min } where
  min = flip elem ["br", "meta", "link", "img", "hr"]

overHTML :: ([Tag Text] -> [Tag Text]) -> Text -> Text
overHTML f = renderHTML5 . f . parseTags
