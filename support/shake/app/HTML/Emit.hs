{-# LANGUAGE OverloadedStrings #-}
module HTML.Emit
  ( renderHTML5
  , overHTML
  , checkMarkup
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Text.HTML.TagSoup

import Development.Shake

-- | Write a HTML file, correctly handling the closing of some tags.
renderHTML5 :: [Tag Text] -> Text
renderHTML5 = renderTagsOptions renderOptions{ optMinimize = min } where
  min = flip elem ["br", "meta", "link", "img", "hr"]

overHTML :: ([Tag Text] -> [Tag Text]) -> Text -> Text
overHTML f = renderHTML5 . f . parseTags

-- | Check HTML markup is well-formed.
checkMarkup :: FilePath -> Tag Text -> Action ()
checkMarkup file (TagText txt)
  |  "<!--" `Text.isInfixOf` txt || "<!–" `Text.isInfixOf` txt
  || "-->" `Text.isInfixOf` txt  || "–>" `Text.isInfixOf` txt
  = fail $ "[WARN] " ++ file ++ " contains misplaced <!-- or -->"
checkMarkup _ _ = pure ()
