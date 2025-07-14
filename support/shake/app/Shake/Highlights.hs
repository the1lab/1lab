{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Shake.Highlights (renderHighlights) where

import Control.Monad.Trans

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Traversable
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import Data.Maybe
import Data.Char

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup

import Development.Shake.FilePath
import Development.Shake

import Definitions

import Debug.Trace

-- | Make some 'Text' title-cased.
titleCase :: Text -> Text
titleCase txt =
  case Text.uncons txt of
    Just (c, cs) -> Text.cons (toUpper c) cs
    Nothing -> ""

-- | Construct a title for a highlighting block.
-- The rules for titles are:
-- 1. If the highlighting icon has an @aria-label@, then we use that as the root of the label.
-- 2. If there is no @aria-label@, then we title-case the highlighting class name.
-- 3. If the highlighting block has an @id@ attribute, then title case it, and concatenate it on.
--    This is used to display the definition name in @definition@ blocks.
highlightText
  :: Text
  -- ^ Highlighting class of the block.
  -> [TagTree Text]
  -- ^ The highlight SVG for the block.
  -> [Attribute Text]
  -- ^ Highlight block attributes.
  -> Text
highlightText clz svg attr =
  fromMaybe (titleCase clz) ariaLabel <>
  maybe "" (": " <>) (lookup "id" attr)
  where
    ariaLabel :: Maybe Text
    ariaLabel =
      case svg of
        (TagBranch _ svgAttr _:_) -> lookup "aria-label" svgAttr
        _ -> Nothing

-- | Expands away @<div class="warning">@ and @<details warning>@. Any
-- icon under @support/web/highlights@ is supported; the @definition@
-- icon will additionally include the principal label being defined (the
-- id of the element) in the text.
renderHighlights :: FilePath -> [Tag Text] -> Action [Tag Text]
renderHighlights input stream = do
  let tree = tagTree stream

  icons <- fmap (Text.pack . map toLower . dropExtension)
    <$> getDirectoryFiles "support/web/highlights" ["*.svg"]

  let
    isIcon t
      | Text.toLower t `elem` icons = pure t
      | otherwise                   = Nothing

    isHighlight (xs, "") = isIcon xs
    isHighlight _ = Nothing

    titleCase (Text.uncons -> Just (c, cs)) = Text.cons (toUpper c) cs
    titleCase _ = ""

    readIcon icn =
      parseTree . Text.pack <$> readFile' ("support/web/highlights" </> Text.unpack icn -<.> "svg")

    highlightSpan icn attr = do
      svg <- readIcon icn
      let text = TagText (highlightText icn svg attr)
      pure $ TagBranch "span" [("class", "highlight-header")]
        [ TagBranch "span" [("class", "highlight-icon")] svg
        , TagBranch "span" [("class", "highlight-text")] [TagLeaf text]
        ]

    go :: TagTree Text -> Action (TagTree Text)
    go (TagBranch "div" attr children)
      | Just clz <- lookup "class" attr,
        let clzs = Text.words clz,
        [icn] <- mapMaybe isIcon clzs
      = do
      icon <- highlightSpan icn attr
      children <- traverse go children
      pure $ TagBranch "div" (("class", "highlighted " <> clz):attr) $ icon:children

    go t@(TagBranch "details" attr children)
      | Just (sattr, schild, rest) <- summary children
      , [icn] <- mapMaybe isHighlight attr
      = do
      icon <- highlightSpan icn attr
      schild <- traverse go schild
      rest <- traverse go rest
      pure $ TagBranch "details" (("class", icn):attr) $
        TagBranch "summary" sattr (icon:schild):rest

    go (TagBranch tag attr children) = TagBranch tag attr <$> traverse go children
    go (TagLeaf t) = pure (TagLeaf t)

    summary :: [TagTree Text] -> Maybe ([(Text, Text)], [TagTree Text], [TagTree Text])
    summary (t@(TagBranch "summary" attr children):ts) = Just (attr, children, ts)
    summary (_:ts) = summary ts
    summary []     = Nothing

  flattenTree <$> traverse go tree
