{-# LANGUAGE OverloadedStrings #-}
module Shake.Highlights (renderHighlights) where

import qualified Data.Text as Text
import Data.Text (Text)
import Data.Maybe
import Data.Char

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup

import Development.Shake.FilePath
import Development.Shake

-- | Expands away @<div class="warning">@ and @<details warning>@. Any
-- icon under @support/web/highlights@ is supported; the @definition@
-- icon will additionally include the principal label being defined (the
-- id of the element) in the text.
renderHighlights :: [Tag Text] -> Action [Tag Text]
renderHighlights stream = do
  let tree = tagTree stream

  icons <- fmap (Text.pack . map toLower . dropExtension)
    <$> getDirectoryFiles "support/web/highlights" ["*.svg"]

  let
    isIcon t
      | Text.toLower t `elem` icons = pure t
      | otherwise                   = Nothing

    isHighlight (xs, "") = isIcon xs
    isHighlight _ = Nothing

    readIcon icn = do
      tree <- parseTree . Text.pack <$> readFile' ("support/web/highlights" </> Text.unpack icn -<.> "svg")
      case tree of
        (TagBranch _ attr _:_) | Just label <- lookup "aria-label" attr -> pure (tree, label)
        _ -> pure (tree, Text.cons (toUpper (Text.head icn)) (Text.tail icn))
    iconSpan icn = do
      (icon, name') <- readIcon icn
      let name = TagText name'
      pure $ TagBranch "span" [("class", "highlight-icon")]
        (icon ++ [ TagBranch "span" [] [TagLeaf name] ])

    go :: TagTree Text -> Action (TagTree Text)
    go (TagBranch "div" attr children)
      | Just clz <- lookup "class" attr,
        let clzs = Text.words clz,
        [icn] <- mapMaybe isIcon clzs
      = do
      icon <- iconSpan icn
      children <- traverse go children
      pure $ TagBranch "div" (("class", "highlighted " <> clz):attr) $ icon:children

    go (TagBranch "details" attr children)
      | Just (sattr, schild, rest) <- summary children
      , [icn] <- mapMaybe isHighlight attr
      = do
      icon <- iconSpan icn
      schild <- traverse go schild
      rest <- traverse go rest
      pure $ TagBranch "details" (("class", icn):attr) $
        TagBranch "summary" sattr (icon:schild):rest

    go (TagBranch tag attr children) = TagBranch tag attr <$> traverse go children
    go (TagLeaf t) = pure (TagLeaf t)

    summary :: [TagTree Text] -> Maybe ([(Text, Text)], [TagTree Text], [TagTree Text])
    summary (TagBranch "summary" attr children:ts) = Just (attr, children, ts)
    summary (_:ts) = summary ts
    summary []     = Nothing

  flattenTree <$> traverse go tree
