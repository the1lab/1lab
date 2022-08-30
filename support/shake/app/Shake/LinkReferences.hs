{-# LANGUAGE OverloadedStrings #-}
-- | Link Agda identifiers in inline code blocks.
module Shake.LinkReferences (linkReferences) where

import qualified Data.HashMap.Strict as HashMap
import Data.HashMap.Strict (HashMap)
import qualified Data.Text as T
import Data.Text (Text)

import Text.Pandoc.Definition
import Text.HTML.TagSoup
import Text.Pandoc.Walk

linkReferences :: Pandoc -> Pandoc
linkReferences (Pandoc meta blocks) =
  let hm = parseSymbolRefs blocks
   in Pandoc meta (walk (link hm) blocks)

link :: HashMap Text Reference -> Inline -> Inline
link hm inline@(Code (_, classes, kv) text)
  | isToBeLinked =
    case HashMap.lookup identifier hm of
      Just ref -> renderReference ref text
      Nothing -> inline
  where
    classes' = map T.toLower classes

    isToBeLinked = ("agda" `elem` classes')
                && ("nolink" `notElem` classes')

    identifier =
      case lookup "ident" kv of
        Just id -> id
        _ -> text
link _ x = x

renderReference :: Reference -> Text -> Inline
renderReference (Reference href cls) t =
  Span ("", ["Agda"], []) [Link ("", [cls], []) [Str t] (href, "")]

data Reference =
  Reference { refHref  :: Text
            , refClass :: Text
            }
  deriving (Eq, Show)

-- | Find all links in Agda code blocks (represented as HTML not
-- markdown) and build a map of ident -> reference.
parseSymbolRefs :: [Block] -> HashMap Text Reference
parseSymbolRefs = go mempty . concatMap getHTML where
  getHTML :: Block -> [Tag Text]
  getHTML (RawBlock "html" xs) = parseTags xs >>= parseTags'
  getHTML (BlockQuote bs) = bs >>= getHTML
  getHTML (Div _ bs) = bs >>= getHTML
  getHTML _ = []

  parseTags' (TagComment x) = parseTags x >>= parseTags'
  parseTags' t = pure t

  go :: HashMap Text Reference -> [Tag Text] -> HashMap Text Reference
  go map (TagOpen "a" meta:TagText t:TagClose "a":xs)
    | Just cls <- lookup "class" meta
    , Just href <- lookup "href" meta
    = go (addIfNotPresent t (Reference href cls) map) xs

    | otherwise = go map xs

  go map (_:xs) = go map xs
  go map [] = map

addIfNotPresent :: Text -> v -> HashMap Text v -> HashMap Text v
addIfNotPresent = HashMap.insertWith (\_ old -> old)
