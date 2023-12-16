{-# LANGUAGE LambdaCase, BlockArguments, OverloadedStrings #-}
module Shake.Markdown.HoTT
  ( hottIndexFilter
  )
  where

import Text.Pandoc.Definition

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Function
import Data.Text (Text)
import Data.List (insertBy, intercalate, intersperse)
import Data.Map (Map)

import Development.Shake

import Control.Lens ( (^.), foldrOf, each )
import Text.Printf

import IdInfo

hottIndexFilter :: Pandoc -> Action Pandoc
hottIndexFilter (Pandoc meta blocks) = do
  iinfo <- allIdInfo

  liftIO $ print iinfo
  let inv = foldrOf identifiers invert mempty iinfo
  liftIO $ print inv

  pure (Pandoc meta (go inv blocks))

data Item = Item
  { itemSeq   :: Int
  , itemKind  :: HoTTBookRefKind
  , itemRef   :: Text
  , itemNames :: [Inline]
  , itemSub   :: Map Int Item
  }
  deriving (Show)

type Sections = Map Text (Map Int Item)

invert :: DefInfo -> Sections -> Sections
invert di it = foldrOf (defiPragmas . each) go it di where
  ins' :: Maybe Int -> Item -> Map Int Item -> Map Int Item
  ins' Nothing i = flip Map.alter (itemSeq i) \case
    Nothing -> Just i
    Just i' -> Just i'{ itemNames = itemNames i' ++ itemNames i, itemSub = itemSub i' <> itemSub i }
  ins' (Just s) i = flip Map.alter (itemSeq i) \case
    Nothing -> Just Item
      { itemSeq   = itemSeq i
      , itemKind  = itemKind i
      , itemRef   = itemRef i
      , itemNames = []
      , itemSub   = Map.singleton s i
      }
    Just i' -> Just i'{ itemSub = ins' Nothing i{itemSeq = s} (itemSub i') }

  ins :: Int -> Int -> Maybe Int -> Item -> Sections -> Sections
  ins c s sub item = flip Map.alter (Text.pack (show c <> "." <> show s)) \case
    Nothing -> Just (ins' sub item mempty)
    Just v' -> Just (ins' sub item v')

  name :: Inline
  name = Span ("", ["Agda"], mempty)
    [ Link ("", ["Function"], [("data-type", di ^. defiType)])
      [Code mempty (di ^. defiName)] (di ^. defiAnchor, di ^. defiName)]

  go (HoTTBookPragma (HoTTBookRef kind chap sect item sub)) =
    ins chap sect sub Item
      { itemSeq   = item
      , itemKind  = kind
      , itemRef   = Text.pack (printf "%d.%.d.%d" chap sect item)
      , itemNames = [name]
      , itemSub   = mempty
      }

isH :: Block -> Bool
isH Header{} = True
isH _ = False

toList :: Map Int Item -> Block
toList = BulletList . map (go True . snd) . Map.toAscList where
  go True (Item _ k r ns m) | Map.null m =
    [Plain ([Str (Text.pack (show k)), Space, Str (r <> ":"), Space] ++ intersperse (Str ", ") ns)]
  go True (Item _ k r ns sub) =
    [ Plain ([Str (Text.pack (show k)), Space, Str (r <> ":"), Space] ++ intersperse (Str ", ") ns)
    , OrderedList (1, LowerRoman, Period) $ map (go False . snd) $ Map.toAscList sub
    ]
  go False (Item _ _ _ ns _) = [Plain (intersperse (Str ", ") ns)]

go :: Sections -> [Block] -> [Block]
go inv (hdr@(Header 3 attr (RawInline _ _:Str k:_)):bs) | Just s <- Map.lookup k inv =
  let
    (these, rest) = break isH bs
  in hdr:these ++ toList s:go inv rest
go inv (b:bs) = b:go inv bs
go inv [] = []
