{-# LANGUAGE LambdaCase, BlockArguments, TemplateHaskell, OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Filter.TagSoup
  ( HtmlFilter
  , deepF, rewriteF, everywhereF
  , el
  , (/>), (&>)
  , parseF

  , classes, attrs, attr, attr_
  , addClass, (!)
  , hasClass, hasAttribute, (?)
  , Attrs, singletonAttrs, _Attrs, _attrs

  , _text, _comment, text', element, children

  , module Filter.TagSoup.TH
  )
  where

import Agda.Utils.Monad

import Control.Monad.IO.Class
import Control.Applicative
import Control.DeepSeq
import Control.Arrow
import Control.Lens hiding (element, children)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import Data.String
import Data.Maybe
import Data.Char
import Data.Set (Set)

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup
import Text.StringLike

import qualified Filter.TagSoup.Attributes as A
import qualified Filter.TagSoup.Elements as H
import Filter.TagSoup.TH hiding (defineElements, defineAttributes)
import Data.Foldable
import Filter

import Debug.Trace
import GHC.Generics (Generic)

data Attrs a = Attrs
  { _attrClasses    :: Set a
  , _attrAttributes :: Map a a
  }
  deriving (Show)

instance Ord a => Semigroup (Attrs a) where
  Attrs x y <> Attrs x' y' = Attrs (x <> x') (y <> y')

instance Ord a => Monoid (Attrs a) where
  mempty = Attrs mempty mempty

makeLenses ''Attrs

normalise :: StringLike a => a -> a
normalise = fromString . map toLower . toString

split :: StringLike a => a -> [a]
split = map (fromString . map toLower) . words . toString

unsplit :: StringLike a => [a] -> a
unsplit = fromString . unwords . map (map toLower . toString)

(~~) :: StringLike a => a -> a -> Bool
x ~~ y = normalise x == normalise y

type HtmlFilter m a = Filter m (TagTree a) (TagTree a)

deepF :: Monad m => Filter m (TagTree a) b -> Filter m (TagTree a) b
deepF m = m <|> (pick (children . each) >>> deepF m)

everywhereF :: Monad m => Filter m (TagTree a) b -> Filter m (TagTree a) b
everywhereF m = m <+> (pick (children . each) >>> everywhereF m)

rewriteF :: forall m a. Monad m => Filter m (TagTree a) (TagTree a) -> Filter m (TagTree a) (TagTree a)
rewriteF m = overF (children . each) (rewriteF m) >>> (m <|> arr id)

el :: (Monad m, StringLike a) => a -> HtmlFilter m a
el x = guardF (pick (_TagBranch . _1) >>> arr (x ~~))

(/>) :: Monad m => Filter m a (TagTree b) -> Filter m (TagTree b) c -> Filter m a c
f /> g = f >>> pick (children . each) >>> g

(&>) :: Monad m => Filter m x (TagTree a) -> HtmlFilter m a -> Filter m x (TagTree a)
f &> g = f >>> overF (children . each) g

_Attrs :: forall a. (StringLike a, Ord a) => Iso' [(a, a)] (Attrs a)
_Attrs = iso fwd bwd where
  fwd :: [(a, a)] -> Attrs a
  fwd xs = Attrs
    { _attrClasses    = foldMap (Set.fromList . split) (lookup "class" xs)
    , _attrAttributes = Map.fromList (map (first normalise) xs)
    }
  bwd :: Attrs a -> [(a, a)]
  bwd (Attrs cls attr) = case Set.toList cls of
    [] -> Map.toList attr
    _ ->
      let
        clz = toList $
          cls <> foldMap (Set.fromList . split) (Map.lookup "class" attr)
      in ("class", unsplit clz):Map.toList (Map.delete "class" attr)

_attrs :: forall a. (Ord a, StringLike a) => Traversal' (TagTree a) (Attrs a)
_attrs = _TagBranch . _2 . _Attrs

classes :: forall a. (Ord a, StringLike a) => Traversal' (TagTree a) (Set a)
classes = _attrs . attrClasses

addClass :: forall a m. (Ord a, StringLike a) => a -> Filter m (TagTree a) (TagTree a)
addClass k =
  let ws = Set.fromList (split k)
   in arr (classes %~ Set.union ws)

hasClass :: forall a m. (Monad m, Ord a, StringLike a) => a -> Filter m (TagTree a) (TagTree a)
hasClass k = filterF (anyOf (classes . folding id) (~~ k))

hasAttribute :: forall a m. (Monad m, Ord a, StringLike a) => a -> a -> Filter m (TagTree a) (TagTree a)
hasAttribute k v = filterF (\x -> v `elem` (x ^.. attr k))

(!) :: forall a m x. (Monad m, Ord a, StringLike a)
    => Filter m x (TagTree a)
    -> Filter m x (Attrs a)
    -> Filter m x (TagTree a)
html ! attr = (html &&& attr) >>> arr (\(a, b) -> a & _TagBranch . _2 . _Attrs <>~ b)

(?) :: forall a m x. (Monad m, Ord a, StringLike a)
    => Filter m x (TagTree a)
    -> Filter m x (Attrs a)
    -> Filter m x (TagTree a)
html ? attr =
      (html &&& attr)
  >>> filterF (\(a,b) -> intersects b (foldOf (_TagBranch . _2 . _Attrs) a))
  >>> arr fst
  where
    intersects :: Attrs a -> Attrs a -> Bool
    intersects (Attrs cls attr) (Attrs cls' attr') =
         Set.isSubsetOf cls cls'
      && Set.isSubsetOf (Map.keysSet attr) (Map.keysSet attr')
      && flip all (Set.toList (Map.keysSet attr)) \key -> fromMaybe False do
          x <- Map.lookup key attr
          y <- Map.lookup key attr'
          pure (x == y)

infixl 7 !
infixl 7 ?

singletonAttrs :: forall a. (Ord a, StringLike a) => a -> a -> Attrs a
singletonAttrs key val = if normalise key == "class"
  then Attrs (Set.fromList (split val)) mempty
  else Attrs mempty (Map.singleton (normalise key) val)

attrs :: forall a. (Ord a, StringLike a) => Fold (TagTree a) (a, a)
attrs = _attrs . attrAttributes . to Map.toList . each . to (first normalise)

attr :: forall a. (Ord a, StringLike a) => a -> Traversal' (TagTree a) a
attr k = _attrs . ix k

attr_ :: forall a. (Ord a, StringLike a) => a -> Traversal' (TagTree a) (Maybe a)
attr_ k = _attrs . at k

type instance IxValue (Attrs a) = a
type instance Index (Attrs a) = a

instance (Ord a, StringLike a) => Ixed (Attrs a)

instance (Ord a, StringLike a) => At (Attrs a) where
  at ix f (Attrs cls attr) = Attrs cls <$> at (normalise ix) f attr

_text :: forall m s. (Monad m, Eq s) => Filter m (TagTree s) s
_text = isF (^? _TagLeaf . _TagText)

_comment :: forall m s. (Monad m, Eq s) => Filter m (TagTree s) s
_comment = isF (^? _TagLeaf . _TagComment)

text' :: forall m s a. (Monad m, Monoid s) => Filter m a s -> Filter m a (TagTree s)
text' fs = collect fs >>> arr (TagLeaf . TagText . fold)

parseF :: forall m s a. (Monad m, StringLike s) => Filter m s (TagTree s)
parseF = nondet parseTree

element
  :: forall m s a. (Monad m, IsString s)
  => s
  -> [Filter m a (TagTree s)]
  -> Filter m a (TagTree s)
element tag xs = broadcast xs >>> arr (TagBranch tag [])

children :: Traversal' (TagTree s) [TagTree s]
children = _TagBranch . _3

deriving instance Generic (Tag a)
deriving instance Generic (TagTree a)
instance NFData a => NFData (Tag a)
instance NFData a => NFData (TagTree a)
