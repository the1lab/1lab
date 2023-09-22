{-# LANGUAGE RoleAnnotations #-}
module Filter.TagSoup where

import Text.HTML.TagSoup.Tree
import Text.StringLike

import Control.Lens.Traversal
import Control.Lens.Iso

type Attrs :: * -> *
type role Attrs nominal
data Attrs a
singletonAttrs :: forall a. (Ord a, StringLike a) => a -> a -> Attrs a
attr :: forall a. (Ord a, StringLike a) => a -> Traversal' (TagTree a) a
_Attrs :: forall a. (StringLike a, Ord a) => Iso' [(a, a)] (Attrs a)
