{-# LANGUAGE TemplateHaskell, LambdaCase, BlockArguments #-}
module Filter.TagSoup.TH where

import Control.Applicative
import Control.Lens

import Agda.Utils.Monad

import Data.String
import Data.Char

import Language.Haskell.TH

import Text.HTML.TagSoup.Tree
import Text.HTML.TagSoup
import Text.StringLike

import Filter

makePrisms ''TagTree
makePrisms ''Tag

defineElements :: [String] -> DecsQ
defineElements = concatMapM \elt -> do
  [arg1, arg2] <- traverse (newName . pure) "xy"
  let
    elt' = pure (LitE (StringL (filter (/= '_') elt)))
    query = mkName ('_':filter (/= '_') elt)
    prism = mkName ('_':toUpper (head elt):filter (/= '_') (tail elt))
    make  = mkName elt
    clz e = clause [] (normalB e) []

    attrs  = conT (mkName "Attrs")
    attrsi = varE (mkName "_Attrs")

  sequence
    [ sigD query [t| forall m s. (Monad m, Ord s, StringLike s) => Filter m (TagTree s) (TagTree s) |]
    , funD query [clz [| guardF (True <$ pick $(varE prism)) |]]

    , sigD prism [t| forall m s. (StringLike s, Ord s) => Prism' (TagTree s) (s, $attrs s, [TagTree s]) |]
    , funD prism [clz [|
        prism' (\(_, a, c) -> TagBranch $elt' (review $attrsi a) c) \case
          TagBranch s a c | s == $elt' -> Just (s, review (from $attrsi) a, c)
          _ -> Nothing
        |]]

    , sigD make [t| forall m s a. (Monad m, IsString s) => [Filter m a (TagTree s)] -> Filter m a (TagTree s) |]
    , funD make [clause [varP arg1] (normalB [| broadcast $(varE arg1) >>> arr (TagBranch $elt' []) |]) []]
    ]

defineAttributes :: [String] -> DecsQ
defineAttributes = concatMapM \attr -> do
  let make  = mkName attr
      query = mkName ('_':filter (/= '_') attr)
      attr' = pure (LitE (StringL (filter (/= '_') attr)))

      attrs  = mkName "Attrs"
      mklens = mkName "attr"
  sequence
    [ sigD make [t| forall m s x. (Monad m, StringLike s, Ord s) => Filter m x s -> Filter m x ($(conT attrs) s) |]
    , funD make [clause [] (normalB [| fmap (singletonAttrs $attr') |]) []]
    , sigD query [t| forall x. (StringLike x, Ord x) => Traversal' (TagTree x) x |]
    , funD query [clause [] (normalB [| $(varE mklens) $attr' |]) []]
    ]
