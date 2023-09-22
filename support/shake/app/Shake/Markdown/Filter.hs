{-# LANGUAGE OverloadedStrings, BlockArguments, Arrows #-}
module Shake.Markdown.Filter (postProcessHtml) where

import Control.Applicative
import Control.Category
import Control.Arrow
import Control.Monad
import Control.Lens hiding (element, children, (<.>))

import qualified Data.HashMap.Strict as HashMap
import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.HashMap.Strict (HashMap)
import Data.Digest.Pure.SHA
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Maybe
import Data.Char
import Data.Set (Set)

import qualified Citeproc as Cite
import Text.HTML.TagSoup.Tree
import Text.Pandoc.Definition
import Text.Pandoc.Builder (Inlines)
import Text.HTML.TagSoup

import Development.Shake.FilePath
import Development.Shake

import Agda.Utils.Monad

import Prelude hiding (id, (.))

import Filter.TagSoup.Attributes as A
import Filter.TagSoup.Elements as H
import Filter.TagSoup
import Shake.Options
import Definitions
import Shake.KaTeX
import Filter

import Timer

postProcessHtml
  :: String
  -> Map Text (Cite.Reference Inlines)
  -> [Tag Text]
  -> Action [Tag Text]
postProcessHtml modname citations stream = do
  let tree = tagTree stream

  skipAgda <- getSkipAgda

  icons <- Set.fromList . fmap (Text.pack . map toLower . dropExtension)
    <$> getDirectoryFiles "support/web/highlights" ["*.svg"]

  let
    isIcon t
      | Text.toLower t `elem` icons = pure t
      | otherwise                   = Nothing

    iconSpan icn = do
      tree <- parseTree . Text.pack <$>
        readFile' ("support/web/highlights" </> Text.unpack icn -<.> "svg")
      let
        fallback = Text.cons (toUpper (Text.head icn)) (Text.tail icn)

      build $ pures tree
        >>> _svg
        >>> H.span [ id, H.span [text' (_svg >>>. attr_ "aria-label" . non fallback)] ]
              ! class_ "highlight-icon"

    add icon = proc it -> do
      icon <- eff (const (iconSpan icon)) -< ()
      overF children (arr (icon:)) -<< it

    [identifiers] = runIdentity . flip runFilter tree $
      collect (explore >>> everywhereF proc elt -> do
        (href, cls) <- elt >- _a >>> (
          pick A._href &&& pick A._class)
        text <- elt >-
          foldF (id /> _text) >>> filterF (not . Text.null)
        id -< HashMap.insertWith (\_ old -> old) text (href, cls))
        >>> arr (foldr ($) mempty)

    mod :: HtmlFilter Action Text
    mod = rewriteF $ asum $
      [ detailsHighlight icons add
      , divHighlight icons add
      , renderKatex
      , resolveWikilink
      , uncommentAgda
      , addCitationTitles citations
      , renderDiagrams
      , headerEmoji
      ] ++
      [ linkIdentifiers identifiers | not skipAgda ]

  (out, diagrams) <- timedM (Text.pack modname) do
    tree <- concatMapM (runFilter mod) tree

    diagrams <- flip runFilter tree $ foldF $ explore >>> deepF (
          _img ? A.class_ "diagram quiver"
      >>> pick A._src
      >>> arr Set.singleton)

    pure (flattenTree tree, diagrams)

  out <$ need [ "_build/html/" </> Text.unpack path | path <- foldMap Set.toList diagrams ]

detailsHighlight, divHighlight
  :: Set Text
  -> (Text -> HtmlFilter Action Text)
  -> HtmlFilter Action Text

detailsHighlight icons add = proc it -> do
  icon <- it >- _details >>> pick attrs
    >>> guardF (arr (\(a, b) -> a `elem` icons && Text.null b))
    >>> arr fst
  it >>- addClass icon
      &> tryF (H._summary >>> add icon)

divHighlight icons add =
  proc it -> do
    clz <- it >- _div >>> pick classes
    case mapMaybe isIcon (Set.toList clz) of
      [icn] -> it >>- add icn
      _     -> () >>- empty
  where isIcon t = t <$ icons ^. at (Text.toLower t)

renderKatex, resolveWikilink, uncommentAgda, renderDiagrams, headerEmoji :: HtmlFilter Action Text

renderKatex = proc it -> do
  it >- el "eq"
  k <- () >>- case it ^? attr "env" of
    Just "math"    -> pure getInlineMath
    Just "display" -> pure getDisplayMath
    _              -> empty
  it >>- foldF (deepF _text) >>> eff k
     >>> parseF

resolveWikilink = proc it -> do
  it >- _a ? A.title "wikilink"
  target <- it >- pick A._href
    >>> eff getWikiLinkUrl
  id -<< it & attr_ "href" ?~ target

uncommentAgda = proc it -> do
  tree <- it >- collect $
        _comment
    >>> parseF
    >>> _pre ? class_ "Agda"

  tree >- filterF (not . null)
    >>> H.div [explore] ! class_ "commented-out"

renderDiagrams = proc it -> do
  cb <- it >- (_pre ? A.class_ "quiver") /> _code

  (text, sha) <- cb >- foldF (deepF _text)
    >>> id &&& arr (showDigest . sha1 . LazyBS.fromStrict . Text.encodeUtf8)

  title <- cb >- collect (pick (attr "title"))
    >>> arr (fromMaybe "commutative diagram" . listToMaybe)

  let
    sha' = Text.pack sha
    diagram c = img []
      ! A.title  (pure title)
      ! A.src    (pure (c <> "-" <> sha' <> ".svg"))
      ! A.class_ (pure ("diagram diagram-" <> c))
      >>> arr (attr_ "data-digest" ?~ sha')
    propagate = foldOf _attrs it & at "id" .~ Nothing
    ident :: Filter Action a (Attrs Text)
    ident = maybe (pure mempty) (A.id_ . pure) (it ^? A._id)

  ()
    >>- eff (\_ -> writeFile' ("_build/diagrams/" </> sha <.> "tex") (Text.unpack text))
    >>> H.div [ diagram "light" , diagram "dark" ]
          ! ident
          ! A.class_ "diagram-container"
    >>> id &> arr (_attrs <>~ propagate)

headerEmoji = asum
  [ proc it -> do
      ident <- it >- el tag >>> pick A._id
      overF children (collect (
          H.a [ H.span [ pure it /> id ]
              , H.span [ text' "🔗" ] ! A.class_ "header-link-emoji"
              ]
          ! A.href   (pure (Text.cons '#' ident))
          ! A.class_ "header-link"))
        -<< it
  | num <- [1..6]
  , let tag = Text.pack ('h':show num)
  ]

linkIdentifiers :: HashMap Text (Text, Text) -> HtmlFilter Action Text
linkIdentifiers identifiers = proc it -> do
  elt <- it >- _code ? class_ "Agda"

  (url, cls) <- it >- foldF (pick (attr "data-ident") <|> (_code /> _text))
    >>> isF (`HashMap.lookup` identifiers)

  () >>-
    H.span [ a [code [pure elt /> id]] ! class_ (pure cls) ! href (pure url) ]
      ! class_ "Agda"

addCitationTitles :: Map Text (Cite.Reference Inlines) -> HtmlFilter Action Text
addCitationTitles refMap = proc it -> do
  ref <- it >- _a ? A.role "doc-biblioref"
    >>> foldF (pick A._href)
    >>> isF (flip Map.lookup refMap <=< Text.stripPrefix "#ref-")
  (it >>- id)
    ! (| A.title (isF id -< Cite.valToText =<< Cite.lookupVariable "title" ref) |)
