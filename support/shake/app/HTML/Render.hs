{-# LANGUAGE DeriveGeneric, DeriveAnyClass, OverloadedStrings, BlockArguments #-}
module HTML.Render where

import Prelude hiding ((!!))

import Agda.Interaction.Highlighting.Common

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Syntax.Common.Aspect
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Function
import Agda.Utils.DocTree

import Control.DeepSeq
import Control.Monad

import qualified Data.HashMap.Strict as Hm
import qualified Data.Text.Lazy as Tl
import qualified Data.Text as Text
import Data.HashMap.Strict (HashMap)
import Data.Foldable
import Data.Hashable
import Data.Aeson
import Data.Maybe
import Data.Text (Text)

import GHC.Generics

import qualified Network.URI.Encode

import System.FilePath

import qualified Text.PrettyPrint.Annotated.HughesPJ as Ppr
import qualified Text.PrettyPrint.Annotated as Ppr

import qualified Text.Blaze.Html5.Attributes as Attr
import Text.Blaze.Html.Renderer.Text ( renderHtml )
import Text.Blaze.Html5 as Html hiding (map)

renderToHtml :: Doc -> Text
renderToHtml = finish . renderTree' Html.text toblaze . renderToTree where
  toblaze a t = Html.span do
    aspectsToHtml Nothing mempty Nothing a t
    unless (null (note a)) do
      Html.span (string (note a)) !! [Attr.class_ "Note"]

  finish = Tl.toStrict . renderHtml . wrapper
  wrapper = (!! [Attr.class_ "Agda"]) . Html.pre

-- | Data about an identifier
data Identifier = Identifier
  { idIdent   :: Text
  , idAnchor  :: Text
  , idType    :: Text
  , idTooltip :: Text
  }
  deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON, NFData)

instance Hashable Identifier where
  hashWithSalt s = hashWithSalt s . idAnchor

-- | Attach multiple Attributes
(!!) :: Html -> [Attribute] -> Html
h !! as = h ! mconcat as

-- | Converts module names to the corresponding HTML file names.
modToFile :: TopLevelModuleName -> String -> FilePath
modToFile m ext = Network.URI.Encode.encode $ render (pretty m) <.> ext

-- Put anchors that enable referencing that token.
-- We put a fail safe numeric anchor (file position) for internal references
-- (issue #2756), as well as a heuristic name anchor for external references
-- (issue #2604).
aspectsToHtml :: Maybe TopLevelModuleName -> HashMap Text.Text (Int, Identifier) -> Maybe Int -> Aspects -> Html -> Html
aspectsToHtml ourmod types pos mi =
  applyWhen hereAnchor (anchorage nameAttributes mempty <>) . anchorage posAttributes
  where
  -- Warp an anchor (<A> tag) with the given attributes around some HTML.
  anchorage :: [Attribute] -> Html -> Html
  anchorage attrs html = Html.a html !! attrs

  -- File position anchor (unique, reliable).
  posAttributes :: [Attribute]
  posAttributes = concat
    [ [Attr.id $ stringValue $ show pos | Just pos <- [pos]]
    , concat (maybeToList (link <$> definitionSite mi))
    , Attr.class_ (stringValue $ unwords classes) <$ guard (not $ null classes)
    ]

  -- Named anchor (not reliable, but useful in the general case for outside refs).
  nameAttributes :: [Attribute]
  nameAttributes = [ Attr.id $ stringValue $ fromMaybe __IMPOSSIBLE__ $ mDefSiteAnchor ]

  classes = concat
    [ otherAspectClasses (toList $ otherAspects mi)
    , concatMap aspectClasses (aspect mi)
    ]

  aspectClasses (Name mKind op) = kindClass ++ opClass
    where
    kindClass = toList $ fmap showKind mKind

    showKind (Constructor Inductive)   = "InductiveConstructor"
    showKind (Constructor CoInductive) = "CoinductiveConstructor"
    showKind k                         = show k

    opClass = ["Operator" | op]
  aspectClasses a = [show a]

  otherAspectClasses = map show

  -- Should we output a named anchor?
  -- Only if we are at the definition site now (@here@)
  -- and such a pretty named anchor exists (see 'defSiteAnchor').
  hereAnchor :: Bool
  hereAnchor = here && isJust mDefSiteAnchor

  mDefinitionSite :: Maybe DefinitionSite
  mDefinitionSite = definitionSite mi

  -- Are we at the definition site now?
  here :: Bool
  here = maybe False defSiteHere mDefinitionSite

  mDefSiteAnchor  :: Maybe String
  mDefSiteAnchor  = maybe __IMPOSSIBLE__ defSiteAnchor mDefinitionSite

  link :: DefinitionSite -> [Html.Attribute]
  link ds@(DefinitionSite m defPos _here _aName) =
    let
      anchor :: String
      anchor = definitionSiteToAnchor ds

      ident_ :: Maybe Int
      ident_ = fst <$> Hm.lookup (Text.pack anchor) types
    in [ Attr.href $ stringValue $ anchor ]
    ++ maybeToList (Html.dataAttribute "module" . stringValue . show . pretty <$> ourmod)
    ++ maybeToList (Html.dataAttribute "identifier" . stringValue . show <$> ident_)

definitionSiteToAnchor :: DefinitionSite -> String
definitionSiteToAnchor (DefinitionSite m defPos _ _) =
  applyUnless (defPos <= 1)
    (++ "#" ++ Network.URI.Encode.encode (show defPos))
    (Network.URI.Encode.encode $ modToFile m "html")
