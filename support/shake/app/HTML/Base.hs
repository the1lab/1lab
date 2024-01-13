-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Function for generating highlighted, hyperlinked HTML from Agda
-- sources.
{-# LANGUAGE FlexibleInstances, DeriveGeneric, OverloadedStrings, DeriveAnyClass #-}
module HTML.Base
  ( HtmlOptions(..)
  , defaultHtmlOptions
  , HtmlHighlight(..)
  , srcFileOfInterface
  , defaultPageGen
  , MonadLogHtml(logHtml)
  , LogHtmlT
  , runLogHtmlWith
  , modToFile, highlightedFileExt
  , Identifier(..)
  ) where

import Prelude hiding ((!!), concatMap)

import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans ( MonadIO(..), lift )
import Control.Monad.Trans.Reader ( ReaderT(runReaderT), ask )

import Data.Function ( on )
import Data.Foldable (toList, concatMap)
import Data.Maybe
import Data.Aeson
import qualified Data.IntMap as IntMap
import qualified Data.List   as List
import Data.List.Split (splitWhen)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text as Ts
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Hm

import GHC.Generics (Generic)

import qualified Network.URI.Encode

import System.FilePath

import Text.Blaze.Html5
    ( preEscapedToHtml
    , toHtml
    , stringValue
    , Html
    , (!)
    , Attribute
    , textValue
    )
import qualified Text.Blaze.Html5 as Html5
import qualified Text.Blaze.Html5.Attributes as Attr
import Text.Blaze.Html.Renderer.Text ( renderHtml )
  -- The imported operator (!) attaches an Attribute to an Html value
  -- The defined operator (!!) attaches a list of such Attributes

-- import Paths_Agda

import Agda.Interaction.Highlighting.Precise hiding (toList)

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Common

import qualified Agda.TypeChecking.Monad as TCM
  ( Interface(..)
  )

import Agda.Utils.Function
import qualified Agda.Utils.IO.UTF8 as UTF8

import Agda.Utils.Impossible

-- | Determine how to highlight the file

data HtmlHighlight = HighlightAll | HighlightCode | HighlightAuto
  deriving (Show, Eq, Generic)

instance NFData HtmlHighlight

-- | Data about an identifier
data Identifier = Identifier
  { idIdent  :: Ts.Text
  , idAnchor :: Ts.Text
  , idType   :: Ts.Text
  }
  deriving (Eq, Show, Ord, Generic, ToJSON, FromJSON, NFData)


highlightOnlyCode :: HtmlHighlight -> FileType -> Bool
highlightOnlyCode HighlightAll  _ = False
highlightOnlyCode HighlightCode _ = True
highlightOnlyCode HighlightAuto AgdaFileType = False
highlightOnlyCode HighlightAuto MdFileType   = True
highlightOnlyCode HighlightAuto _            = True

-- | Determine the generated file extension

highlightedFileExt :: HtmlHighlight -> FileType -> String
highlightedFileExt hh ft
  | not $ highlightOnlyCode hh ft = "html"
  | otherwise = case ft of
      AgdaFileType -> "html"
      MdFileType   -> "md"
      _            -> __IMPOSSIBLE__

-- | Options for HTML generation

data HtmlOptions = HtmlOptions
  { htmlOptDir        :: FilePath
  , htmlOptHighlight  :: HtmlHighlight
  , htmlOptJsUrl      :: Maybe FilePath
  , htmlOptCssUrl     :: FilePath
  , htmlOptGenTypes   :: Bool
  , htmlOptDumpIdents :: Maybe FilePath
  } deriving (Eq, Show, Generic, NFData)

defaultHtmlOptions :: HtmlOptions
defaultHtmlOptions = HtmlOptions
  { htmlOptDir       = "_build/html0"
  , htmlOptHighlight = HighlightAuto
  , htmlOptJsUrl     = Just "code-only.js"
  , htmlOptCssUrl    = "/css/default.css"
  , htmlOptGenTypes  = True
  , htmlOptDumpIdents = Just "_build/all-types.json"
  }

-- | Internal type bundling the information related to a module source file

data HtmlInputSourceFile = HtmlInputSourceFile
  { _srcFileModuleName :: TopLevelModuleName
  , _srcFileType :: FileType
  -- ^ Source file type
  , _srcFileText :: Text
  -- ^ Source text
  , _srcFileHighlightInfo :: HighlightingInfo
  -- ^ Highlighting info
  }
  deriving Show

-- | Bundle up the highlighting info for a source file

srcFileOfInterface :: TopLevelModuleName -> TCM.Interface -> HtmlInputSourceFile
srcFileOfInterface m i = HtmlInputSourceFile m (TCM.iFileType i) (TCM.iSource i) (TCM.iHighlighting i)

-- | Logging during HTML generation

type HtmlLogMessage = String
type HtmlLogAction m = HtmlLogMessage -> m ()

class MonadLogHtml m where
  logHtml :: HtmlLogAction m

type LogHtmlT m = ReaderT (HtmlLogAction m) m

instance Monad m => MonadLogHtml (LogHtmlT m) where
  logHtml message = do
    doLog <- ask
    lift $ doLog message

runLogHtmlWith :: Monad m => HtmlLogAction m -> LogHtmlT m a -> m a
runLogHtmlWith = flip runReaderT

renderSourceFile
  :: HashMap Ts.Text Identifier
  -> HtmlOptions
  -> HtmlInputSourceFile
  -> Text
renderSourceFile types opts = renderSourcePage where
  htmlHighlight = htmlOptHighlight opts
  renderSourcePage (HtmlInputSourceFile moduleName fileType sourceCode hinfo) =
    page opts onlyCode moduleName pageContents
    where
      tokens = tokenStream sourceCode hinfo
      onlyCode = highlightOnlyCode htmlHighlight fileType
      pageContents = code types onlyCode fileType tokens

defaultPageGen
  :: (MonadIO m, MonadLogHtml m)
  => HashMap Ts.Text Identifier
  -> HtmlOptions
  -> HtmlInputSourceFile -> m ()
defaultPageGen types opts srcFile@(HtmlInputSourceFile moduleName ft _ _) = do
  let
    ext        = highlightedFileExt (htmlOptHighlight opts) ft
    target     = htmlOptDir opts </> modToFile moduleName ext
    typeTarget = htmlOptDir opts </> modToFile moduleName "json"
    html       = renderSourceFile types opts srcFile

  logHtml $ render $ "Generating HTML for" <+> pretty moduleName
  writeRenderedHtml html target
  liftIO $ encodeFile typeTarget types

-- | Converts module names to the corresponding HTML file names.
modToFile :: TopLevelModuleName -> String -> FilePath
modToFile m ext = Network.URI.Encode.encode $ render (pretty m) <.> ext

-- | Generates a highlighted, hyperlinked version of the given module.

writeRenderedHtml
  :: MonadIO m
  => Text       -- ^ Rendered page
  -> FilePath   -- ^ Output path.
  -> m ()
writeRenderedHtml html target = liftIO $ UTF8.writeTextToFile target html


-- | Attach multiple Attributes

(!!) :: Html -> [Attribute] -> Html
h !! as = h ! mconcat as

-- | Constructs the web page, including headers.

page
  :: HtmlOptions
  -> Bool                  -- ^ Whether to reserve literate
  -> TopLevelModuleName  -- ^ Module to be highlighted.
  -> Html
  -> Text
page opts htmlHighlight modName pageContent =
  renderHtml $ if htmlHighlight
               then pageContent
               else Html5.docTypeHtml $ hdr <> rest
  where

    hdr = Html5.head $ mconcat
      [ Html5.meta !! [ Attr.charset "utf-8" ]
      , Html5.title (toHtml . render $ pretty modName)
      , Html5.link !! [ Attr.rel "stylesheet"
                      , Attr.href $ stringValue (htmlOptCssUrl opts)
                      ]
      , case htmlOptJsUrl opts of
          Nothing -> mempty
          Just script ->
            Html5.script mempty !!
            [ Attr.type_ "text/javascript"
            , Attr.src $ stringValue script
            ]
      ]

    rest = Html5.body $ (Html5.pre ! Attr.class_ "Agda") pageContent

-- | Position, Contents, Infomation

type TokenInfo =
  ( Int
  , String
  , Aspects
  )

-- | Constructs token stream ready to print.

tokenStream
  :: Text             -- ^ The contents of the module.
  -> HighlightingInfo -- ^ Highlighting information.
  -> [TokenInfo]
tokenStream contents info =
  map (\cs -> case cs of
          (mi, (pos, _)) : _ ->
            (pos, map (snd . snd) cs, fromMaybe mempty mi)
          [] -> __IMPOSSIBLE__) $
  List.groupBy ((==) `on` fst) $
  zipWith (\pos c -> (IntMap.lookup pos infoMap, (pos, c))) [1..] (T.unpack contents)
  where
  infoMap = toMap info

-- | Constructs the HTML displaying the code.

code
  :: HashMap Ts.Text Identifier
  -> Bool     -- ^ Whether to generate non-code contents as-is
  -> FileType -- ^ Source file type
  -> [TokenInfo]
  -> Html
code types _onlyCode _fileType = mconcat . map mkMd . splitByMarkup
  where
  trd (_, _, a) = a

  splitByMarkup :: [TokenInfo] -> [[TokenInfo]]
  splitByMarkup = splitWhen $ (== Just Markup) . aspect . trd

  mkHtml :: TokenInfo -> Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (annotate pos mi) $ toHtml s

  backgroundOrAgdaToHtml :: TokenInfo -> Html
  backgroundOrAgdaToHtml token@(_, s, mi) = case aspect mi of
    Just Background -> preEscapedToHtml s
    Just Markup     -> __IMPOSSIBLE__
    _               -> mkHtml token

  -- The assumption here is that Background tokens and Agda tokens are always
  -- separated by Markup tokens, so these runs only contain one kind.
  mkMd :: [TokenInfo] -> Html
  mkMd tokens = if containsCode then formatCode else formatNonCode
    where
      containsCode = any ((/= Just Background) . aspect . trd) tokens

      formatCode = Html5.pre ! Attr.class_ "Agda" $ mconcat $ backgroundOrAgdaToHtml <$> tokens
      formatNonCode = mconcat $ backgroundOrAgdaToHtml <$> tokens

  -- Put anchors that enable referencing that token.
  -- We put a fail safe numeric anchor (file position) for internal references
  -- (issue #2756), as well as a heuristic name anchor for external references
  -- (issue #2604).
  annotate :: Int -> Aspects -> Html -> Html
  annotate pos mi =
    applyWhen hereAnchor (anchorage nameAttributes mempty <>) . anchorage posAttributes
    where
    -- Warp an anchor (<A> tag) with the given attributes around some HTML.
    anchorage :: [Attribute] -> Html -> Html
    anchorage attrs html = Html5.a html !! attrs

    -- File position anchor (unique, reliable).
    posAttributes :: [Attribute]
    posAttributes = concat
      [ [Attr.id $ stringValue $ show pos ]
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

    link :: DefinitionSite -> [Attribute]
    link (DefinitionSite m defPos _here _aName) =
      [ Attr.href $ stringValue $ anchor ]
      ++ maybeToList (Html5.dataAttribute "type" . textValue . idType <$> ident_)
      where
        anchor :: String
        anchor =
          applyUnless (defPos <= 1)
            (++ "#" ++ Network.URI.Encode.encode (show defPos))
            (Network.URI.Encode.encode $ modToFile m "html")
        ident_ :: Maybe Identifier
        ident_ = Hm.lookup (Ts.pack anchor) types
