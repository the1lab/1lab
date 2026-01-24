-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Function for generating highlighted, hyperlinked HTML from Agda
-- sources.
{-# LANGUAGE FlexibleInstances, DeriveGeneric, OverloadedStrings, DeriveAnyClass, BlockArguments #-}
module HTML.Base
  ( HtmlOptions(..)
  , defaultHtmlOptions
  , HtmlHighlight(..)
  , srcFileOfInterface
  , defaultPageGen
  , modToFile, highlightedFileExt
  , Identifier(..)
  ) where

import Prelude hiding ((!!), concatMap)

import Control.Monad.Trans ( MonadIO(..) )
import Control.DeepSeq

import qualified Data.Text.Lazy as T
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import Data.IntMap.Strict (IntMap)
import Data.List.Split (splitWhen)
import Data.Text.Lazy (Text)
import Data.Binary
import Data.Maybe

import GHC.Generics (Generic)

import System.FilePath

import Text.Blaze.Html5
    ( preEscapedToHtml
    , toHtml
    , stringValue
    , Html
    , (!)
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

import HTML.Render

-- | Determine how to highlight the file

data HtmlHighlight = HighlightAll | HighlightCode | HighlightAuto
  deriving (Show, Eq, Generic)

instance NFData HtmlHighlight

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
  , htmlOptBaseUrl    :: FilePath
  , htmlOptHighlight  :: HtmlHighlight
  , htmlOptGenTypes   :: Bool
  } deriving (Eq, Show, Generic, NFData)

defaultHtmlOptions :: FilePath -> HtmlOptions
defaultHtmlOptions baseurl = HtmlOptions
  { htmlOptDir        = "_build/html0"
  , htmlOptBaseUrl    = baseurl
  , htmlOptHighlight  = HighlightAuto
  , htmlOptGenTypes   = True
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

srcFileOfInterface :: TCM.Interface -> HtmlInputSourceFile
srcFileOfInterface i = HtmlInputSourceFile
  (TCM.iTopLevelModuleName i)
  (TCM.iFileType i)
  (TCM.iSource i)
  (TCM.iHighlighting i)

renderSourceFile
  :: IntMap Identifier
  -> HtmlOptions
  -> HtmlInputSourceFile
  -> Text
renderSourceFile locals opts (HtmlInputSourceFile moduleName fileType sourceCode hinfo) =
  let
    htmlHighlight = htmlOptHighlight opts

    tokens = tokenStream sourceCode hinfo
    onlyCode = highlightOnlyCode htmlHighlight fileType

    pageContents = code locals onlyCode fileType moduleName tokens
  in page opts onlyCode moduleName pageContents

defaultPageGen
  :: MonadIO m
  => HtmlOptions
  -> HtmlModule
  -> HtmlInputSourceFile
  -> m ()
defaultPageGen opts types srcFile@(HtmlInputSourceFile moduleName ft _ _) = do
  let
    ext        = highlightedFileExt (htmlOptHighlight opts) ft
    target     = htmlOptDir opts </> modToFile moduleName ext
    typeTarget = htmlOptDir opts </> modToFile moduleName "bin"
    html       = renderSourceFile (htmlModIdentifiers types) opts srcFile

  liftIO do
    UTF8.writeTextToFile target html
    encodeFile typeTarget types

-- | Constructs the web page, including headers.

page
  :: HtmlOptions
  -> Bool                -- ^ Whether to reserve literate
  -> TopLevelModuleName  -- ^ Module to be highlighted.
  -> Html
  -> Text
page opts htmlHighlight modName pageContent =
  renderHtml $ if htmlHighlight
               then pageContent
               else Html5.docTypeHtml $ hdr <> rest
  where
    base = htmlOptBaseUrl opts

    hdr = Html5.head $ mconcat
      [ Html5.meta !! [ Attr.charset "utf-8" ]
      , Html5.title (toHtml . render $ pretty modName)
      , Html5.link !!
        [ Attr.rel "stylesheet"
        , Attr.href $ stringValue $ base </> "css/default.css"
        ]
      , Html5.script $ "Object.assign(window, { baseUrl: \"" <> toHtml base <> "\"})"
      , Html5.script mempty !!
          [ Attr.type_ "text/javascript"
          , Attr.src $ stringValue $ base </> "code-only.js"
          ]
      ]

    rest = Html5.body $ (Html5.pre ! Attr.class_ "Agda") pageContent

-- | Position, Contents, Information

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
  :: IntMap Identifier
  -> Bool     -- ^ Whether to generate non-code contents as-is
  -> FileType -- ^ Source file type
  -> TopLevelModuleName
  -> [TokenInfo]
  -> Html
code locals _onlyCode _fileType mod = mconcat . map mkMd . splitByMarkup
  where
  trd (_, _, a) = a

  splitByMarkup :: [TokenInfo] -> [[TokenInfo]]
  splitByMarkup = splitWhen $ (== Just Markup) . aspect . trd

  mkHtml :: TokenInfo -> Html
  mkHtml (pos, s, mi) =
    -- Andreas, 2017-06-16, issue #2605:
    -- Do not create anchors for whitespace.
    applyUnless (mi == mempty) (aspectsToHtml locals (Just mod) (Just pos) mi) $ toHtml s

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
