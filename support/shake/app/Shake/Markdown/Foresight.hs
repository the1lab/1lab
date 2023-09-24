{-# LANGUAGE OverloadedStrings, TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveGeneric, DeriveAnyClass, DerivingStrategies #-}
{-# LANGUAGE ViewPatterns, BlockArguments, LambdaCase, TemplateHaskell #-}
module Shake.Markdown.Foresight
  ( foresightRules
  , WikiLink(..)
  , isWikiLink
  , getWikiLink, getWikiLinkUrl
  , Glossary(_getEntries), GlossaryQ(..)
  , Mangled(getMangled), mangleLink
  , Definition(..), definitionTarget

  , ModuleInfo, modDiagrams, modMathsInline, modMathsDisplay, modMathsSpans
  )
  where

import Agda.Utils.Impossible

import Control.Monad.IO.Class
import Control.Exception
import Control.DeepSeq
import Control.Arrow (first)
import Control.Lens hiding ((<.>))

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.Digest.Pure.SHA
import Data.Map.Strict (Map)
import Data.Function
import Data.Hashable
import Data.Foldable
import Data.Monoid ( Endo(..) )
import Data.Binary ( Binary )
import Data.List (intersperse, sortOn, groupBy)
import Data.Text (Text)
import Data.Ord (Down(..))
import Data.Set (Set)

import Development.Shake.FilePath
import Development.Shake

import GHC.Generics (Generic)

import HTML.Backend (moduleName)

import Text.Pandoc.Walk
import Text.Pandoc

import {-# SOURCE #-} Shake.Markdown (readLabMarkdown)

newtype Mangled = Mangled { getMangled :: Text }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Binary, NFData, Hashable)

data Definition = Definition
  { definitionModule :: FilePath
  , definitionAnchor :: Text
  , definitionCopy   :: Bool
  }
  deriving (Show, Generic, NFData, Binary)

instance Eq Definition where
  (==) = (==) `on` definitionAnchor

instance Hashable Definition where
  hashWithSalt s = hashWithSalt s . definitionAnchor

data ModuleInfo = ModuleInfo
  { _modDefns        :: Map Mangled Definition
  , _modDiagrams     :: Set Text

  , _modMathsInline  :: Set Text
  , _modMathsDisplay :: Set Text

  , _modMathsSpans   :: !Int
    -- ^ Sum of the sizes of the two sets
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Binary, NFData, Hashable)

newtype Glossary = Glossary { _getEntries :: Map Mangled Definition }
  deriving (Show, Eq, Generic)
  deriving anyclass (Binary, NFData, Hashable)

makeLenses ''ModuleInfo
makeLenses ''Glossary

data GlossaryQ = GlossaryQ
  deriving (Eq, Show, Generic, NFData, Binary, Hashable)
newtype LinkTargetQ = LinkTargetQ Text
  deriving (Eq, Show, Generic)
  deriving anyclass (NFData, Binary, Hashable)

type instance RuleResult GlossaryQ   = Glossary
type instance RuleResult LinkTargetQ = Text

mangleLink :: Text -> Mangled
mangleLink = doit where
  doit
    = Mangled
    . Text.concat
    . intersperse (Text.singleton '-')
    . map (Text.filter wordChar . Text.toLower)
    . Text.words

  wordChar '-' = True
  wordChar '[' = True
  wordChar c = ('a' <= c && c <= 'z')
            || ('0' <= c && c <= '9')

scanModule :: MonadIO m => FilePath -> FilePath -> m ModuleInfo
scanModule anchor input = liftIO do
  Pandoc _meta markdown <- readLabMarkdown input
  let
    act = query (scanBlock anchor) markdown <> query scanInline markdown
    out = appEndo act $ ModuleInfo mempty mempty mempty mempty 0
  pure out

addDefinition :: Lens' t (Map Mangled Definition) -> Mangled -> Definition -> t -> t
addDefinition defs _ Definition{definitionCopy = True} ge = ge
addDefinition defs key@(getMangled -> keyt) def it = go False key (plural it) where
  plural
    | Text.null keyt = error $ "Definition has empty key: " ++ show def
    | Text.last keyt == 'y' = go True (Mangled (Text.init keyt <> "ies"))
    | otherwise             = go True (Mangled (keyt <> "s"))
  go c key ge = case ge ^. defs . at key of
    Just def' | def' /= def -> error $ unlines
      [ "Conflict when building link map:"
      , "The files " ++ show (definitionModule def) ++ " and " ++ show (definitionModule def')
        ++ " both define the term " ++ show key
      ]
    _ -> ge & defs . at key ?~ def{definitionCopy = c}

scanBlock :: FilePath -> Block -> Endo ModuleInfo
scanBlock fp = go where
  mod = dropExtension fp
  add id v = Endo $ addDefinition modDefns (mangleLink v) Definition
    { definitionModule = mod
    , definitionAnchor = id
    , definitionCopy   = False
    }

  addMany id = foldMap (add id) . Text.words

  go (Div (id, [only], keys) _blocks) | "definition" == only, not (Text.null id) =
    let aliases = foldMap (addMany id) (lookup "alias" keys)
    in add id id <> aliases

  go (Header _ (id, _, keys) _inline) =
    foldMap (addMany id) (lookup "defines" keys)

  go (CodeBlock (_, clz, _) code)
    | "quiver" `elem` clz = Endo (modDiagrams %~ Set.insert code)
    | null clz = error $ "Code block without class in " ++ fp

  go _ = mempty

scanInline :: Inline -> Endo ModuleInfo
scanInline = \case
  Math DisplayMath span -> Endo $ (modMathsDisplay %~ Set.insert span)
                                . (modMathsSpans %~ succ)
  Math InlineMath span -> Endo $ (modMathsInline %~ Set.insert span)
                               . (modMathsSpans %~ succ)
  _ -> mempty

definitionTarget :: Definition -> Text
definitionTarget def = Text.pack (definitionModule def) <> ".html#" <> definitionAnchor def

foresightRules :: Rules (FilePath -> Action ModuleInfo)
foresightRules = do
  scan <- newCache \fp -> do
    need [fp]
    let
      modn = moduleName (dropExtensions (dropDirectory1 fp)) <.> "html"
      writeDiagram contents = do
        let digest = showDigest . sha1 . LazyBS.fromStrict $ Text.encodeUtf8 contents
        writeFile ("_build/diagrams" </> digest <.> "part") $ Text.unpack contents
        pure digest

    traced "scanning" do
      scan <- scanModule modn fp
      digests <- traverse writeDiagram (Set.toList (scan ^. modDiagrams))
      let
        svgs = do
          d <- digests
          [ "_build/html/light-" <> Text.pack d <> ".svg"
            , "_build/html/dark-" <> Text.pack d <> ".svg"
            ]
        out = scan & modDiagrams .~ Set.fromList svgs
      () <- evaluate (rnf out)
      pure out

  _ <- addOracle \GlossaryQ -> do
    md   <- fmap ("src" </>) <$> getDirectoryFiles "src" ["**/*.lagda.md"]
    need md
    outs <- forP md scan

    let
      alldefs :: [(Mangled, Definition)]
      alldefs = outs >>= (Map.toList . view modDefns)

    pure $ foldr (uncurry (addDefinition getEntries)) (Glossary mempty) alldefs

  _ <- addOracle \(LinkTargetQ target) -> do
    glo <- view getEntries <$> askOracle GlossaryQ
    case Map.lookup (mangleLink target) glo of
      Just def -> pure $ definitionTarget def
      Nothing  -> error $
        "Unknown wiki-link target: " ++ Text.unpack target

  -- Debugging target to print all the wikilink targets:
  phony "glossary" do
    let
      get = sortOn (Down . length . snd)
          . map (\case { xs@((_, d):_) -> (definitionModule d, xs) ; _ -> __IMPOSSIBLE__ })
          . groupBy ((==) `on` definitionModule . snd)
          . sortOn (definitionModule . snd)
          . map (first getMangled)
          . Map.toList . view getEntries

      bykey =
          groupBy ((==) `on` definitionAnchor . snd)
        . sortOn (definitionAnchor . snd)

      aliases [(k, d)] = "  #" <> definitionAnchor d <> ": " <> k
      aliases g@((_, d):_) =
        "  #" <> definitionAnchor d <> ":\n    "
        <> Text.intercalate ", " (map fst g)
      aliases _ = __IMPOSSIBLE__

    entries <- get <$> askOracle GlossaryQ
    liftIO $ for_ entries $ \(mod, defs) -> do
      Text.putStr $ Text.pack (dropExtension mod) <> ":\n"
        <> Text.unlines (aliases <$> bykey defs)

  pure scan

data WikiLink = WikiLink
  { wikiLinkDest     :: Text
  , wikiLinkContents :: [Inline]
  , wikiLinkAttrs    :: Attr
  }
  deriving Show

instance Eq WikiLink where
  (==) = (==) `on` wikiLinkDest

instance Hashable WikiLink where
  hashWithSalt s = hashWithSalt s . wikiLinkDest

isWikiLink :: Inline -> Maybe WikiLink
isWikiLink (Link attr contents (url, title))
  | "wikilink" == title = pure $ WikiLink url contents attr
isWikiLink _ = Nothing

getWikiLinkUrl :: Text -> Action Text
getWikiLinkUrl = askOracle . LinkTargetQ

getWikiLink :: WikiLink -> Action Inline
getWikiLink (WikiLink dest contents attr) = do
  url <- getWikiLinkUrl dest
  pure $ Link attr contents (url, "")
