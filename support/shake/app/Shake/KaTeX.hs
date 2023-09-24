{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies, DerivingStrategies #-}

-- | Shake rules to compile equations to HTML with KaTeX
module Shake.KaTeX
  ( katexRules

  , getParsedPreamble
  , getPreambleFor

  , PrecompiledTex
  , getPrecompiled
  , getInline
  , getDisplay
  ) where

import Control.Exception
import Control.DeepSeq
import Control.Monad
import Control.Lens hiding ((<.>))

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Map.Strict as Map
import qualified Data.Binary as Binary
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Generics
import Data.Foldable
import Data.Binary
import Data.Maybe

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake.FilePath
import Development.Shake

import GHC.Generics
import GHC.Compact

import Shake.Markdown.Foresight
import Shake.Utils
import Macros

newtype LatexPreamble = LatexPreamble Bool
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

newtype ParsedPreamble = ParsedPreamble ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult LatexPreamble = Text
type instance RuleResult ParsedPreamble = Preamble

-- | Get the preamble for a given build ('True' = dark mode)
getPreambleFor :: Bool -> Action Text
getPreambleFor = askOracle . LatexPreamble

-- | Get parsed preamble
getParsedPreamble :: Action Preamble
getParsedPreamble = askOracle $ ParsedPreamble ()

-- | Shake rules required for compiling KaTeX equations.
katexRules :: (String -> Action ModuleInfo) -> Rules ()
katexRules moduleScan = versioned 2 do
  _ <- addOracle \(ParsedPreamble _) -> do
    need ["src/preamble.tex"]
    t <- liftIO $ Text.readFile "src/preamble.tex"
    case parsePreamble t of
      Just p -> pure p
      Nothing -> error "Failed to parse preamble.tex!"

  _ <- addOracleCache \(LatexPreamble bool) -> do
    pre <- askOracle (ParsedPreamble ())
    let dark = if bool then darkSettings else mempty
    pure (preambleToLatex pre <> Text.pack "\n" <> dark)

  "_build/katex/*.bin" %> \out -> do
    let
      inp = "src"
        </> map (\c -> if c == '.' then '/' else c) (dropDirectory1 (dropDirectory1 (dropExtension out)))
        <.> "lagda.md"

    need [inp]
    mod <- moduleScan inp
    pre <- precompileTex (mod ^. modMathsInline) (mod ^. modMathsDisplay)
    liftIO $ Binary.encodeFile out pre

  pure ()

darkSettings :: Text
darkSettings = Text.pack "\\newcommand{\\labdark}{yes!}"

data PrecompiledTex = PrecompiledTex
  { precompiledDisplay :: Map Text Text
  , precompiledInlines :: Map Text Text
  }
  deriving (Eq, Show, Ord, GHC.Generics.Generic)

instance Binary PrecompiledTex
instance NFData PrecompiledTex

render :: Bool -> Text -> Action Text
render display tex = do
  pre <- askOracle (ParsedPreamble ())

  let args = ["-T"] ++ ["-d" | display]
      stdin = LazyBS.fromStrict $ Text.encodeUtf8 $ applyPreamble pre tex

  Stdout out <- nodeCommand [StdinBS stdin] "katex" args
  pure . Text.stripEnd . Text.decodeUtf8 $ out

mangleKey :: Text -> Text
mangleKey = Text.unwords . Text.lines

precompileTex :: Foldable f => f Text -> f Text -> Action PrecompiledTex
precompileTex inline display = do
  let inl  = toList inline
      disp = toList display

  display <- forP disp \t -> (mangleKey t,) <$> render True t
  inline <- forP inl \t -> (mangleKey t,) <$> render False t

  let it = PrecompiledTex (Map.fromList display) (Map.fromList inline)
  () <- liftIO (evaluate (rnf it))
  pure it

getPrecompiled :: String -> Action PrecompiledTex
getPrecompiled modn = do
  let path = "_build/katex/" <> modn <> ".bin"
  need [path]
  liftIO $ do
    it <- compactWithSharing =<< Binary.decodeFile path
    pure (getCompact it)

getInline :: PrecompiledTex -> Text -> Text
getInline (PrecompiledTex _ i) k = fromMaybe (impossibleTex k') $ Map.lookup k' i
  where k' = mangleKey k

getDisplay :: PrecompiledTex -> Text -> Text
getDisplay (PrecompiledTex d _) k = fromMaybe (impossibleTex k') $ Map.lookup k' d
  where k' = mangleKey k

impossibleTex k = error $ "Impossible: getting a maths span " ++ show k ++ " that wasn't pre-rendered for the module"
