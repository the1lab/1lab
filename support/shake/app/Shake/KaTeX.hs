{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | Shake rules to compile equations to HTML with KaTeX
module Shake.KaTeX
  ( katexRules
  , getDisplayMath
  , getInlineMath
  ) where

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Generics

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

newtype LatexEquation = LatexEquation (Bool, Text)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult LatexEquation = Text

-- | Convert a display/block-level LaTeX equation to HTML.
getDisplayMath :: Text -> Action Text
getDisplayMath contents = askOracle (LatexEquation (True, contents))

-- | Convert an inline LaTeX equation to HTML.
getInlineMath :: Text -> Action Text
getInlineMath contents = askOracle (LatexEquation (False, contents))

-- | Shake rules required for compiling KaTeX equations.
katexRules :: Rules ()
katexRules = versioned 1 do
  _ <- addOracleCache \(LatexEquation (display, tex)) -> do
    need [".macros"]

    let args = ["-f", ".macros", "-t"] ++ ["-d" | display]
        stdin = LazyBS.fromStrict $ Text.encodeUtf8 tex
    Stdout out <- command [StdinBS stdin] "node" ("node_modules/.bin/katex":args)
    pure . Text.stripEnd . Text.decodeUtf8 $ out

  pure ()
