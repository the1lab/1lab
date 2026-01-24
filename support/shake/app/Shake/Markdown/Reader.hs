{-# LANGUAGE BlockArguments, OverloadedStrings, LambdaCase #-}
{-# LANGUAGE DerivingStrategies, UnboxedTuples, MagicHash #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
module Shake.Markdown.Reader (markdownReader, readLabMarkdown) where

import Control.Monad.IO.Class
import Control.Exception
import Control.DeepSeq
import Control.Monad

import qualified Data.Text as Text
import Data.Maybe
import Data.Char
import Data.Text (Text)

import Development.Shake

import GHC.Exts (Int(I#), Int#, (+#))
import GHC.Compact

import Text.Pandoc.Shared
import Text.Pandoc.Walk
import Text.Pandoc hiding (trace)

labReaderOptions :: ReaderOptions
labReaderOptions =
  let
    good = [ Ext_wikilinks_title_before_pipe ]
    bad  = [Ext_definition_lists, Ext_compact_definition_lists]
    exts = foldr disableExtension
      (foldr enableExtension (getDefaultExtensions "markdown") good)
      bad
  in def { readerExtensions = exts }

readLabMarkdown :: MonadIO m => FilePath -> m Pandoc
readLabMarkdown fp = liftIO cont where
  unParaMath :: Block -> Block
  unParaMath (Para [Math DisplayMath m]) = Plain [Math DisplayMath m]
  unParaMath x = x

  cont :: IO Pandoc
  cont = {-# SCC "readLabMarkdown" #-} do
    contents <- mangleMarkdown <$> readFile fp
    evaluate $ rnf contents
    either (fail . show) pure =<< runIO do
      doc <- readMarkdown labReaderOptions [(fp, contents)]
      pure $ walk unParaMath $ walk postParseInlines doc
{-# NOINLINE readLabMarkdown #-}

-- | Patch a sequence of inline elements. `patchInline' should be preferred
-- where possible, this is only useful when you cannot modify inlines in
-- isolation.
postParseInlines :: [Inline] -> [Inline]

-- Float text that occurs directly after a mathematics span *inside* the
-- span. This allows the entire expression to reflow but preserves the
-- intended semantics of having e.g. `$n$-connected` be a single logical
-- unit (which should be line-wrapped together).
--
-- The text is attached naïvely, so if the entire expression is a single
-- group (i.e. something like `${foo}$`), it will probably not work.
-- However, the naïve solution does have the benefit of automatically
-- attaching the non-wrapping text to the last "horizontal unit" in the
-- span.
--
-- However, note that the glue between the original mathematics and the
-- attached text is treated as an opening delimiter. This is to have
-- correct spacing in case the maths ends with an operatorname, e.g. id.
postParseInlines (Math ty mtext:Str txt:xs)
  | not (Text.isPrefixOf " " txt)
  =
    let
      glue   = "\\mathopen{\\nobreak}\\textnormal{" <> txt <> "}"
      mtext' = Text.stripEnd mtext <> glue
    in postParseInlines (Math ty mtext':xs)

-- Parse the contents of wikilinks as markdown. Pandoc doesn't parse
-- inlines inside wikilinks, but it does do space splitting. We call the
-- Pandoc parser in a pure context to read the title part as an *actual*
-- list of inlines.
postParseInlines (Link attr@(_id, cls, _attrs) content (url, title):xs)
  | "wikilink" `elem` cls =
  link' `seq` link':postParseInlines xs where

  contents = flip query content \case
    Text.Pandoc.Str x -> x
    Text.Pandoc.Space -> " "
    inl               -> error $ "Unexpected inline in wikilink contents: " ++ show inl

  try      = either (const Nothing) Just . runPure
  fail     = error $
    "Failed to parse contents of wikilink as Markdown:" <> Text.unpack contents

  link' = fromMaybe fail do
    -- The contents of a link are valid if they consist of a single list
    -- of inlines. Pandoc doesn't let us parse a list of inlines, but we
    -- can still parse it as a document and ensure that (a) everything
    -- got bunched in the same paragraph and (b) there was no metadata.
    parsed@(Pandoc (Meta m) [Para is]) <- try (readMarkdown labReaderOptions contents)
    guard (null m) -- I don't foresee this ever failing.

    -- Rendering the contents as plain text will strip all the
    -- decorations, thus recovering the "underlying page" that was meant
    -- to be linked to. Of course, we should only try changing the
    -- target if the link looks like [[foo]], rather than [[foo|bar]].
    let
      target = if url == contents
        then stringify parsed
        else url

    -- Note that Pandoc doesn't distinguish between [[foo]] and
    -- [[foo|foo]], so really the only way is checking whether the URL
    -- is equal to the contents string. If that was the case, then
    -- stripping formatting is the right thing, otherwise e.g. [[*path
    -- induction*]] would fail since the target "*path-induction*"
    -- doesn't exist.
    pure (Link attr is (target, title))

postParseInlines (x:xs) = x:postParseInlines xs
postParseInlines [] = []

type Posn    = (# Int#, Int# #)
type Mangler = Posn -> String -> String

-- | Pandoc's wiki-link extension does not support splitting the guts of
-- a wikilink over multiple lines. The function 'mangleMarkdown'
-- pre-processes the input file so that any invalid space characters
-- inside a wikilink are replaced by the safe ASCII space @ @.
mangleMarkdown :: String -> Text
mangleMarkdown = Text.pack . toplevel (# 1#, 1# #) where
  adv :: Char -> Posn -> Posn
  adv '\n' (# l, c #) = (# l +# 1#, 1# #)
  adv _    (# l, c #) = (# l, c +# 1# #)

  eat :: Int -> Posn -> Posn
  eat (I# n) (# l, c #) = (# l, c +# n #)

  pos :: Posn -> String
  pos (# l , c #) = "line " ++ show (I# l) ++ ", column " ++ show (I# c)

  toplevel :: Mangler
  toplevel p ('$':cs)                 = '$':       entermaths p toplevel (eat 1 p) cs
  toplevel p ('`':'`':'`':cs)         = "```"   ++ code       p toplevel (eat 3 p) cs
  toplevel p ('<':'p':'r':'e':' ':cs) = "<pre " ++ pre        p toplevel (eat 5 p) cs

  toplevel p ('[':'[':cs)         = '[':'[':wikilink toplevel (eat 2 p) cs
  toplevel p ('<':'!':'-':'-':cs) = startcomment p (eat 4 p) cs
  toplevel p (c:cs)               = c:toplevel (adv c p) cs
  toplevel p []                   = []

  entermaths :: Posn -> Mangler -> Mangler
  entermaths p0 k p ('$':cs) = '$':maths p0 True k (eat 1 p) cs
  entermaths p0 k p cs       = maths p0 False k p cs

  maths :: Posn -> Bool -> Mangler -> Mangler
  maths p0 True  k p ('$':'$':cs) = '$':'$':k (eat 2 p) cs
  maths p0 False k p ('$':cs)     = '$':k (eat 1 p) cs
  maths p0 False k p ('\n':cs)    =
    let
      loop p ('\n':cs) = error $ "Paragraph break at " ++ pos p ++ " in inline maths started at " ++ pos p0
      loop p (c:cs)
        | isSpace c = c:loop (adv c p) cs
        | otherwise = c:maths p0 False k (adv c p) cs
      loop p [] = error $ "End-of-file encountered at " ++ pos p ++ " while reading inline maths started at " ++ pos p0
    in '\n':loop (adv '\n' p) cs

  maths p0 d k p (c:cs)       = c:maths p0 d k (adv c p) cs
  maths p0 d _ p []           = error $ "Unterminated " ++ (if d then "display " else "inline ") ++ "maths started at " ++ pos p0

  startcomment :: Posn -> Mangler
  startcomment p0 p ('[':'T':'O':'D':'O':cs) = comment p0 False 1 (eat 5 p) cs
  startcomment p0 p (c:cs)
    | isSpace c       = startcomment p0 (adv c p) cs
    | otherwise       = "<div class=\"commented-out\">\n" ++ comment p0 True 1 p (c:cs)
  startcomment p0 p []   = error $ "Unterminated comment started at " ++ pos p0

  code :: Posn -> Mangler -> Mangler
  code p0 k p ('`':'`':'`':cs) = "```" ++ k (eat 3 p) cs
  code p0 k p (c:cs)           = c:code p0 k (adv c p) cs
  code p0 k p []               = error $ "Unterminated code block started at " ++ pos p0

  pre :: Posn -> Mangler -> Mangler
  pre p0 k p ('<':'/':'p':'r':'e':'>':cs) = "</pre>" ++ k (eat 6 p) cs
  pre p0 k p (c:cs)                       = c:pre p0 k (adv c p) cs
  pre p0 k p []                           = error $ "Unterminated <pre> block started at " ++ pos p0

  comment :: Posn -> Bool -> Int -> Mangler
  comment p0 e 0 p cs = concat ["\n</div>" | e] ++ toplevel p cs
  comment p0 e n p [] = error $ "Unterminated comment started at " ++ pos p0

  comment p0 e n p ('-':'-':'>':cs)     = comment p0 e (n - 1) (eat 3 p) cs
  comment p0 e n p ('<':'!':'-':'-':cs) = comment p0 e (n + 1) (eat 4 p) cs

  comment p0 True n p ('<':'p':'r':'e':' ' :cs)
    = "<pre " ++ pre p (comment p0 True n) (eat 6 p) cs
  comment p0 True n p ('`':'`':'`':cs)     = "```" ++ code p (comment p0 True n) (eat 3 p) cs
  comment p0 True n p ('[':'[':cs)         = '[':'[':wikilink     (comment p0 True n) (eat 2 p) cs
  comment p0 True n p ('$':'$':cs)         = '$':'$':maths p True (comment p0 True n) (eat 2 p) cs
  comment p0 True n p ('$':c:cs)           = '$':maths p False    (comment p0 True n) p (c:cs)

  comment p0 e n p (c:cs)
    | e         = c:comment p0 e n (adv c p) cs
    | otherwise = comment p0 e n (adv c p) cs

  wikilink :: Mangler -> Mangler
  wikilink k p (']':']':cs) = ']':']':k (eat 2 p) cs

  wikilink k p ('\n':cs)    = ' ':wikilink k (adv '\n' p) cs
  wikilink k p ('\t':cs)    = ' ':wikilink k (adv '\t' p) cs
  wikilink k p ('\f':cs)    = ' ':wikilink k (adv '\f' p) cs
  wikilink k p ('\r':cs)    = ' ':wikilink k (adv '\r' p) cs

  wikilink k p (c:cs)       = c:wikilink k (adv c p) cs
  wikilink k p []           = []

markdownReader :: Rules (FilePath -> Action Pandoc)
markdownReader = newCache \fp -> do
  need [fp]
  traced "pandoc" $ do
    md <- compact =<< readLabMarkdown fp
    pure $! getCompact md
