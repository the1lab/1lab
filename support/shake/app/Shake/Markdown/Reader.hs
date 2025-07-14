{-# LANGUAGE BlockArguments, OverloadedStrings, LambdaCase #-}
module Shake.Markdown.Reader (markdownReader, readLabMarkdown) where

import Control.Monad.IO.Class
import Control.Monad

import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy as Lazy
import qualified Data.Sequence as Seq
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.Text.Lazy.Builder (Builder)
import Data.Sequence (Seq)
import Data.Foldable
import Data.Maybe
import Data.Char
import Data.Text (Text)

import Development.Shake

import GHC.Compact

import Text.Pandoc.Shared
import Text.Pandoc.Walk
import Text.Pandoc hiding (trace)
import Debug.Trace (traceShow, trace)

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
postParseInlines (Math ty mtext:s@(Str txt):xs)
  | not (Text.isPrefixOf " " txt)
  =
    let
      glue   = "\\mathopen{\\nobreak}\\textnormal{" <> txt <> "}"
      mtext' = Text.stripEnd mtext <> glue
    in postParseInlines (Math ty mtext':xs)

-- Parse the contents of wikilinks as markdown. While Pandoc doesn't
-- read the title part of a wikilink, it will always consist of a single
-- Str span. We call the Pandoc parser in a pure context to read the
-- title part as an actual list of inlines.
postParseInlines (Link attr [Str contents] (url, "wikilink"):xs) =
  link' `seq` link':postParseInlines xs where

  try  = either (const Nothing) Just . runPure
  fail = error $
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
    pure (Link attr is (target, "wikilink"))

postParseInlines (x:xs) = x:postParseInlines xs
postParseInlines [] = []

data Posn = Posn { pLine :: {-# UNPACK #-} !Int, pCol :: {-# UNPACK #-} !Int }
  deriving (Show)

startPosn :: Posn
startPosn = Posn 1 1

advance :: Char -> Posn -> Posn
advance c (Posn line col) = case c of
  '\n' -> Posn (line + 1) 1
  '\t' -> Posn line (col + 8)
  c    -> Posn line (col + 1)

cols :: Int -> Posn -> Posn
cols n (Posn line col) = Posn line (n + col)

nl :: Posn -> Posn
nl = advance '\n'

type Message = [(Posn, String)]
type State = Posn -> String -> (Seq Message, Builder)

(<:) :: Char -> (a, Builder) -> (a, Builder)
c <: (m, cs) = (m,) $! Builder.singleton c <> cs

(<+) :: String -> (a, Builder) -> (a, Builder)
s <+ (m, cs) = (m,) $! Builder.fromString s <> cs

msg :: Monoid a => Posn -> String -> (Seq Message, a) -> (Seq Message, a)
msg pn s (msg, x) = (msg Seq.|> [(pn, s)], x)

msgs :: Monoid a => [(Posn, String)] -> (Seq Message, a) -> (Seq Message, a)
msgs msgs (msg, x) = (msg Seq.|> msgs, x)

-- | Pandoc's wiki-link extension does not support splitting the guts of
-- a wikilink over multiple lines.
--
-- The function 'mangleMarkdown' pre-processes the input file so that
-- any invalid space characters inside a wikilink are replaced by the
-- safe ASCII space @ @.
--
-- It also performs some early validation.
mangleMarkdown :: FilePath -> String -> Text
mangleMarkdown filename = finish . startfile startPosn where

  finish :: (Seq Message, Builder) -> Text
  finish (msgs, b)
    | null (fold msgs) = Lazy.toStrict $ Builder.toLazyText b
    | otherwise = error $ Text.unpack $ Text.stripEnd $ Text.unlines $ map Text.unlines $ map (map k) $ toList msgs
      where k (Posn line col, s) = Text.pack (filename <> ":" <> show line <> ":" <> show col <> ": " <> s)

  startfile :: State
  startfile !pn ('-':'-':'-':cs) = "---" <+ startcodeblock "metadata block" '-' pn 3 (cols 3 pn) cs
  startfile !pn cs0              = content True pn cs0

  content :: Bool -> State
  content bol !pn = \case
    ('[':'[':cs)         -> "[[" <+ wikilink pn body (cols 2 pn) cs
    ('^':'[':cs)         -> "^[" <+ footnote pn body (cols 2 pn) cs
    ('[':cs)             -> '['  <: link pn body (cols 1 pn) cs

    ('~':'~':'~':cs) | bol ->  "~~~" <+ startcodeblock "code block" '~' pn 3 (cols 3 pn) cs
    ('`':'`':'`':cs) | bol ->  "```" <+ startcodeblock "code block" '`' pn 3 (cols 3 pn) cs

    ('<':'!':'-':'-':cs) -> startcomment pn (cols 4 pn) cs

    ('<':'!':'-':cs)  -> msg pn "stray <!-" $ body (cols 3 pn) cs
    ('-':'-':'>':cs)  -> msg pn "stray -->" $ body (cols 3 pn) cs
    ('-':'>':cs)      -> msg pn "stray ->"  $ body (cols 2 pn) cs

    ('\n':cs) -> newline' (if bol then 1 else 0) pn ('\n':cs)
    (c:cs)
      | isSpace c -> c <: content bol (advance c pn) cs
      | otherwise -> c <: body (advance c pn) cs

    [] -> mempty

  body :: State
  body = content False

  newline' :: Int -> State
  newline' !d !pn ('\n':cs) = '\n' <: newline' (d + 1) (nl pn) cs
  newline' !d !pn (c:cs)    = content (d > 1) pn (c:cs)
  newline' !d !pn []        = mempty

  newline :: State
  newline = newline' 0

  startend :: String -> Posn -> Posn -> (Seq Message, Builder) -> (Seq Message, Builder)
  startend thing start end = msgs
    [ (end,   thing)
    , (start, "  ... opened here")
    ]

  startcodeblock :: String -> Char -> Posn -> Int -> State
  startcodeblock desc delim !start !fence !pn = \case
    c:cs | c == delim -> c <: startcodeblock desc delim start (fence + 1) (cols 1 pn) cs
    cs0 ->
      let
        loop !pn ('\n':cs) = codeblock desc delim start fence pn ('\n':cs)
        loop !pn (c:cs)    = c <: loop (advance c pn) cs
        loop !pn []        = startend ("unterminated " <> desc) start pn mempty
      in loop pn cs0

  codeblock :: String -> Char -> Posn -> Int -> State
  codeblock desc delim !start !fence !pn cs0 =
    let
      bol :: State
      bol !pn (c:cs)
        | isSpace c  = c <: bol (advance c pn) cs
        | c == delim = c <: leave (fence - 1) (cols 1 pn) cs
        | otherwise  = c <: codeblock desc delim start fence (advance c pn) cs
      bol !pn [] = startend ("unterminated " <> desc) start pn mempty

      leave :: Int -> State
      leave !0 !pn ('\n':cs) = newline pn ('\n':cs)
      leave !0 !pn (c:cs)    = msg pn "junk after code block terminator" $ body pn (c:cs)

      leave !n !pn (c:cs)
        | c == delim = c <: leave (n - 1) (cols 1 pn) cs
        | otherwise  = codeblock desc delim start fence pn (c:cs)

    in case cs0 of
      '\n':cs -> '\n' <: bol (nl pn) cs
      c:cs    -> c <: codeblock desc delim start fence (advance c pn) cs
      []      -> startend ("unterminated " <> desc) start pn mempty

  startcomment :: Posn -> State
  startcomment !start !pn = \case
    []                       -> startend "unterminated comment" start pn mempty
    ('[':'T':'O':'D':'O':cs) -> comment start False leavecomment pn cs

    (c:cs)
      | isSpace c -> startcomment start (advance c pn) cs
      | otherwise -> "<div class=\"commented-out\">\n" <+ comment start True leavecomment pn (c:cs)

  leavecomment :: State
  leavecomment !pn cs = "</div>" <+ body pn cs

  comment :: Posn -> Bool -> State -> State
  comment !start content k !pn cs0 = case cs0 of
    [] -> startend "unterminated comment" start pn mempty

    ('-':'-':'>':cs)     -> k (cols 3 pn) cs
    ('<':'!':'-':'-':cs) -> comment pn content (comment start content k) (cols 4 pn) cs

    ('[':'[':cs) | content -> "[[" <+ wikilink pn (comment start True k) (cols 2 pn) cs
    ('^':'[':cs) | content -> "^[" <+ footnote pn (comment start True k) (cols 2 pn) cs
    ('[':cs)     | content -> '['  <: link pn (comment start True k) (cols 1 pn) cs
    (c:cs)
      | content   -> c <: comment start content k (advance c pn) cs
      | otherwise -> comment start content k (advance c pn) cs

  noparbreak :: Char -> String -> Posn -> State -> State
  noparbreak ch thing start cont !pn = (ch <:) . loop False (nl pn) where
    loop failed !pn ('\n':cs) = ch <: loop True (nl pn) cs
    loop failed !pn (c:cs)
      | failed    = startend ("illegal paragraph break inside " <> thing) start pn $ content True pn (c:cs)
      | otherwise = cont pn (c:cs)
    loop failed !pn [] = startend ("unterminated " <> thing) start pn mempty

  wikilink :: Posn -> State -> State
  wikilink !start k !pn = \case
    ('\n':cs)     -> noparbreak ' ' "wikilink" start (wikilink start k) pn cs

    (']':']':cs)  -> "]]" <+ k (cols 2 pn) cs

    ('[':'[':cs)  -> "[[" <+ wikilink pn (wikilink start k) (cols 1 pn) cs
    ('[':cs)      -> '['  <: link pn (wikilink start k) (cols 1 pn) cs

    (c:cs)
      | isSpace c -> ' ' <: wikilink start k (advance c pn) cs
      | otherwise -> c   <: wikilink start k (advance c pn) cs
    []            -> msg start "unterminated wikilink" mempty

  link' :: Bool -> Posn -> State -> State
  link' footnote !start k !pn cs0 = case cs0 of
    ('\n':cs) -> noparbreak '\n' (if footnote then "footnote" else "link") start (link' footnote start k) pn cs

    (']':cs)     -> ']' <: k (cols 1 pn) cs

    ('[':'[':cs) -> "[[" <+ wikilink pn (link' footnote start k) (cols 1 pn) cs
    ('[':cs)     -> '['  <: link pn (link' footnote start k) (cols 1 pn) cs

    (c:cs)    -> c <: link' footnote start k (advance c pn) cs

    []        -> msg start "unterminated wikilink" mempty

  link, footnote :: Posn -> State -> State
  link     = link' False
  footnote = link' True

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
  cont = do
    contents <- mangleMarkdown fp <$> readFile fp
    doc <- either (fail . show) compactWithSharing =<< runIO do
      doc <- readMarkdown labReaderOptions [(fp, contents)]
      pure $ walk unParaMath $ walk postParseInlines doc
    pure $! getCompact doc

markdownReader :: Rules (FilePath -> Action Pandoc)
markdownReader = newCache \fp -> do
  need [fp]
  traced "pandoc" $ readLabMarkdown fp
