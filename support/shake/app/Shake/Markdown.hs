{-# LANGUAGE BlockArguments, OverloadedStrings, FlexibleContexts, ViewPatterns, LambdaCase #-}
{-# LANGUAGE DerivingStrategies, UnboxedTuples, MagicHash #-}

{-| Convert a markdown file to templated HTML, applying several
post-processing steps and rendered to HTML using the
@support/web/template.html@ template.
-}
module Shake.Markdown (buildMarkdown, readLabMarkdown) where

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Control.Monad

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Map.Lazy as Map
import qualified Data.Sequence as Seq
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.Digest.Pure.SHA
import Data.Foldable
import Data.Monoid (Ap(..))
import Data.Aeson (encodeFile)
import Data.Maybe
import Data.Text (Text)
import Data.Char

import qualified System.Directory as Dir

import Development.Shake.FilePath
import Development.Shake

import GHC.Exts (Int(I#), Int#, (+#))

import qualified Citeproc as Cite
import Text.DocTemplates
import Text.HTML.TagSoup
import Text.HTML.TagSoup.Match
import Text.HTML.TagSoup.Tree

import Text.Pandoc.Builder (Inlines)
import Text.Pandoc.Citeproc
import Text.Pandoc.Shared
import Text.Collate.Lang (Lang (..))
import Text.Pandoc.Walk
import Text.Pandoc

import Shake.LinkReferences
import Shake.SearchData
import Shake.Highlights
import Shake.Diagram (diagramHeight)
import Shake.Options
import Shake.Recent (recentAdditions, renderCommit)
import Shake.Digest
import Shake.KaTeX
import Shake.Git

import HTML.Emit

import Definitions

import System.IO.Unsafe
import Text.Show.Pretty (ppShow)

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
    contents <- mangleMarkdown <$> Text.readFile fp
    either (fail . show) pure =<< runIO do
      doc <- readMarkdown labReaderOptions [(fp, contents)]
      pure $ walk unParaMath $ walk postParseInlines doc

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

type Posn    = (# Int#, Int# #)
type Mangler = Posn -> String -> String

-- | Pandoc's wiki-link extension does not support splitting the guts of
-- a wikilink over multiple lines. The function 'mangleMarkdown'
-- pre-processes the input file so that any invalid space characters
-- inside a wikilink are replaced by the safe ASCII space @ @.
mangleMarkdown :: Text -> Text
mangleMarkdown = Text.pack . toplevel (# 1#, 1# #) . Text.unpack where
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

buildMarkdown :: String   -- ^ The name of the Agda module.
              -> FilePath -- ^ Input markdown file, produced by the Agda compiler.
              -> FilePath -- ^ Output HTML file.
              -> Action ()
buildMarkdown modname input output = do
  gitCommit <- gitCommit
  skipAgda <- getSkipAgda

  need [bibliographyName, input]

  modulePath <- findModule modname
  authors <- gitAuthors modulePath
  let
    permalink = gitCommit </> modulePath

    title
      | length modname > 24 = '…':reverse (take 24 (reverse modname))
      | otherwise = modname

    mStr = MetaString . Text.pack
    patchMeta
      = Meta
      . Map.insert "title" (mStr title)
      . Map.insert "source" (mStr permalink)
      . Map.insert "module" (mStr modname)
      . Map.insert "bibliography" (mStr bibliographyName)
      . Map.insert "link-citations" (MetaBool True)
      . unMeta

  (markdown, references) <- traced "pandoc" do
    Pandoc meta markdown <- readLabMarkdown input
    let pandoc = addPageTitle (Pandoc (patchMeta meta) markdown)
    either (fail . show) pure =<< runIO do
      (,) <$> processCitations pandoc <*> getReferences Nothing pandoc

  liftIO $ Dir.createDirectoryIfMissing True $ "_build/diagrams" </> modname

  let
    refMap = Map.fromList $ map (\x -> (Cite.unItemId . Cite.referenceId $ x, x)) references
    (display, inline) = flip query markdown \case
      Math DisplayMath contents -> (Seq.singleton contents, mempty)
      Math InlineMath contents -> (mempty, Seq.singleton contents)
      _ -> mempty

  prerenderMaths (toList display) (toList inline)

  Pandoc meta@(Meta metamap) blocks <-
      walkM (patchInline refMap)
    . (if skipAgda then id else linkReferences modname)
    $ markdown

  need [ if isJust (Map.lookup "talk" metamap) then talkTemplateName else pageTemplateName ]

  -- Rendering the search data has to be done *here*, after running the
  -- maths through KaTeX but before adding the emoji to headers.
  let search = query (getHeaders (Text.pack modname)) markdown

  baseUrl <- getBaseUrl

  filtered <- parallel $ map (runWriterT . walkM (patchBlock baseUrl modname)) blocks
  let (bs, mss)                     = unzip filtered
      MarkdownState references defs = fold mss
      markdown                      = Pandoc meta bs

  digest <- do
    cssDigest     <- getFileDigest "_build/html/css/default.css"
    startJsDigest <- getFileDigest "_build/html/start.js"
    mainJsDigest  <- getFileDigest "_build/html/main.js"
    pure . Context . Map.fromList $
      [ ("css",       toVal (Text.pack cssDigest))
      , ("start-js",  toVal (Text.pack startJsDigest))
      , ("main-js",   toVal (Text.pack mainJsDigest))
      ]

  text <- liftIO $ either (fail . show) pure =<<
    runIO (renderMarkdown authors references modname baseUrl digest markdown)

  let tags = foldEquations False (parseTags text)
  tags <- renderHighlights tags
  traverse_ (checkMarkup input) tags

  traced "writing" do
    Dir.createDirectoryIfMissing False "_build/html/fragments"
    Dir.createDirectoryIfMissing False "_build/search"

    Text.writeFile output $ renderHTML5 tags

  traced "search" do
    encodeFile ("_build/search" </> modname <.> "json") search

  for_ (Map.toList defs) \(key, bs) -> traced "writing fragment" do
    text <- either (fail . show) pure =<<
      runIO (renderMarkdown authors references modname baseUrl digest (Pandoc mempty bs))

    Text.writeFile ("_build/html/fragments" </> Text.unpack (getMangled key) <.> "html") text

-- | Find the original Agda file from a 1Lab module name.
findModule :: MonadIO m => String -> m FilePath
findModule modname = do
  let toPath '.' = '/'
      toPath c = c
  let modfile = "src" </> map toPath modname

  exists <- liftIO $ Dir.doesFileExist (modfile <.> "lagda.md")
  pure $ if exists
    then modfile <.> "lagda.md"
    else modfile <.> "agda"

-- | Adds the first level-1 header as a page title, if one has not
-- already been provided by the author.
addPageTitle :: Pandoc -> Pandoc
addPageTitle (Pandoc (Meta meta) m) = Pandoc (Meta meta') m where
  search (Header 1 _ inl:_) = Just (MetaInlines inl)
  search (_:xs)             = search xs
  search []                 = Nothing

  meta' = case Map.lookup "pagetitle" meta <|> Map.lookup "customtitle" meta <|> search m of
    Just m  -> Map.insert "pagetitle" m meta
    Nothing -> meta

isAgdaBlock :: TagTree Text -> Bool
isAgdaBlock (TagBranch _ attrs _) = anyAttrLit ("class", "Agda") attrs
isAgdaBlock _ = False

-- | Rewrite a single inline element.
patchInline
  :: Map.Map Text (Cite.Reference Inlines)
  -- ^ A lookup of reference names to the actual reference.
  -> Inline
  -> Action Inline
-- Pre-render latex equations.
patchInline _ (Math DisplayMath contents) = htmlInl <$> getDisplayMath contents
patchInline _ (Math InlineMath contents) = htmlInl <$> getInlineMath contents

patchInline _ l@Link{} | Just wikil <- isWikiLink l = getWikiLink wikil

-- Add the title to reference links.
patchInline refMap (Link attrs contents (target, ""))
  | Just citation <- Text.stripPrefix "#ref-" target
  , Just ref      <- Map.lookup citation refMap
  , Just title    <- Cite.valToText =<< Cite.lookupVariable "title" ref
  = pure $ Link attrs contents (target, title)

patchInline _ (Str s)
  | "[" `Text.isPrefixOf` s
  , s /= "[", s /= "[…]" -- "[" appears on its own before citations
  = error ("possible broken link: " <> Text.unpack s)

patchInline _ h = pure h

data MarkdownState = MarkdownState
  { mdReferences  :: [Val Text]
    -- ^ List of references extracted from Pandoc's "reference" div.
  , mdDefinitions :: Map.Map Mangled [Block]
    -- ^ List of definition blocks
  }

instance Semigroup MarkdownState where
  MarkdownState a b <> MarkdownState a' b' = MarkdownState (a <> a') (b <> b')

instance Monoid MarkdownState where
  mempty = MarkdownState mempty mempty

diagramResource :: Resource
diagramResource = unsafePerformIO $ newResourceIO "diagram" 1
{-# NOINLINE diagramResource #-}

-- | Patch a Pandoc block element.
patchBlock
  :: (MonadIO f, MonadFail f, MonadWriter MarkdownState f, MonadTrans t, f ~ t Action)
  => String
  -> String
  -> Block
  -> f Block
-- Make all headers links, and add an anchor emoji.
patchBlock _ _ (Header i a@(ident, _, _) inl) = pure $ Header i a
  $ htmlInl (Text.concat ["<a href=\"#", ident, "\" class=\"header-link\"><span>"])
  : inl
  ++ [htmlInl "</span><span class=\"header-link-emoji\">🔗</span></a>"]

-- Replace quiver code blocks with a link to an SVG file, and depend on the SVG file.
patchBlock _ mod (CodeBlock (id, classes, attrs) contents) | "quiver" `elem` classes = do
  let
    digest = take 12 . showDigest . sha1 . LazyBS.fromStrict $ Text.encodeUtf8 contents
    title = fromMaybe "commutative diagram" (lookup "title" attrs)

    lfn = mod </> digest <.> "light.svg"
    dfn = mod </> digest <.> "dark.svg"

  height <- lift do
    -- We have to lock the diagram directory to prevent race conditions
    -- between two Markdown tasks that are trying to write the same
    -- diagram.
    -- This isn't the best in terms of atomicity, but it does preserve
    -- the nice property that diagrams are globally shared by their
    -- contents.
    withResource diagramResource 1 $ liftIO do
      Text.writeFile ("_build/diagrams" </> mod </> digest <.> "tex") contents

    need [ "_build/html" </> lfn, "_build/html" </> dfn ]
    diagramHeight ("_build/html" </> lfn)

  let attrs' = ("style", "--height: " <> Text.pack (show height) <> "px;"):attrs

  pure $ Div ("", ["diagram-container"], [])
    [ Plain [ Image (id, "diagram diagram-light":classes, attrs') [] (Text.pack lfn, title) ]
    , Plain [ Image (id, "diagram diagram-dark":classes, attrs')  [] (Text.pack dfn, title) ]
    ]

patchBlock base _ (Div attr@("recent-additions", _, _) []) =
  Div attr . map (renderCommit base) <$> lift recentAdditions

-- Find the references block, parse the references, and remove it. We write
-- the references as part of our template instead.
patchBlock _ _ (Div ("refs", _, _) body) = do
  for_ body \ref -> case ref of
    (Div (id, _, _) body) -> do
      -- If our citation is a single paragraph, don't wrap it in <p>.
      let body' = case body of
            [Para p] -> [Plain p]
            body -> body
      -- Now render it the citation itself to HTML and add it to our template
      -- context.
      body <- either (fail . show) pure . runPure $
        writeHtml5String def { writerExtensions = getDefaultExtensions "html" } (Pandoc mempty body')
      let ref = Context $ Map.fromList
                [ ("id", toVal id)
                , ("body", toVal body)
                ]
      tell mempty { mdReferences = [ MapVal ref ]}

    _ -> fail ("Unknown reference node " ++ show ref)
  pure $ Plain [] -- TODO: pandoc-types 1.23 removed Null

patchBlock _ _ b@(Div (id, clz, kv) bs) | "definition" `elem` clz, not (Text.null id) = do
  let
    isfn (Note _) = True
    isfn _ = False
  b <$ tell (MarkdownState mempty (Map.singleton (mangleLink id) (walk (filter (not . isfn)) bs)))

patchBlock _ _ h = pure h

-- | Render our Pandoc document using the given template variables.
renderMarkdown
  :: PandocMonad m
  => [Text]       -- ^ List of authors
  -> [Val Text]   -- ^ List of references
  -> String       -- ^ Name of the current module
  -> String       -- ^ Base URL
  -> Context Text -- ^ Digests of the various files.
  -> Pandoc
  -> m Text
renderMarkdown authors references modname baseUrl digest markdown@(Pandoc (Meta meta) _) = do
  let
    isTalk = isJust $ Map.lookup "talk" meta

    templateName
      | isTalk         = Just talkTemplateName
      | mempty == meta = Nothing
      | otherwise      = Just pageTemplateName

    get nm = getTemplate nm
      >>= runWithPartials . compileTemplate nm
      >>= either (throwError . PandocTemplateError . Text.pack) pure

  template <- traverse get templateName

  let
    authors' = case authors of
      [] -> "Nobody"
      [x] -> x
      _ -> Text.intercalate ", " (init authors) `Text.append` " and " `Text.append` last authors

    context = Context $ Map.fromList
      [ ("is-index",     toVal (modname == "index"))
      , ("authors",      toVal authors')
      , ("reference",    toVal references)
      , ("base-url",     toVal (Text.pack baseUrl))
      , ("digest",       toVal digest)
      ]

    opts = def
      { writerTemplate        = template
      , writerTableOfContents = not isTalk
      , writerVariables       = context
      , writerExtensions      = getDefaultExtensions "html"
      , writerSlideLevel      = Just 2
      }

  setTranslations (Lang "en" Nothing Nothing [] [] [])
  if isTalk
    then writeRevealJs opts markdown
    else writeHtml5String opts markdown

-- | Simple textual list of starting identifiers not to fold
don'tFold :: Set.Set Text
don'tFold = Set.fromList
  [ "`⟨" -- used for STLC
  , "‶⟨" -- used in Cat.Diagram.Product.Solver
  ]

-- | Removes the RHS of equation reasoning steps?? IDK, ask Amelia.
foldEquations :: Bool -> [Tag Text] -> [Tag Text]
foldEquations _ (to@(TagOpen "a" attrs):tt@(TagText t):tc@(TagClose "a"):rest)
  | xs@(_:_) <- Text.splitOn "." t, let t = last xs, t `Set.notMember` don'tFold
  , Text.length t > 1
  , Text.last t == '⟨'
  , Just href <- lookup "href" attrs =
  [ TagOpen "span" [("class", "reasoning-step")]
  , TagOpen "span" [("class", "as-written " <> fromMaybe "" (lookup "class" attrs))]
  , to, tt, tc ] ++ go href rest
  where
    alternate = Text.init t
    go href (to@(TagOpen "a" attrs):tt@(TagText t):tc@(TagClose "a"):cs)
      | Text.length t >= 1
      , Text.head t == '⟩'
      , Just href' <- lookup "href" attrs
      , href' == href
      = [ to, tt, tc, TagClose "span"
      , TagOpen "span" [("class", "alternate " <> fromMaybe "" (lookup "class" attrs))]
      , TagText alternate
      , TagClose "span"
      , TagClose "span"
      ] ++ foldEquations True cs
    go href (c:cs) = c:go href cs
    go _ [] = []
foldEquations False (TagClose "html":cs) =
  [TagOpen "style" [], TagText ".equations { display: none !important; }", TagClose "style", TagClose "html"]
  ++ foldEquations True cs
foldEquations has_eqn (c:cs) = c:foldEquations has_eqn cs
foldEquations _ [] = []

-- | Get all headers in the document, building a list of definitions for our
-- search index.
getHeaders :: Text -> Pandoc -> [SearchTerm]
getHeaders module' markdown@(Pandoc (Meta meta) _) =
  (:) main . flip evalState [] . getAp . query (Ap . go) $ markdown
  where
  main = SearchTerm
    { idIdent = module'
    , idAnchor = module' <> ".html"
    , idType = Nothing
    , idDefines = Nothing
    }

  hasRaw :: [Inline] -> Bool
  hasRaw = any \case
    RawInline{} -> True
    _ -> False

  -- The state stores a path of headers in the document of the form (level,
  -- header), which is updated as we walk down the document.
  go :: [Block] -> State [(Int, Text)] [SearchTerm]
  go [] = pure []
  go (Header level (hId, _, keys) hText:xs) | not (hasRaw hText) = do
    path <- get
    let title = trimr (renderPlain hText)
    let path' = (level, title):dropWhile (\(l, _) -> l >= level) path
    put path'

    if hId == "" then go xs
    else
      (:) SearchTerm
        { idIdent  = Text.intercalate " > " . reverse $ map snd path'
        , idAnchor = module' <> ".html#" <> hId
        , idType   = Nothing
        , idDefines = Text.words <$> lookup "defines" keys
        } <$> go xs
  go (Div (hId, _, keys) blocks:xs) | hId /= "" = do
    path <- get

    (:) SearchTerm
      { idIdent  = Text.intercalate " > " . reverse $ hId:map snd path
      , idAnchor = module' <> ".html#" <> hId
      , idType   = Nothing
      , idDefines = (:) hId . Text.words <$> lookup "alias" keys
      } <$> go xs
  go (_:xs) = go xs

  -- writePlain won't render *markdown*, e.g. links, but it *will*
  -- preserve raw HTML - as long as we tell it to. Since any mathematics
  -- in the description will have been rendered to raw HTML by this
  -- point, that's exactly what we want!
  write = writePlain def{ writerExtensions = enableExtension Ext_raw_html (writerExtensions def) }
  renderPlain inlines = either (error . show) id . runPure . write $ Pandoc mempty [Plain inlines]

htmlInl :: Text -> Inline
htmlInl = RawInline "html"

pageTemplateName, talkTemplateName, bibliographyName :: FilePath
pageTemplateName = "support/web/template.html"
talkTemplateName = "support/web/template.reveal.html"
bibliographyName = "src/bibliography.bibtex"
