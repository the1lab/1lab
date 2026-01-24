{-# LANGUAGE BlockArguments, OverloadedStrings, FlexibleContexts, ViewPatterns, LambdaCase #-}

{-| Convert a markdown file to templated HTML, applying several
post-processing steps and rendered to HTML using the
@support/web/template.html@ template.
-}
module Shake.Markdown (buildMarkdown) where

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative

import qualified Data.Sequence as Seq
import qualified Data.Map.Lazy as Map
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import qualified Data.Set as Set

import Data.List (intersperse)
import Data.Foldable
import Data.Monoid (Ap(..))
import Data.Aeson (encodeFile)
import Data.Maybe
import Data.Text (Text)

import qualified System.Directory as Dir

import Development.Shake.FilePath
import Development.Shake

import qualified Citeproc as Cite
import Text.DocTemplates
import Text.HTML.TagSoup

import Text.Pandoc.Builder (Inlines)
import Text.Pandoc.Citeproc
import Text.Pandoc.Shared
import Text.Collate.Lang (Lang (..))
import Text.Pandoc.Walk
import Text.Pandoc

import Shake.Markdown.Reader
import Shake.LinkReferences
import Shake.SearchData
import Shake.Highlights
import Shake.Diagram (diagramHeight)
import Shake.Options
import Shake.Recent (recentAdditions, renderCommit)
import Shake.Digest
import Shake.KaTeX
import Shake.Git

import Definitions

buildMarkdown
  :: Action (Context Text)
  -> String   -- ^ The name of the Agda module.
  -> FilePath -- ^ Input markdown file, produced by the Agda compiler.
  -> FilePath -- ^ Output HTML file.
  -> Action ()
buildMarkdown digest modname input output = do
  gitCommit <- gitCommit
  skipAgda <- getSkipAgda
  digest <- digest

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

  let
    refMap = Map.fromList $ map (\x -> (Cite.unItemId . Cite.referenceId $ x, x)) references
    (display, inline) = flip query markdown \case
      Math DisplayMath contents -> (Seq.singleton contents, mempty)
      Math InlineMath contents -> (mempty, Seq.singleton contents)
      _ -> mempty

    diagrams = flip query markdown \case
      CodeBlock (_id, classes, _attrs) contents | "quiver" `elem` classes ->
        let digest = shortDigest contents in
        [ "_build/html/" </> modname </> digest <.> "light.svg"
        , "_build/html/" </> modname </> digest <.> "dark.svg"
        ]
      _ -> []

  need diagrams
  prerenderMaths (toList display) (toList inline)

  Pandoc meta@(Meta metamap) blocks <-
      walkM (patchInline refMap)
    . (if skipAgda then id else linkReferences modname)
    $ markdown

  need [ if isJust (Map.lookup "talk" metamap) then talkTemplateName else pageTemplateName ]

  -- Rendering the search data has to be done *here*, after running the
  -- maths through KaTeX but before adding the emoji to headers.
  let search = query (getHeaders (Text.pack modname)) markdown
  traced "writing" do
    encodeFile ("_build/search" </> modname <.> "json") search

  baseUrl <- getBaseUrl

  filtered <- parallel $ map (runWriterT . walkM (patchBlock baseUrl modname)) blocks
  let (bs, mss)                     = unzip filtered
      MarkdownState references defs = fold mss
      markdown                      = Pandoc meta bs

  text <- quietly $ traced "initial render" $ either (fail . show) pure =<<
    runIO (renderMarkdown authors references modname baseUrl digest markdown)

  let tags = foldEquations False (parseTags text)
  tags <- renderHighlights tags

  traced "writing" do
    Dir.createDirectoryIfMissing False "_build/html/fragments"
    Dir.createDirectoryIfMissing False "_build/search"

    Text.writeFile output $ renderHTML5 tags

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
  , _mdDefinitions :: Map.Map Mangled [Block]
    -- ^ List of definition blocks
  }

instance Semigroup MarkdownState where
  MarkdownState a b <> MarkdownState a' b' = MarkdownState (a <> a') (b <> b')

instance Monoid MarkdownState where
  mempty = MarkdownState mempty mempty

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
    digest = shortDigest contents
    title = fromMaybe "commutative diagram" (lookup "title" attrs)

    lfn = mod </> digest <.> "light.svg"
    dfn = mod </> digest <.> "dark.svg"

  height <- lift $ diagramHeight ("_build/html" </> lfn)

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

patchBlock _ _ b@(Div (id, clz, _kv) bs) | "definition" `elem` clz, not (Text.null id) = do
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
    pack = Span mempty . pure . Str

    authors' :: [Inline]
    authors' = case authors of
      []  -> [Str "Nobody"]
      [x] -> [Str x]
      _   -> intersperse Space (map (pack . (<> ",")) (init authors))
        <> [Space, Str "and", Space, pack (last authors <> ".")]

    authors'' = either (error . show) id . runPure . writeHtml5String def $ Pandoc mempty [Plain authors']

    context = Context $ Map.fromList
      [ ("is-index",     toVal (modname == "index"))
      , ("authors",      toVal authors'')
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
getHeaders module' markdown =
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
  go (Div (hId, _, keys) _:xs) | hId /= "" = do
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

-- | Write a HTML file, correctly handling the closing of some tags.
renderHTML5 :: [Tag Text] -> Text
renderHTML5 = renderTagsOptions renderOptions{ optMinimize = min } where
  min = flip elem ["br", "meta", "link", "img", "hr"]
