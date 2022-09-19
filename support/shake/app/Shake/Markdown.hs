{-# LANGUAGE BlockArguments, OverloadedStrings, FlexibleContexts #-}

{-| Convert a markdown file to templated HTML, applying several
post-processing steps and rendered to HTML using the
@support/web/template.html@ template.
-}
module Shake.Markdown (buildMarkdown) where

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Writer
import Control.Monad.State

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Map.Lazy as Map
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import Data.Aeson (encodeFile)
import Data.Digest.Pure.SHA
import Data.Text (Text)
import Data.Foldable
import Data.List (intersperse)
import Data.Maybe

import qualified System.Directory as Dir

import Development.Shake.FilePath
import Development.Shake

import qualified Citeproc as Cite
import Text.DocTemplates
import Text.HTML.TagSoup

import Text.Collate.Lang (Lang (..))
import Text.Pandoc.Builder (Inlines)
import Text.Pandoc.Citeproc
import Text.Pandoc.Shared
import Text.Pandoc.Walk
import Text.Pandoc

import Shake.LinkReferences
import Shake.SearchData
import Shake.AgdaRefs
import Shake.KaTeX
import Shake.Git

import HTML.Emit

buildMarkdown :: AgdaRefs -- ^ All Agda identifiers in the codebase.
              -> FilePath -- ^ Input markdown file, produced by the Agda compiler.
              -> FilePath -- ^ Output HTML file.
              -> Action ()
buildMarkdown refs input output = do
  gitCommit <- gitCommit
  let modname = dropDirectory1 (dropDirectory1 (dropExtension input))

  need [templateName, bibliographyName, autorefsName, input]

  modulePath <- findModule modname
  authors <- gitAuthors modulePath
  autorefs <- liftIO $ readAutoRefs autorefsName
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
      . Map.insert "bibliography" (mStr bibliographyName)
      . Map.insert "link-citations" (MetaBool True)
      . unMeta

  (markdown, references) <- liftIO do
    contents <- Text.readFile input
    either (fail . show) pure =<< runIO do
      Pandoc meta markdown <- readMarkdown def { readerExtensions = getDefaultExtensions "markdown" } [(input, contents)]
      let pandoc = Pandoc (patchMeta meta) markdown
      (,) <$> processCitations pandoc <*> getReferences Nothing pandoc

  liftIO $ Dir.createDirectoryIfMissing False "_build/diagrams"

  let refMap = Map.fromList $ map (\x -> (Cite.unItemId . Cite.referenceId $ x, x)) references
  markdown <- walkM (patchInline refMap autorefs) . walk patchInlines . linkReferences modname $ markdown
  (markdown, MarkdownState references dependencies) <- runWriterT (walkM patchBlock markdown)
  need dependencies

  text <- liftIO $ either (fail . show) pure =<< runIO (renderMarkdown authors references modname markdown)

  tags <- mapM (parseAgdaLink modname refs) . foldEquations False $ parseTags text
  traverse_ (checkMarkup input) tags
  liftIO . Text.writeFile output $ renderHTML5 tags

  liftIO $ Dir.createDirectoryIfMissing False "_build/search"
  liftIO $ encodeFile ("_build/search" </> modname <.> "json") (query (getHeaders (Text.pack modname)) markdown)

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


-- | Patch a sequence of inline elements. `patchInline' should be preferred
-- where possible, this is only useful when you cannot modify inlines in
-- isolation.
patchInlines :: [Inline] -> [Inline]
-- Replace any expression $foo$-bar with <span ...>$foo$-bar</span>, so that
-- the equation is not split when word wrapping.
patchInlines (m@Math{}:s@(Str txt):xs)
  | not (Text.isPrefixOf " " txt)
  = htmlInl "<span style=\"white-space: nowrap;\">" : m : s : htmlInl "</span>"
  : patchInlines xs
patchInlines (x:xs) = x:patchInlines xs
patchInlines [] = []


-- | Rewrite a single inline element.
patchInline
  :: Map.Map Text (Cite.Reference Inlines)
  -- ^ A lookup of reference names to the actual reference.
  -> Map.Map Text Text
  -- ^ A lookup table of automatic <ref /> links. I hate this, but
  -- Pandoc doesn't let me do any better.
  -> Inline
  -> Action Inline
-- Pre-render latex equations.
patchInline _ _ (Math DisplayMath contents) = htmlInl <$> getDisplayMath contents
patchInline _ _ (Math InlineMath contents) = htmlInl <$> getInlineMath contents
-- Add the title to reference links.
patchInline refMap _ (Link attrs contents (target, ""))
  | Just citation <- Text.stripPrefix "#ref-" target
  , Just ref <- Map.lookup citation refMap
  , Just title <- Cite.valToText =<< Cite.lookupVariable "title" ref
  = pure $ Link attrs contents (target, title)
patchInline _ autolinks (RawInline "tex" txt)
  | "\\r{" `Text.isPrefixOf` txt
  , "}" `Text.isSuffixOf` txt
  , let txt' = Text.strip $ Text.drop 3 txt
  , let key = Text.take (Text.length txt' - 1) txt'
  , Just target <- Map.lookup (Text.toLower key) autolinks
  = pure $ Link ("", [], []) (intersperse Space $ map Str (Text.words key)) (target, key)
patchInline _ _ h = pure h


data MarkdownState = MarkdownState
  { mdReferences :: [Val Text] -- ^ List of references extracted from Pandoc's "reference" div.
  , mdDependencies :: [String] -- ^ Additional files this markdown file depends on.
  }

instance Semigroup MarkdownState where
  (MarkdownState r s) <> (MarkdownState r' s') = MarkdownState (r <> r') (s <> s')

instance Monoid MarkdownState where
  mempty = MarkdownState mempty mempty


-- | Patch a Pandoc block element.
patchBlock :: (MonadIO f, MonadFail f, MonadWriter MarkdownState f) => Block -> f Block
-- Make all headers links, and add an anchor emoji.
patchBlock (Header i a@(ident, _, _) inl) = pure $ Header i a
  $ htmlInl (Text.concat ["<a href=\"#", ident, "\" class=\"header-link\">"])
  : inl
  ++ [htmlInl "<span class=\"header-link-emoji\">🔗</span></a>"]
-- Replace quiver code blocks with a link to an SVG file, and depend on the SVG file.
patchBlock (CodeBlock (id, classes, attrs) contents) | "quiver" `elem` classes = do
  let
    digest = showDigest . sha1 . LazyBS.fromStrict $ Text.encodeUtf8 contents
    title = fromMaybe "commutative diagram" (lookup "title" attrs)
  liftIO $ Text.writeFile ("_build/diagrams" </> digest <.> "tex") contents
  tell mempty {
    mdDependencies =
      [ "_build/html/light-" <> digest <.> "svg"
      , "_build/html/dark-" <> digest <.> "svg"
      ]
    }

  pure $ Div ("", ["diagram-container"], [])
    [ Plain [ Image (id, "diagram diagram-light":classes, attrs) [] (Text.pack ("light-" <> digest <.> "svg"), title) ]
    , Plain [ Image (id, "diagram diagram-dark":classes, attrs) [] (Text.pack ("dark-" <> digest <.> "svg"), title) ]
    ]
-- Find the references block, parse the references, and remove it. We write
-- the references as part of our template instead.
patchBlock (Div ("refs", _, _) body) = do
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
  pure Null
patchBlock h = pure h


-- | Render our Pandoc document using the given template variables.
renderMarkdown :: PandocMonad m
               => [Text] -- ^ List of authors
               -> [Val Text] -- ^ List of references
               -> String -- ^ Name of the current module
               -> Pandoc -> m Text
renderMarkdown authors references modname markdown = do
  template <- getTemplate templateName >>= runWithPartials . compileTemplate templateName
                >>= either (throwError . PandocTemplateError . Text.pack) pure

  let
    authors' = case authors of
      [] -> "Nobody"
      [x] -> x
      _ -> Text.intercalate ", " (init authors) `Text.append` " and " `Text.append` last authors

    context = Context $ Map.fromList
              [ ("is-index", toVal (modname == "index"))
              , ("authors", toVal authors')
              , ("reference", toVal references)
              ]
    options = def { writerTemplate = Just template
                  , writerTableOfContents = True
                  , writerVariables = context
                  , writerExtensions = getDefaultExtensions "html" }
  setTranslations (Lang "en" Nothing Nothing [] [] [])
  writeHtml5String options markdown


-- | Removes the RHS of equation reasoning steps?? IDK, ask Amelia.
foldEquations :: Bool -> [Tag Text] -> [Tag Text]
foldEquations _ (to@(TagOpen "a" attrs):tt@(TagText t):tc@(TagClose "a"):rest)
  | Text.length t >= 1, Text.last t == '⟨', Just href <- lookup "href" attrs =
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
getHeaders module' = flip evalState [] . getAp . query (Ap . go) where
  -- The state stores a path of headers in the document of the form (level,
  -- header), which is updated as we walk down the document.
  go :: [Block] -> State [(Int, Text)] [SearchTerm]
  go [] = pure []
  go (Header level (hId, _, _) hText:xs) = do
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
        , idDesc   = getDesc xs
        } <$> go xs
  go (Div (hId, _, _) blocks:xs) | hId /= "" = do
    path <- get

    (:) SearchTerm
      { idIdent  = Text.intercalate " > " . reverse $ hId:map snd path
      , idAnchor = module' <> ".html#" <> hId
      , idType   = Nothing
      , idDesc   = getDesc blocks
      } <$> go xs
  go (_:xs) = go xs

  renderPlain inlines = either (error . show) id . runPure . writePlain def $ Pandoc mempty [Plain inlines]

  -- | Attempt to find the "description" of a heading. Effectively, if a header
  -- is followed by a paragraph, use its contents.
  getDesc (Para x:_) = Just (renderPlain x)
  getDesc (Plain x:_) = Just (renderPlain x)
  getDesc (Div (_, cls, _) _:xs) | "warning" `elem` cls = getDesc xs
  getDesc (BlockQuote blocks:_) = getDesc blocks
  getDesc _ = Nothing

htmlInl :: Text -> Inline
htmlInl = RawInline "html"

templateName, bibliographyName, autorefsName :: FilePath
templateName = "support/web/template.html"
bibliographyName = "src/bibliography.bibtex"
autorefsName = "src/autorefs.txt"

readAutoRefs :: FilePath -> IO (Map.Map Text Text)
readAutoRefs file = do
  ts <- Text.lines <$> Text.readFile file
  let
    go line
      | (words, target) <- Text.breakOn ":" line
      , let words' = Text.strip words
      , let target' = Text.strip (Text.tail target)
      = foldMap (flip Map.singleton target' . Text.strip) (Text.splitOn "," words')
  pure $ foldMap go ts
