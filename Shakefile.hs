#!/usr/bin/env stack
{- stack --resolver lts-18.18 script
         --package aeson
         --package Agda
         --package bytestring
         --package containers
         --package directory
         --package doctemplates
         --package mtl
         --package pandoc
         --package pandoc-types
         --package process
         --package shake
         --package tagsoup
         --package text
         --package uri-encode
         --package SHA
-}
{-# LANGUAGE BlockArguments, OverloadedStrings #-}
{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TypeFamilies, FlexibleContexts #-}
module Main (main) where

import Control.Monad.IO.Class
import Control.Monad.Error.Class
import Control.Monad.Writer
import Control.Concurrent
import Control.Monad

import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import qualified Data.Map.Lazy as Map
import qualified Data.Text as Text
import Data.Aeson (eitherDecodeFileStrict')
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Digest.Pure.SHA
import Data.Map.Lazy (Map)
import Data.Text (Text)
import Data.Foldable
import Data.Either
import Data.Maybe
import Data.List

import Development.Shake.FilePath
import Development.Shake.Classes
import Development.Shake

import Network.URI.Encode (decodeText)

import qualified System.Directory as Dir
import System.IO.Unsafe
import System.Console.GetOpt
import System.Process (callCommand)
import System.IO

import Text.HTML.TagSoup
import Text.DocTemplates

import Text.Pandoc.Filter
import Text.Pandoc.Walk
import Text.Pandoc

import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Utils.Pretty
import Agda.Syntax.Common


newtype LatexEquation = LatexEquation (Bool, Text) -- TODO: Less lazy instance
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult LatexEquation = Text

data Reference
  = Reference { refHref :: Text
              , refClasses :: [Text]
              }
  deriving (Eq, Show)

moduleName :: FilePath -> String
moduleName = concat . intersperse "." . splitDirectories

findModule :: MonadIO m => String -> m FilePath
findModule modname = do
  let toPath '.' = '/'
      toPath c = c
  let modfile = "src" </> map toPath modname

  exists <- liftIO $ Dir.doesFileExist (modfile <.> "lagda.md")
  pure $ if exists
    then modfile <.> "lagda.md"
    else modfile <.> "agda"

buildMarkdown :: String
              -> (Text -> Action (Map Text Reference, Map Text Text))
              -> FilePath -> FilePath -> Action ()
buildMarkdown gitCommit moduleIds input output = do
  let
    templateName = "support/web/template.html"
    modname = moduleName (dropDirectory1 (dropDirectory1 (dropExtension input)))

  need [templateName, input]

  modulePath <- findModule modname
  let
    permalink = gitCommit </> modulePath

    title
      | length modname > 24 = '…':reverse (take 24 (reverse modname))
      | otherwise = modname

  Pandoc meta markdown <- liftIO do
    contents <- Text.readFile input
    either (fail . show) pure =<< runIO do
      md <- readMarkdown def { readerExtensions = getDefaultExtensions "markdown" } [(input, contents)]
      applyFilters def [JSONFilter "agda-reference-filter"] ["html"] md

  let
    htmlInl = RawInline (Format "html")

    -- | Replace any expression $foo$-bar with <span ...>$foo$-bar</span>, so that
    -- the equation is not split when word wrapping.
    patchInlines (m@Math{}:s@(Str txt):xs)
      | not (Text.isPrefixOf " " txt)
      = htmlInl "<span style=\"white-space: nowrap;\">" : m : s : htmlInl "</span>"
      : patchInlines xs
    patchInlines (x:xs) = x:patchInlines xs
    patchInlines [] = []

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
      tell ["_build/html" </> digest <.> "svg"]

      pure $ Div ("", ["diagram-container"], [])
        [ Plain [ Image (id, "diagram":classes, attrs) [] (Text.pack (digest <.> "svg"), title) ]
        ]
    patchBlock h = pure h

    patchInline (Math DisplayMath contents) = htmlInl <$> askOracle (LatexEquation (True, contents))
    patchInline (Math InlineMath contents) = htmlInl <$> askOracle (LatexEquation (False, contents))
    patchInline h = pure h

    mStr = MetaString . Text.pack
    patchMeta = Meta . Map.insert "title" (mStr title) . Map.insert "source" (mStr permalink) . unMeta

  liftIO $ Dir.createDirectoryIfMissing False "_build/diagrams"

  markdown <- pure . walk patchInlines . Pandoc (patchMeta meta) $ markdown
  markdown <- walkM patchInline markdown
  (markdown, dependencies) <- runWriterT $ walkM patchBlock markdown
  need dependencies

  text <- liftIO $ either (fail . show) pure =<< runIO do
    template <- getTemplate templateName >>= runWithPartials . compileTemplate templateName
                >>= either (throwError . PandocTemplateError . Text.pack) pure
    let
      context = Context $ Map.fromList [ (Text.pack "is-index", toVal (modname == "index")) ]
      options = def { writerTemplate = Just template
                    , writerTableOfContents = True
                    , writerVariables = context
                    , writerExtensions = getDefaultExtensions "html" }
    writeHtml5String options markdown

  tags <- traverse (parseAgdaLink moduleIds) (parseTags text)
  liftIO $ Text.writeFile output (renderTags tags)

  command_ [] "agda-fold-equations" [output]

main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="_build", shakeChange=ChangeDigest} $ do
  fileIdMap <- newCache parseFileIdents
  fileTyMap <- newCache parseFileTypes
  gitCommit <- newCache gitCommit

  "_build/all-pages.agda" %> \out -> do
    files <- sort <$> getDirectoryFiles "src" ["**/*.agda", "**/*.lagda.md"]
    need (map ("src" </>) files)
    let
      toOut x | takeExtensions x == ".lagda.md"
              = moduleName (dropExtensions x) ++ " -- (text page)"
      toOut x = moduleName (dropExtensions x) ++ " -- (code only)"

    writeFileLines out $ "{-# OPTIONS --cubical #-}"
                       : ["open import " ++ toOut x | x <- files]
                      ++ ["import " ++ x ++ " -- (builtin)" | x <- builtinModules]

    command [] "agda"
      [ "--html"
      , "--html-dir=_build/html0"
      , "--html-highlight=auto"
      , "--local-interfaces"
      , "--css=/css/agda-cats.css"
      , out
      ]

  "_build/types.json" %> \out -> do
    files <- sort <$> getDirectoryFiles "src" ["**/*.lagda.md", "**/*.agda"]
    need (["_build/all-pages.agda", "support/get-types.py"] ++ map ("src" </>) files)

    let modules = builtinModules ++ map (moduleName . dropExtensions) files

    command_ [FileStdout out, Stdin (intercalate "\n" modules)] "python3" ["support/get-types.py"]

  "_build/html1/*.html" %> \out -> do
    need ["_build/all-pages.agda"]

    let
      modname = dropExtension (takeFileName out)
      input = "_build/html0" </> modname

    ismd <- liftIO $ Dir.doesFileExist (input <.> ".md")

    gitCommit <- gitCommit ()

    if ismd
      then buildMarkdown gitCommit fileIdMap (input <.> ".md") out
      else liftIO $ Dir.copyFile (input <.> ".html") out

  "_build/html/*.html" %> \out -> do
    let input = "_build/html1" </> takeFileName out
    need [input]

    text <- liftIO $ Text.readFile input
    tags <- traverse (addLinkType fileIdMap fileTyMap) (parseTags text)
    liftIO $ Text.writeFile out (renderTags tags)

  "_build/html/*.svg" %> \out -> do
    let inp = "_build/diagrams" </> takeFileName out -<.> "tex"
    need [inp]
    command_ [Traced "build-diagram"] "sh"
      ["support/build-diagram.sh", out, inp]
    removeFilesAfter "." ["rubtmp*"]

  "_build/html/css/*.css" %> \out -> do
    let inp = "support/web/" </> takeFileName out -<.> "scss"
    need [inp]
    command_ [] "sassc" [inp, out]

  "_build/html/favicon.ico" %> \out -> do
    need ["support/favicon.ico"]
    copyFile' "support/favicon.ico" out

  "_build/html/static/**/*" %> \out -> do
    let inp = "support/" </> dropDirectory1 (dropDirectory1 out)
    need [inp]
    traced "copying" $ Dir.copyFile inp out

  "_build/html/*.js" %> \out -> do
    let inp = "support/web" </> takeFileName out
    need [inp]
    traced "copying" $ Dir.copyFile inp out

  phony "all" do
    need ["_build/all-pages.agda"]
    files <- filter ("open import" `isPrefixOf`) . lines <$> readFile' "_build/all-pages.agda"
    need $ "_build/html/all-pages.html"
         : [ "_build/html" </> (words file !! 2) <.> "html"
           | file <- files
           ]

    f1 <- getDirectoryFiles "support" ["**/*.scss"] >>= \files -> pure ["_build/html/css/" </> takeFileName f -<.> "css" | f <- files]
    f2 <- getDirectoryFiles "support" ["**/*.js"] >>= \files -> pure ["_build/html/" </> takeFileName f | f <- files]
    f3 <- getDirectoryFiles "support/static/" ["**/*"] >>= \files ->
      pure ["_build/html/static" </> f | f <- files]
    f4 <- getDirectoryFiles "_build/html0" ["Agda.*.html"] >>= \files ->
      pure ["_build/html/" </> f | f <- files]
    need $ "_build/html/favicon.ico":(f1 ++ f2 ++ f3 ++ f4)

  phony "clean" do
    removeFilesAfter "_build" ["html0/*", "html/*", "diagrams/*", "*.agda", "*.md", "*.html"]

  phony "really-clean" do
    need ["clean"]
    removeFilesAfter "_build" ["**/*.agdai", "*.lua"]

  versioned 1 do
    _ <- addOracleCache \(LatexEquation (display, tex)) -> do
      need [".macros"]

      let args = ["-f", ".macros", "-t"] ++ (if display then ["-d"] else [])
          stdin = LazyBS.fromStrict $ Text.encodeUtf8 tex
      Stdout out <- command [StdinBS stdin] "katex" args
      pure $ Text.decodeUtf8 out

    pure ()

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: (Text -> Action (Map Text Reference, Map Text Text))
                 -> Tag Text -> Action (Tag Text)
parseAgdaLink fileIds tag@(TagOpen "a" attrs)
  | Just href <- lookup "href" attrs, Text.pack "agda://" `Text.isPrefixOf` href = do
    href <- pure $ Text.splitOn "#" (Text.drop (Text.length "agda://") href)
    let
      cont mod ident = do
        (idMap, _) <- fileIds mod
        case Map.lookup ident idMap of
          Just (Reference href classes) -> do
            pure (TagOpen "a" (emplace [("href", href)] attrs))
          _ -> error $ "Could not compile Agda link: " ++ show href
    case href of
      [mod] -> cont mod mod
      [mod, ident] -> cont mod (decodeText ident)
      _ -> error $ "Could not parse Agda link: " ++ show href
parseAgdaLink _ x = pure x

emplace :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
emplace ((p, x):xs) ys = (p, x):emplace xs (filter ((/= p) . fst) ys)
emplace [] ys = ys

-- | Lookup an identifier given a module name and ID within that module,
-- returning its type.
addLinkType :: (Text -> Action (Map Text Reference, Map Text Text)) -- ^ Lookup an ident from a module name and location
             -> (() -> Action (Map Text (Map Text Text))) -- ^ Lookup a type from a module name and ident
             -> Tag Text -> Action (Tag Text)
addLinkType fileIds fileTys tag@(TagOpen "a" attrs)
  | Just href <- lookup "href" attrs
  , [mod, _] <- Text.splitOn ".html#" href = do
    ty <- resolveId mod href <$> fileIds mod <*> fileTys ()
    pure case ty of
      Nothing -> tag
      Just ty -> TagOpen "a" (emplace [("data-type", ty)] attrs)

    where
      resolveId mod href (_, ids) types = do
        types <- Map.lookup mod types
        id <- Map.lookup href ids
        Map.lookup id types
addLinkType _ _ x = pure x

-- | Parse an Agda module (in the final build directory) to find a list
-- of its definitions.
parseFileIdents :: Text -> Action (Map Text Reference, Map Text Text)
parseFileIdents mod =
  do
    let path = "_build/html1" </> Text.unpack mod <.> "html"
    need [ path ]
    traced ("parsing " ++ Text.unpack mod) do
      go mempty mempty . parseTags <$> Text.readFile path
  where
    go fwd rev (TagOpen "a" attrs:TagText name:TagClose "a":xs)
      | Just id <- lookup "id" attrs, Just href <- lookup "href" attrs
      , Just classes <- lookup "class" attrs
      , mod `Text.isPrefixOf` href, id `Text.isSuffixOf` href
      = go (Map.insert name (Reference href (Text.words classes)) fwd)
           (Map.insert href name rev) xs
      | Just classes <- lookup "class" attrs, Just href <- lookup "href" attrs
      , "Module" `elem` Text.words classes, mod `Text.isPrefixOf` href
      = go (Map.insert name (Reference href (Text.words classes)) fwd)
           (Map.insert href name rev) xs
    go fwd rev (_:xs) = go fwd rev xs
    go fwd rev [] = (fwd, rev)


gitCommit :: () -> Action String
gitCommit () = do
  Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"]
  pure (head (lines t))

--  Loads our type lookup table into memory
parseFileTypes :: () -> Action (Map Text (Map Text Text))
parseFileTypes () = do
  need ["_build/types.json"]
  liftIO (eitherDecodeFileStrict' "_build/types.json")
    >>= either fail (liftIO . traverse (traverse instantiate))

-- | Removes implicit arguments from the spine of an Agda type.
--
-- Implicits are removed in both rank-1 and higher rank positions (i.e.,
-- to the left and right of function arrows), including the domains of
-- Pi-types. Other positions are unaffected.

instantiate :: Text -> IO Text
instantiate ty = do
  t <- runPMIO (parse exprParser (map flipDot (Text.unpack ty)))
  case t of
    (Right exp, _)
      -> pure (Text.pack (map flipDot (render (pretty (removeImpls exp)))))
    (Left e, _) -> pure ty
  where
    removeImpls :: Expr -> Expr
    removeImpls (Pi (x :| xs) e) =
      makePi (map (fmap removeImpls) $ filter ((/= Hidden) . getHiding) (x:xs)) (removeImpls e)
    removeImpls (Fun span arg ret) =
      Fun span (removeImpls <$> arg) (removeImpls ret)
    removeImpls e = e

    -- Swaps the character '.' (illegal in Agda identifiers, but
    -- printed by Agda to indicate dependencies in generalisable
    -- variables) for the Katakana middle dot character, and vice-versa.
    --
    -- We call this function to swap '.' -> middle dot when parsing, and
    -- middle dot -> dot when printing.
    flipDot :: Char -> Char
    flipDot '.' = '\12539' -- Katakana middle dot
    flipDot '\12539' = '.'
    flipDot c = c

builtinModules :: [String]
builtinModules =
  [ "Agda.Builtin.Bool"
  , "Agda.Builtin.Char"
  , "Agda.Builtin.Cubical.HCompU"
  , "Agda.Builtin.Cubical.Path"
  , "Agda.Builtin.Cubical.Sub"
  , "Agda.Builtin.Float"
  , "Agda.Builtin.FromNat"
  , "Agda.Builtin.FromNeg"
  , "Agda.Builtin.Int"
  , "Agda.Builtin.List"
  , "Agda.Builtin.Maybe"
  , "Agda.Builtin.Nat"
  , "Agda.Builtin.Reflection"
  , "Agda.Builtin.Sigma"
  , "Agda.Builtin.String"
  , "Agda.Builtin.Unit"
  , "Agda.Builtin.Word"
  , "Agda.Primitive.Cubical"
  , "Agda.Primitive"
  ]
