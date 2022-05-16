{-# LANGUAGE BlockArguments, OverloadedStrings, RankNTypes #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Main (main) where

import Control.Monad.IO.Class
import Control.Monad.Writer

import qualified Data.Text.IO as Text
import qualified Data.Map.Lazy as Map
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Map.Lazy (Map)
import Data.Foldable
import Data.Maybe
import Data.Text (Text)
import Data.List

import Development.Shake.FilePath
import Development.Shake

import Network.URI.Encode (decodeText)

import qualified System.Directory as Dir

import Text.HTML.TagSoup

import Text.Printf

import Agda.Interaction.FindFile (SourceFile(..))
import Agda.TypeChecking.Monad.Base
import Agda.Interaction.Options
import Agda.Interaction.Imports
import Agda.Compiler.Backend
import Agda.Utils.FileName

import qualified System.Environment as Env
import HTML.Backend
import HTML.Base
import HTML.Emit
import System.IO (IOMode(..), hPutStrLn, withFile)
import Agda

import Shake.Markdown
import Shake.KaTeX
import Shake.LinkGraph
import Shake.Git

{-
  Welcome to the Horror That Is 1Lab's Build Script.

  Building 1Lab comprises of (roughly) the following steps:
-}
main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="_build", shakeChange=ChangeDigest} $ do
  fileIdMap <- newCache parseFileIdents
  gitRules
  katexRules

  {-
    Write @_build/all-pages.agda@. This imports every module in the source tree
    (causing Agda to compile them) as well as importing all builtin modules
    (which is required for fetching type information).

    Once the file is produced, compile them and write the resulting HTML (for
    @.agda@) and markdown (for @.lagda.md@) files to @_build/html0@.
  -}
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

    liftIO $ Dir.createDirectoryIfMissing True "_build/html0"
    traced "agda" $
      runAgda defaultOptions{optInputFile = Just "_build/all-pages.agda"} $
      compileAgda out

  {-
    For each 1Lab module, read the emitted file from @_build/html0@. If its
    HTML, we just copy it to @_build/html1@. Otherwise we compile the markdown
    to HTML with some additional post-processing steps (see 'buildMarkdown')

    Finally we emit the HTML using the @support/web/template.html@ template
    and run @agda-fold_equations@ on the output.
  -}
  "_build/html1/*.html" %> \out -> do
    need ["_build/all-pages.agda"]

    let
      modname = dropExtension (takeFileName out)
      input = "_build/html0" </> modname

    ismd <- liftIO $ Dir.doesFileExist (input <.> ".md")

    if ismd
      then buildMarkdown (input <.> ".md") out
      else liftIO $ Dir.copyFile (input <.> ".html") out

  {-
    @_build/html1@ now contains all processed 1Lab modules in HTML form. We now
    'just' need to do some additional post-processing before copying them into
    our final @_build/html@ output folder.

     - Replace @agda://xyz@ links with a link to the actual definition
       ('parseAgdaLink').
     - Check the markup for raw <!-- or -->, which indicates a misplaced
       comment ('checkMarkup').
  -}
  "_build/html/*.html" %> \out -> do
    let input = "_build/html1" </> takeFileName out
    need [input]

    text <- liftIO $ Text.readFile input
    tags <- traverse (parseAgdaLink fileIdMap) (parseTags text)
    traverse_ (checkMarkup (takeFileName out)) tags
    liftIO $ Text.writeFile out (renderHTML5 tags)

  "_build/html/static/links.json" %> \out -> do
    need ["_build/html1/all-pages.html"]
    (start, act) <- runWriterT $ findLinks (tell . Set.singleton) . parseTags
      =<< liftIO (readFile "_build/html1/all-pages.html")
    need (Set.toList act)
    traced "crawling links" . withFile out WriteMode $ \h -> do
      hPutStrLn h "["
      crawlLinks
        (\x o -> liftIO $ hPrintf h "[%s, %s],"
          (show (dropExtension x))
          (show (dropExtension o)))
        (const (pure ()))
        (Set.toList start)
      hPutStrLn h "null]"

  "_build/html/static/search.json" %> \out -> do
    need ["_build/html1/all-pages.html"]
    copyFile' "_build/all-types.json" out

  -- Compile Quiver to SVG. This is used by 'buildMarkdown'.
  "_build/html/*.svg" %> \out -> do
    let inp = "_build/diagrams" </> takeFileName out -<.> "tex"
    need [inp]
    command_ [Traced "build-diagram"] "sh"
      ["support/build-diagram.sh", out, inp]
    removeFilesAfter "." ["rubtmp*"]

  "_build/html/css/*.css" %> \out -> do
    let inp = "support/web/css/" </> takeFileName out -<.> "scss"
    getDirectoryFiles "support/web/css" ["**/*.scss"] >>= \files -> need ["support/web/css" </> f | f <- files]
    command_ [] "sassc" [inp, out]

  "_build/html/favicon.ico" %> \out -> do
    need ["support/favicon.ico"]
    copyFile' "support/favicon.ico" out

  "_build/html/static/**/*" %> \out -> do
    let inp = "support/" </> dropDirectory1 (dropDirectory1 out)
    need [inp]
    traced "copying" $ Dir.copyFile inp out

  "_build/html/*.js" %> \out -> do
    getDirectoryFiles "support/web/js" ["**/*.ts", "**/*.tsx"] >>= \files -> need ["support/web/js" </> f | f <- files]

    let inp = "support/web/js" </> takeFileName out -<.> "ts"
    command_ [] "node_modules/.bin/esbuild"
      [ "--bundle", inp
      , "--outfile=" ++ out
      , "--target=es2017"
      , "--minify"
      , "--sourcemap"
      ]

  {-
    The final build step. This basically just finds all the files we actually
    need and kicks off the above job to build them.
  -}
  phony "all" do
    need ["_build/all-pages.agda"]
    files <- filter ("open import" `isPrefixOf`) . lines <$> readFile' "_build/all-pages.agda"
    need $ "_build/html/all-pages.html"
         : [ "_build/html" </> (words file !! 2) <.> "html"
           | file <- files
           ]

    static <- getDirectoryFiles "support/static/" ["**/*"] >>= \files ->
      pure ["_build/html/static" </> f | f <- files]
    agda <- getDirectoryFiles "_build/html0" ["Agda.*.html"] >>= \files ->
      pure ["_build/html/" </> f | f <- files]
    need $ [ "_build/html/favicon.ico"
           , "_build/html/static/links.json"
           , "_build/html/static/search.json"
           , "_build/html/css/default.css"
           , "_build/html/main.js"
           , "_build/html/code-only.js"
           ] ++ static ++ agda

  -- ???

  phony "clean" do
    removeFilesAfter "_build" ["html0/*", "html/*", "diagrams/*", "*.agda", "*.md", "*.html"]

  phony "really-clean" do
    need ["clean"]
    removeFilesAfter "_build" ["**/*.agdai", "*.lua"]

  phony "typecheck-ts" do
    getDirectoryFiles "support/web/js" ["**/*.ts", "**/*.tsx"] >>= \files -> need ["support/web/js" </> f | f <- files]
    command_ [] "node_modules/.bin/tsc" ["--noEmit", "-p", "tsconfig.json"]

  -- Profit!



--------------------------------------------------------------------------------
-- Various oracles
--------------------------------------------------------------------------------

-- | A link to an identifier in an emitted Agda file of the form @1Lab.Module#1234@.
newtype Reference = Reference Text deriving (Eq, Show)

-- | Parse an Agda module in @_build/html1@ and build a map of all its definitions
-- to their link.
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
      , mod `Text.isPrefixOf` href, id `Text.isSuffixOf` href
      = go (Map.insert name (Reference href) fwd)
           (Map.insert href name rev) xs
      | Just classes <- lookup "class" attrs, Just href <- lookup "href" attrs
      , "Module" `elem` Text.words classes, mod `Text.isPrefixOf` href
      = go (Map.insert name (Reference href) fwd)
           (Map.insert href name rev) xs
    go fwd rev (_:xs) = go fwd rev xs
    go fwd rev [] = (fwd, rev)

--------------------------------------------------------------------------------
-- Additional HTML post-processing
--------------------------------------------------------------------------------

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: (Text -> Action (Map Text Reference, Map Text Text))
              -> Tag Text -> Action (Tag Text)
parseAgdaLink fileIds (TagOpen "a" attrs)
  | Just href <- lookup "href" attrs, Text.pack "agda://" `Text.isPrefixOf` href = do
    href <- pure $ Text.splitOn "#" (Text.drop (Text.length "agda://") href)
    let
      cont mod ident = do
        (idMap, _) <- fileIds mod
        case Map.lookup ident idMap of
          Just (Reference href) -> do
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

-- | Check HTML markup is well-formed.
checkMarkup :: FilePath -> Tag Text -> Action ()
checkMarkup file (TagText txt)
  |  "<!--" `Text.isInfixOf` txt || "<!–" `Text.isInfixOf` txt
  || "-->" `Text.isInfixOf` txt  || "–>" `Text.isInfixOf` txt
  = fail $ "[WARN] " ++ file ++ " contains misplaced <!-- or -->"
checkMarkup _ _ = pure ()

--------------------------------------------------------------------------------
-- Loading types from .agdai files
--------------------------------------------------------------------------------

compileAgda :: FilePath -> String -> TCMT IO ()
compileAgda path _ = do
  skipTypes <- liftIO . fmap isJust . Env.lookupEnv $ "SKIP_TYPES"
  source <- parseSource . SourceFile =<< liftIO (absolute path)
  basepn <- liftIO $ absolute "src/"
  cr <- typeCheckMain TypeCheck source
  modifyTCLens stBackends
    (htmlBackend (filePath basepn) defaultHtmlOptions{htmlOptGenTypes = not skipTypes}:)
  callBackend "HTML" IsMain cr

