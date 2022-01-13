#!/usr/bin/env stack
{- stack --resolver lts-18.18 script
         --package shake
         --package directory
         --package tagsoup
         --package text
         --package containers
         --package uri-encode
         --package process
-}
{-# LANGUAGE BlockArguments, OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Control.Monad.IO.Class
import Control.Concurrent
import Control.Monad

import qualified Data.Text.IO as Text
import qualified Data.Map.Lazy as Map
import qualified Data.Text as Text
import Data.Map.Lazy (Map)
import Data.Text (Text)
import Data.Foldable
import Data.Either
import Data.Maybe
import Data.List

import Debug.Trace

import Development.Shake.FilePath
import Development.Shake

import Network.URI.Encode (decodeText)

import qualified System.Directory as Dir
import System.Process (callCommand)
import System.Console.GetOpt
import System.IO.Unsafe
import System.IO

import Text.HTML.TagSoup

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
              -> (Text -> Action (Map Text Reference))
              -> FilePath -> FilePath -> Action ()
buildMarkdown gitCommit cache input output = do
  need ["support/web/template.html"]

  liftIO $ Dir.createDirectoryIfMissing False "_build/diagrams"

  let
    modname = moduleName (dropDirectory1 (dropDirectory1 (dropExtension input)))

  modulePath <- findModule modname

  let
    diagrams = "_build/diagrams" </> takeFileName output <.> "txt"
    permalink = gitCommit </> modulePath

    title
      | length modname > 24 = '…':reverse (take 24 (reverse modname))
      | otherwise = modname

    pandoc_args path =
      [ "--from", "markdown", "-i", input
      , "--to", "html", "-o", path
      , "--metadata", "title=" ++ title
      , "--metadata", "source=" ++ permalink
      , "--template", "support/web/template.html"
      , "--lua-filter", "support/maths-filter.lua"
      , "--filter", "agda-reference-filter"
      , "--toc"
      ] ++ ["-V is-index" | modname == "index"]

  withTempFile $ \path -> do
    Exit c <- command
      [ AddEnv "HTML_DIR" "_build/html"
      , AddEnv "MODULE_NAME" (takeFileName output)
      , AddEnv "DIAGRAM_LIST" diagrams
      , WithStdout True
      , WithStderr True
      ]
      "pandoc"
      (pandoc_args path)

    text <- liftIO $ Text.readFile path
    tags <- traverse (parseAgdaLink cache) (parseTags text)
    liftIO $ Text.writeFile output (renderTags tags)
    command_ [] "agda-fold-equations" [output]

  diag <- doesFileExist diagrams
  when diag do
    diagrams <- lines <$> readFile' diagrams
    need [diag -<.> "svg" | diag <- diagrams]

buildAgda :: String -> Action ()
buildAgda path = do
  need [path]
  (Stdout s) <-
    command [] "agda"
      [ "--html"
      , "--html-dir=_build/html0"
      , "--html-highlight=auto"
      , "--css=/css/agda-cats.css"
      , path
      ]
  let
    out = lines s
    html = filter (not . ("Generating HTML for Agda." `isPrefixOf`))
         $ filter ("Generating HTML for" `isPrefixOf`) out

  modules <- traverse (findModule . (!! 3) . words) html
  putVerbose $ "Identified Agda dependencies: " ++ show modules
  need modules

data Flags = Only | Ding String
  deriving (Eq, Show)

run :: ([Flags] -> Rules ()) -> IO ()
run f = do
  ref <- newEmptyMVar
  files <- unsafeInterleaveIO (takeMVar ref)
  cwd <- Dir.getCurrentDirectory
  shakeArgsWith shakeOptions{shakeFiles=files} (opts cwd)
    \arguments targets -> do
      let
        flags :: [Flags]
        targets' :: [[String] -> [String]]
        (flags, targets') = partitionEithers arguments

      let paths = foldr (.) id targets' targets

      if Only `elem` flags
        then do
          putMVar ref "_build/shake-only"
          when (length paths > 1)
               (error "Invalid options specified: --only can only be used with one target")
        else
          putMVar ref "_build/shake"

      putStrLn $ "Building: " ++ show paths
      pure (Just (f flags *> want paths))
  where
    opts :: String
         -> [OptDescr (Either String
                              (Either Flags ([String] -> [String])))]
    opts cwd =
      [ Option "" ["only"] (NoArg (Right (Left Only)))
          "Rebuild only the mentioned Agda file."
      , Option "" ["at-exit"]
          (ReqArg (\x -> Right (Left (Ding x))) "The program to invoke")
          "Invoke a command after compilation finishes."
      , Option "" ["reverse"]
          (ReqArg (\x -> Right (Right (reverseTarget cwd x:))) "The Agda file to build")
          "Build the HTML file corresponding to the given Agda file"
      ]

    reverseTarget cwd path =
          "_build/html"
      </> moduleName (dropDirectory1 (dropExtensions (makeRelative cwd path)))
      <.> "html"

agdaDependency :: [Flags] -> FilePath -> IO (Action ())
agdaDependency flags file
  | Only `elem` flags = buildAgda <$> findModule (dropExtension (takeFileName file))
  | otherwise = pure $ need ["_build/all-pages.agda"]

main :: IO ()
main = run \flags -> do
  case listToMaybe $ mapMaybe (\case { Ding x -> Just x; _ -> Nothing }) flags of
    Just d -> action $ runAfter $ callCommand d
    Nothing -> pure ()

  fileIdMap <- newCache parseFileIdents
  gitCommit <- newCache gitCommit

  "_build/all-pages.agda" %> \out -> do
    files <- sort <$> getDirectoryFiles "src" ["**"]
    need (map ("src" </>) files)
    let
      toOut x | takeExtensions x == ".lagda.md"
              = moduleName (dropExtensions x) ++ " -- (text page)"
      toOut x = moduleName (dropExtensions x) ++ " -- (code only)"

    writeFileLines out $ "{-# OPTIONS --cubical #-}":["open import " ++ toOut x | x <- files]

    command [] "agda"
      [ "--html"
      , "--html-dir=_build/html0"
      , "--html-highlight=auto"
      , "--css=/css/agda-cats.css"
      , out
      ]

  "_build/html/*.html" %> \out -> do
    act <- traced "Agda dependency" $ agdaDependency flags out
    act

    let
      modname = dropExtension (takeFileName out)
      input = "_build/html0" </> modname

    ismd <- liftIO $ Dir.doesFileExist (input <.> ".md")

    gitCommit <- gitCommit ()

    if ismd
      then buildMarkdown gitCommit fileIdMap (input <.> ".md") out
      else liftIO $ Dir.copyFile (input <.> ".html") out

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

  unless (Only `elem` flags) $ phony "all" do
    need ["_build/all-pages.agda"]
    files <- filter ("open import" `isPrefixOf`) . lines <$> readFile' "_build/all-pages.agda"
    need $ "_build/html/all-pages.html"
         : [ "_build/html" </> (words file !! 2) <.> "html"
           | file <- files
           ]

    f1 <- getDirectoryFiles "." ["**/*.scss"] >>= \files -> pure ["_build/html/css/" </> takeFileName f -<.> "css" | f <- files]
    f2 <- getDirectoryFiles "." ["**/*.js"] >>= \files -> pure ["_build/html/" </> takeFileName f | f <- files]
    f3 <- getDirectoryFiles "support/static/" ["**/*"] >>= \files ->
      pure ["_build/html/static" </> f | f <- files]
    f4 <- getDirectoryFiles "_build/html0" ["Agda.*"] >>= \files ->
      pure ["_build/html/" </> f | f <- files]
    need $ "_build/html/favicon.ico":(f1 ++ f2 ++ f3 ++ f4)

  phony "clean" do
    removeFilesAfter "_build" ["html0/*", "html/*", "diagrams/*", "*.agda", "*.md", "*.html"]

  phony "really-clean" do
    need ["clean"]
    removeFilesAfter "_build" ["**/*.agdai", "*.lua"]

  phony "sync" do
    need ["all"]
    config <- lines <$> readFile' "Makefile"
    let
      servers = concatMap (drop 2 . words) $ filter ("UPLOAD_SERVERS" `isPrefixOf`) config
      configs
        = map (\x -> let [s,_,b] = words x in (drop (Text.length "UPLOAD_DIR_") s, b))
        $ filter ("UPLOAD_DIR" `isPrefixOf`) config

    for_ servers \server -> do
      let
        Just t = lookup server configs
      command_ [Traced ("rsync (for " ++ server ++ ")")] "rsync" ["_build/html/", server ++ ':':t, "-avx" ]

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: (Text -> Action (Map Text Reference))
              -> Tag Text -> Action (Tag Text)
parseAgdaLink cache tag@(TagOpen "a" attrs)
  | Just href <- lookup "href" attrs, Text.pack "agda://" `Text.isPrefixOf` href = do
    href <- pure $ Text.splitOn "#" (Text.drop (Text.length "agda://") href)
    let
      cont mod ident = do
        idMap <- cache mod
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

-- | Parse an Agda module (in the final build directory) to find a list
-- of its definitions.
parseFileIdents :: Text -> Action (Map Text Reference)
parseFileIdents mod =
  do
    let path = "_build/html" </> Text.unpack mod <.> "html"
    need [ path ]
    traced ("parsing " ++ Text.unpack mod) do
      go mempty . parseTags <$> Text.readFile path
  where
    go x (TagOpen "a" attrs:TagText name:TagClose "a":xs)
      | Just id <- lookup "id" attrs, Just href <- lookup "href" attrs
      , Just classes <- lookup "class" attrs
      , mod `Text.isPrefixOf` href, id `Text.isSuffixOf` href
      = go (Map.insert name (Reference href (Text.words classes)) x) xs
      | Just classes <- lookup "class" attrs, Just href <- lookup "href" attrs
      , "Module" `elem` Text.words classes, mod `Text.isPrefixOf` href
      = go (Map.insert name (Reference href (Text.words classes)) x) xs
    go x (_:xs) = go x xs
    go x [] = x

gitCommit :: () -> Action String
gitCommit () = do
  Stdout t <- command [] "git" ["rev-parse", "--verify", "HEAD"] 
  pure (head (lines t))