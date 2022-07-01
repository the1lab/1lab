{-# LANGUAGE BlockArguments, OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module Main (main) where

import Control.Concurrent.STM
import Control.Monad.IO.Class
import Control.Monad.Writer
import Control.Exception

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Bifunctor
import Data.Foldable
import Data.Either
import Data.List

import Development.Shake.FilePath
import Development.Shake.Database
import Development.Shake hiding (getEnv)

import qualified System.Directory as Dir
import qualified System.FSNotify as Watch
import System.Console.GetOpt
import System.Environment
import System.Time.Extra
import System.Exit

import Text.HTML.TagSoup

import Text.Printf

import System.IO (IOMode(..), hPutStrLn, withFile)

import HTML.Backend (builtinModules)

import Shake.Options
import Shake.AgdaCompile
import Shake.AgdaRefs (getAgdaRefs)
import Shake.SearchData
import Shake.LinkGraph
import Shake.Markdown
import Shake.Modules
import Shake.Diagram
import Shake.KaTeX
import Shake.Git

import Timer

{-
  Welcome to the Horror That Is 1Lab's Build Script.

  Building 1Lab comprises of (roughly) the following steps:
-}
rules :: Rules ()
rules = do
  agdaRules
  agdaRefs <- getAgdaRefs
  gitRules
  katexRules
  (getOurModules, getAllModules) <- moduleRules

  {-
    Write @_build/all-pages.agda@. This imports every module in the source tree
    (causing Agda to compile them) as well as importing all builtin modules
    (which is required for fetching type information).

    Once the file is produced, compile them and write the resulting HTML (for
    @.agda@) and markdown (for @.lagda.md@) files to @_build/html0@.
  -}
  "_build/all-pages.agda" %> \out -> do
    modules <- Map.toList <$> getOurModules
    let
      toOut (x, WithText) = x ++ " -- (text page)"
      toOut (x, CodeOnly) = x ++ " -- (code only)"

    writeFileLines out $ "{-# OPTIONS --cubical #-}"
                       : ["open import " ++ toOut x | x <- modules]
                      ++ ["import " ++ x ++ " -- (builtin)" | x <- builtinModules]

  {-
    For each 1Lab module, read the emitted file from @_build/html0@. If its
    HTML, we just copy it to @_build/html@. Otherwise we compile the markdown
    to HTML with some additional post-processing steps (see 'buildMarkdown')
  -}
  "_build/html/*.html" %> \out -> do
    let
      modName = dropExtension (takeFileName out)
      input = "_build/html0" </> modName

    modKind <- Map.lookup modName <$> getOurModules

    case modKind of
      Just WithText -> do
        agdaRefs <- agdaRefs
        buildMarkdown agdaRefs (input <.> ".md") out
      _ -> copyFile' (input <.> ".html") out
  "_build/search/*.json" %> \out -> need ["_build/html/" </> takeFileName out -<.> "html" ]

  "_build/html/static/links.json" %> \out -> do
    need ["_build/html/all-pages.html"]
    (start, act) <- runWriterT $ findLinks (tell . Set.singleton) . parseTags
      =<< liftIO (readFile "_build/html/all-pages.html")
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
    modules <- filter ((==) WithText . snd) . Map.toList <$> getOurModules
    let searchFiles = "_build/all-types.json":map (\(x, _) -> "_build/search" </> x <.> "json") modules
    need searchFiles
    searchData <- traverse readSearchData searchFiles
    writeSearchData out (concat searchData)

  -- Compile Quiver to SVG. This is used by 'buildMarkdown'.
  "_build/html/light-*.svg" %> \out -> do
    let inp = "_build/diagrams" </> drop (length ("light-" :: String)) (takeFileName out) -<.> "tex"
    buildDiagram inp out False

  "_build/html/dark-*.svg" %> \out -> do
    let inp = "_build/diagrams" </> drop (length ("dark-" :: String)) (takeFileName out) -<.> "tex"
    buildDiagram inp out True

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
    agda <- getAllModules >>= \modules ->
      pure ["_build/html" </> f <.> "html" | (f, _) <- Map.toList modules]
    static <- getDirectoryFiles "support/static/" ["**/*"] >>= \files ->
      pure ["_build/html/static" </> f | f <- files]
    need $
      static ++ agda ++
        [ "_build/html/favicon.ico"
        , "_build/html/static/links.json"
        , "_build/html/static/search.json"
        , "_build/html/css/default.css"
        , "_build/html/main.js"
        , "_build/html/code-only.js"
        ]

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

main :: IO ()
main = do
  args <- getArgs
  when ("--help" `elem` args || "-h" `elem` args) do
    putStrLn $ usageInfo "shake" optDescrs
    exitFailure

  let (opts, extra, errs) = getOpt Permute optDescrs args
      (shakeOpts, ourOpts) = partitionEithers opts
      (errs', shakeOpts') = first (++errs) $ partitionEithers shakeOpts
      rules' = setOptions ourOpts >> rules

      shakeOptions' = foldl' (flip ($)) shakeOptions{shakeFiles="_build", shakeChange=ChangeDigest} shakeOpts'
      (shakeRules, wanted) = case extra of
        [] -> (rules', [])
        files -> (withoutActions rules', [need files])

  unless (null errs') do
    for_ errs' $ putStrLn . ("1lab-shake: " ++)
    exitFailure

  let watching = Watching `elem` ourOpts

  (ok, after) <- shakeWithDatabase shakeOptions' shakeRules \db -> do
    case watching of
      False -> buildOnce db wanted
      True -> buildMany db wanted
  shakeRunAfter shakeOptions' after

  reportTimes

  unless ok exitFailure

  where
    optDescrs :: [OptDescr (Either (Either String (ShakeOptions -> ShakeOptions)) Option)]
    optDescrs = map (fmap Left) shakeOptDescrs ++ map (fmap Right) ourOptsDescrs

    ourOptsDescrs =
      [ Option "w" ["watch"] (NoArg Watching)
          "Start 1lab-shake in watch mode. Starts a persistent process which runs a subset of build tasks for interactive editing. Implies --skip-types."
      , Option [] ["skip-types"] (NoArg SkipTypes)
          "Skip generating type tooltips when compiling Agda to HTML."
      ]

    buildOnce :: ShakeDatabase -> [Action ()] -> IO (Bool, [IO ()])
    buildOnce db wanted = do
      start <- offsetTime

      res :: Either SomeException x <- try $ shakeRunDatabase db wanted

      tot <- start
      case res of
        Left err -> do
          putStrLn $ "❌ Build failed in " ++ showDuration tot
          print err
          pure (False, [])
        Right (_, actions) -> do
          putStrLn $ "✅ Build succeeded in " ++ showDuration tot
          pure (True, actions)

    buildMany :: ShakeDatabase -> [Action ()] -> IO (Bool, [IO ()])
    buildMany db wanted = Watch.withManager \mgr -> do
      (_, clean) <- buildOnce db wanted

      toRebuild <- atomically $ newTVar Set.empty
      _ <- Watch.watchTree mgr "src" (not . Watch.eventIsDirectory) (logEvent toRebuild)
      _ <- Watch.watchTree mgr "support" (not . Watch.eventIsDirectory) (logEvent toRebuild)

      root <- Dir.canonicalizePath "."

      let
        loop clean = do
          changes <- atomically do
            changes <- swapTVar toRebuild Set.empty
            when (Set.null changes) retry
            pure changes

          let
            changes' = map (makeRelative root) (Set.toList changes)

            -- If all our changed files are Agda modules, try to emit just those
            -- HTML files, rather than everything.
            (targets, targetName) = case traverse toModule changes' of
              Nothing -> (wanted, "everything")
              Just [] -> (wanted, "everything")
              Just xs ->
                let targets = map (\x -> "_build/html" </> x <.> "html") xs
                in ([need targets], intercalate ", " targets)

          putStrLn $ "🔨 " ++ intercalate ", " changes' ++ " has changed. Rebuilding " ++ targetName ++ "."

          (_, clean') <- buildOnce db targets
          loop (clean' ++ clean)

      loop clean

    logEvent toRebuild event = atomically $ modifyTVar' toRebuild (Set.insert (Watch.eventPath event))

    toModule path
      | ("src":rest) <- splitDirectories path
      = Just . intercalate "." $ init rest ++ [dropExtensions (last rest)]
      | otherwise = Nothing
