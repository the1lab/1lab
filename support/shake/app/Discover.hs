{-
Description: Parse a Markdown file, which is meant to be interpreted as
a table of contents/indexed, and automatically compile any reachable
Agda links. Each discovered Agda file will be associated with a unique
identifier, which can be used to link to that file in the generated
output.
-}

{-# LANGUAGE FlexibleContexts, LambdaCase, BlockArguments #-}

module Main (main) where

import Agda.Interaction.Options.Lenses
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports
import Agda.Compiler.Backend hiding (options)
import Control.Monad.Except
import Agda.Utils.FileName
import System.Environment
import Agda.Utils.Pretty
import HTML.Backend
import System.Exit
import HTML.Base

import Agda

import qualified Data.Text.IO as T
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Traversable
import Data.Foldable
import Data.Maybe
import Data.IORef
import Data.List
import Text.Pandoc.Walk
import Text.Pandoc

import Control.Monad.Writer
import System.Directory
import System.IO.Temp
import System.IO
import System.FilePath

import Shake.Markdown

main :: IO ()
main = do
  args <- getArgs
  let
    parse = getOptSimple args options $ \file (x,opts) ->
      pure (x, opts{ optInputFile = Just file })

  parsed <- runOptM $ parse (defaultHtmlOptions, defaultOptions)

  case parsed of
    Left e -> error e

    Right (htmlopt, agdaopt) -> do

      createDirectoryIfMissing True "_build/html0"

      case optPrintHelp agdaopt of
        Just help -> do
          putStrLn $ usage (void <$> options) "build-agda-index" help
          exitSuccess
        Nothing -> pure ()

      let Just inp' = optInputFile agdaopt

      inp   <- filePath <$> absolute inp'
      state <- newIORef mempty

      links <- query (dfsAgdaLinks (takeDirectory inp) state) =<< parseMarkdown inp

      parsed' <- for links $ \(url, file) -> do
        if ".lagda.md" `isSuffixOf` file
          then do
            source <- runAgda agdaopt $ \_ -> do
              parseSource . SourceFile =<< liftIO (absolute file)

            pure (Just (url, source))
          else pure Nothing

      let
        parsed = catMaybes parsed'
        unparsed :: [((Text, String), Int)]
        unparsed = [ (f, i) | (f, i) <- zip links [0..], not (".lagda.md" `isSuffixOf` snd f) ]

      withFile "_build/all-pages.agda" WriteMode $ \handle -> do
        hPutStrLn handle "{-# OPTIONS --rewriting --cubical #-}"
        hPutStrLn handle "module all-pages where"
        for_ parsed $ \(_, mod) -> do
          hPutStrLn handle $ "import " ++ render (pretty (srcModuleName mod))

      runAgda agdaopt $ \basepn -> do
        modifyTCLens stBackends (htmlBackend basepn htmlopt:)
        setIncludeDirs
          ( Set.toList (Set.fromList (map (takeDirectory . snd) links))
          ++ ["_build/"] )
          =<< liftIO (absolute (takeDirectory inp) )

        source <- parseSource . SourceFile =<< liftIO (absolute "_build/all-pages.agda")
        modifyPragmaOptions $ \f -> f { optAllowUnsolved = True }
        cr <- typeCheckMain TypeCheck source

        callBackend "HTML" IsMain cr

      let
        modData =
          [ (file, T.pack mn, "_build/html0" </> mn <.> "md")
          | (file, mod) <- parsed
          , let mn = render (pretty (srcModuleName mod))
          ]

        headingMap =
                      Map.fromList [ (f, x) | (f, x, _) <- modData ]
          `Map.union` Map.fromList [ (f, T.pack (show id) <> T.pack x) | ((f, x'), id) <- unparsed, let x = dropExtension (takeFileName x') ]

        wrap x@Table{} = Div (mempty, [], [(T.pack "style", T.pack "overflow-x: auto")]) [x]
        wrap x = x

      readme <- parseMarkdown inp

      T.writeFile (inp' -<.> "html")
        =<< runIOorExplode (renderMarkdown [] [] inp' $ walk wrap $ walk (linkToHeading headingMap) readme)

      pagelets <- listDirectory "_build/html0"
      for_ pagelets $ \source' ->
        when (".md" `isSuffixOf` source') $ do
          let source = "_build/html0" </> source'
          putStrLn $ "Generating pagelet: " ++ show source
          p <- parseMarkdown source
          T.writeFile (source -<.> "html")
            =<< runIOorExplode (renderMarkdown [] [] source (walk wrap $ walk (linkToHeading headingMap) p))

      for_ unparsed $ \((_, source), id) -> do
        let
          target = "_build/html0" </> show id ++ takeFileName source -<.> "html"
        putStrLn $ "Generating pagelet: " ++ target
        p <- parseMarkdown source
        T.writeFile target
          =<< runIOorExplode (renderMarkdown [] [] source (walk wrap $ walk (linkToHeading headingMap) p))

linkToHeading :: Map Text Text -> Inline -> Inline
linkToHeading map (Link attr anchor (url, title))
  | Just t <- Map.lookup url map = Link attr anchor (t <> T.pack ".html", title)
linkToHeading _ x = x

dfsAgdaLinks
  :: FilePath
  -> IORef (Set Text)
  -> Inline
  -> IO [(Text, FilePath)]
dfsAgdaLinks basepath vis (Link attr anchor (url, title))
  | (T.pack ".md" `T.isSuffixOf` url) && not (T.pack "http" `T.isPrefixOf` url) = do
    vis' <- readIORef vis
    if url `Set.member` vis'
      then do
        pure []
      else do
        let
          url' = T.unpack url
          basepath' = takeDirectory (basepath </> url')
        writeIORef vis $ Set.insert url vis'
        links <- query (dfsAgdaLinks basepath' vis) =<<
          parseMarkdown (basepath </> url')
        pure ((url, basepath </> url'):links)
dfsAgdaLinks _ _ _ = pure []

options :: [OptDescr (Flag (HtmlOptions, CommandLineOptions))]
options = fmap (fmap modfst) htmlOpts ++ fmap (fmap modsnd) standardOptions
  where
    modsnd f (x, y) = (,) x <$> f y
    modfst f (x, y) = flip (,) y <$> f x

    htmlOpts :: [OptDescr (Flag HtmlOptions)]
    htmlOpts =
      [ Option [] ["html-dir"] (ReqArg (\d x -> pure x{htmlOptDir=d}) "DIR")
          "directory in which HTML files are placed (default: _build/html0)"

      , Option [] ["html-highlight"] (ReqArg htmlHighlightFlag "[code,all,auto]")
          "whether to highlight only the code parts (code) or the file as a whole (all) or decide by source file type (default: auto)"

      , Option [] ["css"] (ReqArg (\d x -> pure x{htmlOptCssUrl=d}) "URL")
          "the CSS file used by the HTML files (treated as a URL; can be relative)"

      , Option [] ["html"] (NoArg pure) "(for compatibility, ignored)"
      ]

parseHtmlHighlightFlag :: MonadError String m => String -> m HtmlHighlight
parseHtmlHighlightFlag "code" = return HighlightCode
parseHtmlHighlightFlag "all"  = return HighlightAll
parseHtmlHighlightFlag "auto" = return HighlightAuto
parseHtmlHighlightFlag opt    = throwError $ concat ["Invalid option <", opt, ">, expected <all>, <auto> or <code>"]

htmlHighlightFlag :: String -> Flag HtmlOptions
htmlHighlightFlag opt    o = do
  flag <- parseHtmlHighlightFlag opt
  return $ o { htmlOptHighlight = flag }

parseMarkdown :: FilePath -> IO Pandoc
parseMarkdown path =
  do
    text <- T.readFile path
    runIOorExplode $ readMarkdown ourOpts text
  where
    ourOpts :: ReaderOptions
    ourOpts = def{ readerExtensions = pandocExtensions }
