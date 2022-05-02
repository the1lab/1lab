-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

{-# LANGUAGE FlexibleContexts #-}
module Main (main) where

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports
import Agda.Compiler.Backend hiding (options)
import Control.Monad.Except
import Agda.Utils.FileName
import System.Environment
import HTML.Backend
import System.Exit
import HTML.Base

import Agda

main :: IO ()
main = do
  args <- getArgs
  let
    parse = getOptSimple args options $ \file (x,opts) ->
      pure (x,opts{ optInputFile = Just file })
  parsed <- runOptM $ parse (defaultHtmlOptions, defaultOptions)
  case parsed of
    Left e -> error e
    Right (htmlopt, agdaopt) -> do
      case optPrintHelp agdaopt of
        Just help -> do
          putStrLn $ usage (void <$> options) "agda-typed-html" help
          exitSuccess
        Nothing -> pure ()
      runAgda agdaopt $ \basepn -> do
        let Just inp = optInputFile agdaopt
        source <- parseSource . SourceFile =<< liftIO (absolute inp)
        cr <- typeCheckMain TypeCheck source
        modifyTCLens stBackends (htmlBackend basepn htmlopt:)
        callBackend "HTML" IsMain cr

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
