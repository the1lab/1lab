{-# LANGUAGE TemplateHaskellQuotes, OverloadedStrings, ScopedTypeVariables #-}

module Shake.Diagram (buildDiagram) where

import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.ByteString.Lazy (ByteString)

import Development.Shake.FilePath
import Development.Shake

-- | Render a LaTeX diagram to SVG. This renders the diagram using the
-- @support/diagram.tex@ template, and then uses pdflatex and pdftocairo
-- to convert it to SVG.
buildDiagram :: FilePath -- ^ The input (partial) TeX file.
             -> FilePath -- ^ The output SVG file
             -> Action ()
buildDiagram input output = do
  need [input, templatePath]

  (template, diagram) <- liftIO $ (,) <$> Text.readFile templatePath <*> Text.readFile input

  let texPath = replaceBaseName input (takeBaseName input ++ "_full")
  liftIO . Text.writeFile texPath $ Text.replace "__BODY__" diagram template

  -- TODO: Do we want to parse the errors here/in the log file? Might be
  -- nice to spit out warnings/errors, but also a lot of work.
  Stdout (_ :: ByteString) <- command [] "pdflatex" ["-output-directory", takeDirectory input, "-synctex=1", "-interaction=nonstopmode", texPath]
  command_ [] "pdftocairo" ["-svg", texPath -<.> "pdf", output]

templatePath :: FilePath
templatePath = "support/diagram.tex"
