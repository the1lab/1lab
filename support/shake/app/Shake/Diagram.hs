{-# LANGUAGE TemplateHaskellQuotes, OverloadedStrings, ScopedTypeVariables #-}

module Shake.Diagram (buildDiagram, diagramHeight) where

import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.ByteString.Lazy (ByteString)
import Data.Text (Text)

import Text.HTML.TagSoup

import Development.Shake.FilePath
import Development.Shake

-- | Render a LaTeX diagram to SVG. This renders the diagram using the
-- @support/diagram.tex@ template, and then uses pdflatex and pdftocairo
-- to convert it to SVG.
buildDiagram
  :: Action Text -- ^ What preamble should we use?
  -> FilePath    -- ^ The input (partial) TeX file.
  -> FilePath    -- ^ The output SVG file
  -> Bool
  -> Action ()
buildDiagram preamble input output isdark = do
  need [input, templatePath]

  (template, diagram') <- liftIO $ (,)
    <$> Text.readFile templatePath
    <*> Text.readFile input

  let
    diagram = maybeDarken isdark diagram'
    texPath = replaceBaseName input (takeBaseName input ++ "_full" ++ ['d' | isdark])

  preamble <- preamble

  liftIO
    . Text.writeFile texPath
    . Text.replace "__BODY__" diagram
    . Text.replace "__PREAMBLE__" preamble
    $ template

  -- TODO: Do we want to parse the errors here/in the log file? Might be
  -- nice to spit out warnings/errors, but also a lot of work.
  Stdout (_ :: ByteString) <- command [] "pdflatex" ["-output-directory", takeDirectory input, "-synctex=1", "-interaction=nonstopmode", texPath]
  command_ [] "pdftocairo" ["-svg", texPath -<.> "pdf", output]

-- | Compute the scaled height of a diagram (given in SVG), to use as a
-- @style@ tag.
diagramHeight :: FilePath -> Action Double
diagramHeight fp = do
  contents <- readFile' fp
  let
    height (TagOpen "svg" attrs:xs) | Just h <- lookup "height" attrs = h
    height (_:t) = height t
    height [] = error $ "Diagram SVG has no height: " <> fp

    -- The ratio between heights is a magic number in the purest sense
    -- of the word. @ncfavier obtained it through divination.
    it :: Double
    it = read (height (parseTags contents)) * (25 / 12)

  pure $! it

maybeDarken :: Bool -> Text -> Text
maybeDarken False = id
maybeDarken True = Text.unlines . map mkdark . Text.lines where
  mkdark :: Text -> Text
  mkdark line
    | "begin{tikzcd}" `Text.isSuffixOf` line = line <> "[background color=diagrambg]"
    | otherwise = line

templatePath :: FilePath
templatePath = "support/diagram.tex"
