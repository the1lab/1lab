{-# LANGUAGE TemplateHaskellQuotes, OverloadedStrings, ScopedTypeVariables #-}

module Shake.Diagram (buildDiagram) where

import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.ByteString.Lazy (ByteString)
import Data.Text (Text)

import Development.Shake.FilePath
import Development.Shake

-- | Render a LaTeX diagram to SVG. This renders the diagram using the
-- @support/diagram.tex@ template, and then uses pdflatex and pdftocairo
-- to convert it to SVG.
buildDiagram
  :: FilePath -- ^ The input (partial) TeX file.
  -> FilePath -- ^ The output SVG file
  -> Bool     -- ^ Is this the dark mode build?
  -> Action ()
buildDiagram input output isdark = do
  need $ [input, templatePath]
      ++ ["support/darken.tex" | isdark]

  (template, diagram') <- liftIO $ (,)
    <$> Text.readFile templatePath
    <*> Text.readFile input

  let
    diagram = maybeDarken isdark diagram'
    texPath = replaceBaseName input (takeBaseName input ++ "_full" ++ ['d' | isdark])

  darkenTemplate <- if isdark
    then liftIO $ Text.readFile "support/darken.tex"
    else pure ""

  liftIO
    . Text.writeFile texPath
    . Text.replace "__BODY__" diagram
    . Text.replace "__DARK__" darkenTemplate
    $ template

  -- TODO: Do we want to parse the errors here/in the log file? Might be
  -- nice to spit out warnings/errors, but also a lot of work.
  Stdout (_ :: ByteString) <- command [] "pdflatex" ["-output-directory", takeDirectory input, "-synctex=1", "-interaction=nonstopmode", texPath]
  command_ [] "pdftocairo" ["-svg", texPath -<.> "pdf", output]

maybeDarken :: Bool -> Text -> Text
maybeDarken False = id
maybeDarken True = Text.unlines . map mkdark . Text.lines where
  mkdark :: Text -> Text
  mkdark line
    | "begin{tikzcd}" `Text.isSuffixOf` line = line <> "[background color=diagrambg]"
    | otherwise = line

templatePath :: FilePath
templatePath = "support/diagram.tex"
