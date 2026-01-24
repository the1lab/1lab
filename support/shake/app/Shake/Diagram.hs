{-# LANGUAGE TemplateHaskellQuotes, OverloadedStrings, ScopedTypeVariables, LambdaCase, BlockArguments #-}

module Shake.Diagram (diagramRules, diagramHeight) where

import Control.DeepSeq

import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import Data.Text (Text)

import Text.Pandoc.Definition
import Text.HTML.TagSoup
import Text.Pandoc.Walk

import Development.Shake.FilePath
import Development.Shake

import Shake.Modules (ModName, markdownSource)
import Shake.Digest
import Shake.KaTeX (getPreambleFor)

import qualified System.Directory as Dir

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
  command_ [NoProcessGroup, WithStderr False, EchoStdout False, EchoStderr False] "pdflatex" ["-output-directory", takeDirectory input, "-synctex=1", "-interaction=nonstopmode", texPath]
  command_ [NoProcessGroup, WithStderr False, EchoStdout False, EchoStderr False] "pdftocairo" ["-svg", texPath -<.> "pdf", output]

-- | Compute the scaled height of a diagram (given in SVG), to use as a
-- @style@ tag.
diagramHeight :: FilePath -> Action Double
diagramHeight fp = do
  contents <- readFile' fp
  let
    height (TagOpen "svg" attrs:_) | Just h <- lookup "height" attrs = take (length h - 2) h
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

diagramRules :: (FilePath -> Action Pandoc) -> Rules ()
diagramRules read = do
  -- Compile Quiver to SVG. This is used by 'buildMarkdown'.
  "_build/html/**/*.light.svg" %> \out -> do
    let
      inp = "_build/diagrams"
        </> takeFileName (takeDirectory out)
        </> takeBaseName out -<.> "tex"
    need [inp]
    buildDiagram (getPreambleFor False) inp out False

  "_build/html/**/*.dark.svg" %> \out -> do
    let
      inp = "_build/diagrams"
        </> takeFileName (takeDirectory out)
        </> takeBaseName out -<.> "tex"
    need [inp]
    buildDiagram (getPreambleFor True) inp out True

  modDiagrams :: ModName -> Action (Map String Text) <- newCache \mod -> do
    md <- markdownSource mod
    need [ md ]
    doc <- read md
    let
      diagrams = flip query doc \case
        (CodeBlock (_, classes, _) contents) | "quiver" `elem` classes ->
          Map.singleton (shortDigest contents) contents
        _ -> mempty
    diagrams `deepseq` pure diagrams

  -- Extract the diagram with the given digest from the module source
  -- file; even if the module uses many diagrams, only one will be written.
  --
  -- It's faster to traverse the markdown many times looking for each of
  -- the needed diagrams than it is to lock the folder associated with
  -- the module (since we process blocks in parallel when rendering a
  -- file).
  "_build/diagrams/*/*.tex" %> \out -> do
    let
      mod  = takeFileName (takeDirectory out)
      want = dropExtensions (takeFileName out)

    liftIO $ Dir.createDirectoryIfMissing True $ "_build/diagrams" </> mod

    contents <- (Map.! want) <$> modDiagrams mod
    liftIO $ Text.writeFile ("_build/diagrams" </> mod </> want <.> "tex") contents
