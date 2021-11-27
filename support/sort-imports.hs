#!/usr/bin/env stack
{- stack --resolver lts-18.14 script
         --package text
         --package deepseq
-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Exception
import Control.DeepSeq

import Data.List (isSuffixOf, sortOn, groupBy, partition)
import qualified Data.Text.IO as Text
import qualified Data.Text as Text
import Data.Function (on)
import Data.Foldable
import Data.Ord

import Debug.Trace

import System.Environment
import System.IO

main :: IO ()
main = traverse_ sortImports =<< getArgs

sortImports :: FilePath -> IO ()
sortImports path
  | ".lagda.md" `isSuffixOf` path = sortImportsLiterate path
  | otherwise = sortImportsCode path

sortImportsCode :: FilePath -> IO ()
sortImportsCode path = do
  putStrLn $ "Sorting Agda file " ++ path
  lines <- Text.lines <$> Text.readFile path

  evaluate (rnf lines)

  withFile path WriteMode $ \handle -> do
    traverse_ (Text.hPutStrLn handle) (sortImpl lines)

sortImportsLiterate :: FilePath -> IO ()
sortImportsLiterate path = do
  putStrLn $ "Sorting Literate Agda file " ++ path
  lines <- Text.lines <$> Text.readFile path

  evaluate (rnf lines)

  withFile path WriteMode $ \handle -> do
    let
      (prefix, first_code_rest) =
        break ((||) <$> (== "```agda") <*> (== "```")) lines

    traverse_ (Text.hPutStrLn handle) prefix

    case first_code_rest of
      (pre:lines) -> do
        Text.hPutStrLn handle pre

        let (code, rest) = break ((||) <$> (== "```agda") <*> (== "```")) lines
            code' = sortImpl code

        traverse_ (Text.hPutStrLn handle) code'
        traverse_ (Text.hPutStrLn handle) rest
      _ -> traverse_ (Text.hPutStrLn handle) first_code_rest

sortImpl :: [Text.Text] -> [Text.Text]
sortImpl lines = sorted ++ emptyLineBefore' mod where
  emptyLineBefore xs = case xs of
    [] -> []
    (_:_) -> "":xs

  emptyLineBefore' xs
    | null sorted = xs
    | otherwise = case xs of
      [] -> []
      (_:_) -> "":xs

  (oi_i_o, mod) = break ("module" `Text.isPrefixOf`) lines
  (open_imports, io') = partition ("open import" `Text.isPrefixOf`) oi_i_o
  (imports, io'') = partition ("import" `Text.isPrefixOf`) io'
  (opens, prefix) = partition ("open" `Text.isPrefixOf`) io''

  sorted = filter (not . Text.null) prefix
        ++ sortItems "open import" open_imports
        ++ emptyLineBefore (sortItems "import" imports)
        ++ emptyLineBefore (sortOn (Down . Text.length) opens)

  findItem prefix line = head (Text.words (Text.drop (Text.length prefix) line))

  sortItems prefix =
      drop 1
    . concatMap (("":) . sortOn (Down . Text.length . findItem prefix))
    . groupBy ((==) `on` fst . Text.breakOn "." . findItem prefix)
    . sortOn (findItem prefix)
