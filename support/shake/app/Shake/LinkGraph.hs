{-# LANGUAGE RankNTypes #-}

-- | Build a graph of links between nodes.
module Shake.LinkGraph
  ( findLinks
  , crawlLinks
  ) where

import Control.Monad.IO.Class

import qualified Data.Set as Set
import Data.Char (isDigit)
import Data.Foldable

import Development.Shake.FilePath

import Text.HTML.TagSoup

import qualified System.Directory as Dir

findLinks :: MonadIO m => (String -> m ()) -> [Tag String] -> m (Set.Set String)
findLinks cb (TagOpen "a" attrs:xs)
  | Just href' <- lookup "href" attrs
  , (_, anchor) <- span (/= '#') href'
  , not (any isDigit anchor)
  = do
    let href = takeWhile (/= '#') href'
    t <- liftIO $ Dir.doesFileExist ("_build/html" </> href)
    cb ("_build/html" </> href)
    if t && Set.notMember href ignoreLinks
      then Set.insert href <$> findLinks cb xs
      else findLinks cb xs
findLinks k (_:xs) = findLinks k xs
findLinks _ [] = pure mempty

ignoreLinks :: Set.Set String
ignoreLinks = Set.fromList [ "all-pages.html", "index.html" ]

crawlLinks
  :: MonadIO m'
  => (forall m. MonadIO m => String -> String -> m ())
  -> (String -> m' ())
  -> [String]
  -> m' ()
crawlLinks link need = go mempty where
  go _visitd [] = pure ()
  go visited (x:xs)
    | x `Set.member` visited = go visited xs
    | otherwise = do
      links <- findLinks need . parseTags =<< liftIO (readFile ("_build/html" </> x))
      for_ links $ \other -> link x other
      go (Set.insert x visited) (Set.toList links ++ xs)
