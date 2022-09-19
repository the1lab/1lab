{-# LANGUAGE BlockArguments, OverloadedStrings, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Shake.AgdaRefs
  ( AgdaRefs
  , getAgdaRefs
  , parseAgdaLink
  ) where

import Control.Monad

import qualified Data.HashMap.Strict as HM
import qualified Data.Text as Text
import Data.Text (Text)

import Text.HTML.TagSoup

import Development.Shake

import HTML.Base (Identifier(..))

import Shake.Options
import Shake.Utils

newtype AgdaRefs = AgdaRefs { unAgdaRefs :: HM.HashMap Text Text }

-- | Get a lookup of all Agda identifiers in the codebase.
getAgdaRefs :: Rules (Action AgdaRefs)
getAgdaRefs = versioned 1 do
  rule <- newCache \() -> do
    types :: [Identifier] <- readJSONFile "_build/all-types.json"
    pure . AgdaRefs . HM.fromList . concatMap toModuleIdent $ types

  pure (rule ())

  where
    toModuleIdent :: Identifier -> [(Text, Text)]
    toModuleIdent (Identifier id anchor _)
      | (filename, _) <- Text.span (/= '#') anchor
      , Just module' <- Text.stripSuffix ".html" filename
      = [(module' <> "#" <> id, anchor)
        ,(filename <> "#" <> id, anchor)
        ,(module', filename) -- TODO: Better handling of modules?
        ]
      | otherwise = error ("Cannot determine module from " ++ Text.unpack anchor)

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: FilePath
              -> AgdaRefs
              -> Tag Text -> Action (Tag Text)
parseAgdaLink modname fileIds x@(TagOpen "a" attrs)
  | Just href <- lookup "href" attrs
  , Just ident <- Text.stripPrefix "agda://" href = do
    case HM.lookup ident (unAgdaRefs fileIds) of
      Just href -> pure $ TagOpen "a" (emplace [("href", href)] attrs)
      _ -> do
        watching <- getWatching
        unless watching $ error $ "Could not find Agda link " ++ Text.unpack ident ++ " in " ++ modname
        pure x
parseAgdaLink _ _ x = pure x

emplace :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
emplace ((p, x):xs) ys = (p, x):emplace xs (filter ((/= p) . fst) ys)
emplace [] ys = ys
