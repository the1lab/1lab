{-# LANGUAGE BlockArguments, OverloadedStrings, ScopedTypeVariables #-}
module Shake.AgdaRefs
  ( AgdaRefs
  , getAgdaRefs
  , parseAgdaLink
  ) where

import qualified Data.HashMap.Strict as HM
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Aeson

import Text.HTML.TagSoup

import Development.Shake

import HTML.Base (Identifier(..))

newtype AgdaRefs = AgdaRefs { unAgdaRefs :: HM.HashMap Text Text }

-- | Get a lookup of all Agda identifiers in the codebase.
getAgdaRefs :: Rules (Action AgdaRefs)
getAgdaRefs = versioned 1 do
  rule <- newCache \() -> do
    need ["_build/all-pages.agda"]
    need ["_build/all-types.json"]

    types :: Either String [Identifier] <- liftIO $ eitherDecodeFileStrict' "_build/all-types.json"
    either fail (pure . AgdaRefs . HM.fromList . concatMap toModuleIdent) types

  pure (rule ())

  where
      toModuleIdent :: Identifier -> [(Text, Text)]
      toModuleIdent (Identifier id anchor _)
        | (filename, _) <- Text.span (/= '#') anchor
        , Just module' <- Text.stripSuffix ".html" filename
        = [(module' <> "#" <> id, anchor)
          ,(module', module' <> ".html") -- TODO: Better handling of modules?
          ]
        | otherwise = error ("Cannot determine module from " ++ Text.unpack anchor)

-- | Possibly interpret an <a href="agda://"> link to be a honest-to-god
-- link to the definition.
parseAgdaLink :: AgdaRefs
              -> Tag Text -> Tag Text
parseAgdaLink fileIds (TagOpen "a" attrs)
  | Just href <- lookup "href" attrs
  , Just ident <- Text.stripPrefix "agda://" href = do
    case HM.lookup ident (unAgdaRefs fileIds) of
      Just href -> TagOpen "a" (emplace [("href", href)] attrs)
      _ -> error $ "Could not find Agda link: " ++ show ident
parseAgdaLink _ x = x

emplace :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
emplace ((p, x):xs) ys = (p, x):emplace xs (filter ((/= p) . fst) ys)
emplace [] ys = ys
