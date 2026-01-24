{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module Shake.Recent where

import qualified Data.Map.Strict as Map
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text as Text
import Data.Maybe
import Data.List (sortOn)
import Data.Text (Text)

import Development.Shake.FilePath
import Development.Shake

import Shake.Modules (getOurModules, moduleName)
import Shake.Git (gitCommand)

import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Blaze.Html5 as H
import Text.Blaze.Html5 ((!))
import Text.Blaze.Renderer.Text (renderMarkup)
import Text.Pandoc.Definition (Block(RawBlock))


data Commit = Commit
  { commitAuthor    :: Text
  , commitSubject   :: Text
  , commitHash      :: Text

  , commitDate      :: Text

  , commitAdditions :: [Text]
  }
  deriving (Show)


recentAdditions :: Action [Commit]
recentAdditions = do
  Stdout log <- gitCommand
    [ "log", "--diff-filter=A"
    , "--pretty=format:%H%x00%aN%x00%s%x00%ad"
    , "--date=format:%B %d, %Y"
    , "--", "src/"
    ]

  allMods <- getOurModules

  let
    changes = take 20 $ lines log

    parse :: String -> Action (Maybe Commit)
    parse s = do
      let
        [ hash, author, message, date ] = Text.splitOn "\NUL" $ Text.pack s

        file out =
          let
            srcfp = drop 2 out -- remove A\t
            fp = dropExtensions $ dropDirectory1 srcfp
          in moduleName fp

      Stdout out <- gitCommand ["show", "--diff-filter=A", "--name-status", "--pretty=oneline", Text.unpack hash ]

      let
        mods  = map Text.pack $ filter (`Map.member` allMods) $ map file $ drop 1 $ lines out
        valid = not (null mods)

      pure $! if valid
        then Just Commit
          { commitAuthor    = author
          , commitSubject   = message
          , commitHash      = hash
          , commitDate      = date
          , commitAdditions = mods
          }
        else Nothing

  take 10 . catMaybes <$> parallel (map parse changes)

blazeCommit :: String -> Commit -> H.Markup
blazeCommit baseUrl (Commit author subject hash date changes) = do
  let
    base = Text.pack baseUrl
    link f = H.preEscapedTextValue $ base <> f <> ".html"
    split = Text.intercalate ".&shy;" . Text.split (== '.')
    change f = H.span ! A.class_ "Agda" $
      H.a ! A.href (link f) ! A.class_ "Module" $ H.preEscapedText (split f)

    sep [] = ""
    sep [x] = x
    sep [x, y] = x <> " and " <> y
    sep [x, y, z] = x <> ", " <> sep [y <> ",", z]
    sep (x:xs) = x <> ", " <> sep xs

    pl | length changes == 1 = " "
       | otherwise = "s "

    changed = map change (take 5 (sortOn Text.length changes)) ++ [ H.string (show (length changes - 10) <> " more") | length changes > 10 ]

  H.div ! A.class_ "commit" $ do
    H.a
      ! A.href ("https://github.com/the1lab/1lab/commit/" <> H.preEscapedTextValue hash)
      ! A.class_ "commit-subject"
      $ H.text subject
    H.span ! A.class_ "commit-author-date" $ do
      H.span $ H.text author
      " authored on "
      H.span $ H.text date
    H.span ! A.class_ "commit-changes" $
      "Added module" <> pl <> sep changed <> "."

renderCommit :: String -> Commit -> Block
renderCommit = ((RawBlock "html" . Lazy.toStrict . renderMarkup) .) . blazeCommit
