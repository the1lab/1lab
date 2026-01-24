{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances,
 MultiParamTypeClasses, TupleSections, LambdaCase, UndecidableInstances,
 GeneralizedNewtypeDeriving, OverloadedStrings #-}

-- | Functions for parsing macro definitions, adapted from the texmath
-- package to support extracting the arity of macros.
module Macros
  ( Macro
  , Preamble
  , parsePreamble
  , preambleToLatex
  , applyPreamble
  )
  where

import Control.Applicative
import Control.DeepSeq
import Control.Monad

import qualified Data.Text as T
import Data.Char (isDigit, isLetter)
import Data.Function (on)
import Data.Hashable
import Data.Binary
import Data.Maybe

import Text.Parsec hiding ((<|>), many, optional)

type ParsecK = forall st m s. Stream s m Char => ParsecT s st m T.Text

data Macro = Macro
  { macroDefinition :: {-# UNPACK #-} !T.Text
  , macroKatexOnly  :: Bool
  , macroParser     :: ParsecK
  }

newtype Preamble = Preamble { getPreamble :: [Macro] }
  deriving (Eq, Show, Hashable, Binary, NFData)

preambleToLatex :: Preamble -> T.Text
preambleToLatex (Preamble ms) = T.unlines $ map macroDefinition $ filter (not . macroKatexOnly) ms

applyPreamble :: Preamble -> T.Text -> T.Text
applyPreamble (Preamble pre) = applyMacros pre

instance Eq Macro where
  (==) = (==) `on` macroDefinition

instance Ord Macro where
  (<=) = (<=) `on` macroDefinition

instance Hashable Macro where
  hashWithSalt s = hashWithSalt s . macroDefinition

instance Binary Macro where
  put m = do
    put (macroKatexOnly m)
    put (macroDefinition m)
  get = do
    kao <- get
    def <- get
    case parse pMacroDefinition (show def) (def :: T.Text) of
      Right m -> pure $ m { macroKatexOnly = kao }
      Left e -> error $ "Binary Macro: failed to parse serialized Macro?\n" ++ show e

instance NFData Macro where
  rnf (Macro a k _) = rnf (a,k)

instance Show Macro where
  show m = "Macro " ++ show (macroDefinition m)

-- | Parses a string for a list of macro definitions, optionally
-- separated and ended by spaces and TeX comments.  Returns
-- the list of macros (which may be empty) and the unparsed
-- portion of the input string.
parsePreamble :: T.Text -> Maybe Preamble
parsePreamble = (Preamble <$>) . either (const Nothing) Just . parseMacroMacro
  -- case parse pMacroDefinitions "input" s of
  --   Left _       -> Nothing
  --   Right (m, _) -> Just (Preamble m)

-- | Applies a list of macros to a string recursively until a fixed
-- point is reached.  If there are several macros in the list with the
-- same name, earlier ones will shadow later ones.
applyMacros :: [Macro] -> T.Text -> T.Text
applyMacros [] s = s
applyMacros ms s = fromMaybe s $
  iterateToFixedPoint ((2 * length ms) + 1) (applyMacrosOnce ms) s

------------------------------------------------------------------------------

pSkipSpaceComments :: (Monad m, Stream s m Char)
                   => ParsecT s st m String
pSkipSpaceComments = many space <* skipMany (comment >> spaces)

pMacroDefinitions :: (Monad m, Stream s m Char)
                  => ParsecT s st m ([Macro], s)
pMacroDefinitions = do
  _ <- pSkipSpaceComments
  defs <- sepEndBy pMacroDefinition pSkipSpaceComments
  rest <- getInput
  return (reverse defs, rest)  -- reversed so later macros shadow earlier

parseMacroMacro :: T.Text -> Either String [Macro]
parseMacroMacro s =
  case parse pMacroDefinitions (T.unpack s) s of
    Left e             -> error $
      "\nFailed to parse input:" <> T.unpack s <> "\n"
      <> show e
    Right (m@(_:_), r) -> (m ++) <$> parseMacroMacro (applyMacros m r)
    Right ([], _)      -> pure []

pMacroDefinition
  :: (Monad m, Stream s m Char)
  => ParsecT s st m Macro
pMacroDefinition =
  newcommand
  <|> declareMathOperator
  <|> newenvironment
  <|> newalphabet
  <|> try (char '{') *> pMacroDefinition <* char '}'

iterateToFixedPoint :: (Eq a, MonadFail m) => Int -> (a -> m a) -> a -> m a
iterateToFixedPoint 0 _ _ = fail "Macro application did not terminate"
iterateToFixedPoint limit f x = do
  y <- f x
  if y == x
    then pure y
    else iterateToFixedPoint (limit - 1) f y

applyMacrosOnce :: MonadFail m => [Macro] -> T.Text -> m T.Text
applyMacrosOnce ms s = do
  ts <- runParserT (many tok) () "input" s
  case ts of
    Right r -> pure $ T.concat r
    Left e  -> fail (show e)
  where
    tok :: Monad m => ParsecT T.Text () m T.Text
    tok = try $ do
      skipComment
      choice
        [ choice (map (\m -> macroParser m) ms)
        , csname tok
        , T.pack <$> ctrlseq
        , T.pack <$> count 1 anyChar
        ]

csname :: (Monad m, Stream s m Char) => ParsecT s st m T.Text -> ParsecT s st m T.Text
csname tok = do
  _ <- try $ string "\\csname"
  spaces
  t <- manyTill tok $ try (string "\\endcsname")
  pure $ T.cons '\\' $ T.concat t

ctrlseq :: (Monad m, Stream s m Char)
        => ParsecT s st m String
ctrlseq = do
  _ <- char '\\'
  res <- many1 letter <|> count 1 anyChar
  return $ '\\' : res

newalphabet :: (Monad m, Stream s m Char)
            => ParsecT s st m Macro
newalphabet = try $ do
  _ <- string "\\definealphabet"
  startc <- char '{' *> letter <* char '}'
  cseq <- char '{' *> ctrlseq <* char '}'
  start <- char '{' *> letter <* char '}'
  end   <- char '{' *> letter <* char '}'
  guard (end >= start)

  let
    def = T.pack $ concat ["\\definealphabet{", [startc], "}{", cseq, "}{", [start, '}', '{', end, '}']]

    parsec :: ParsecK
    parsec = try $ do
      _ <- string ['\\', startc]
      t <- letter
      guard (t >= start && t <= end)
      pure (T.pack (cseq ++ ['{', t, '}']))

  pure $ Macro def False parsec

newcommand :: (Monad m, Stream s m Char)
           => ParsecT s st m Macro
newcommand = try $ do
  _ <- char '\\'
  -- we ignore differences between these so far:
  cmd <- try (string "newcommand")
    <|> try (string "renewcommand")
    <|> string "providecommand"
  _ <- optional (char '*')

  _ <- pSkipSpaceComments
  name <- inbraces <|> ctrlseq
  guard (take 1 name == "\\")
  let name' = drop 1 name
  numargs <- numArgs
  _ <- pSkipSpaceComments

  optarg <- if numargs > 0
    then optArg
    else return Nothing

  let
    numargs' = case optarg of
      Just _  -> numargs - 1
      Nothing -> numargs

  _ <- pSkipSpaceComments
  kao <- isJust <$> optionMaybe (try (string "\\katex"))
  body <- inbraces <|> ctrlseq
  let
    defn = '\\':cmd ++ "{" ++ name ++ "}" ++
      (if numargs > 0 then "[" ++ show numargs ++ "]" else "") ++
      case optarg of { Nothing -> ""; Just x -> "[" ++ x ++ "]"} ++
      "{" ++ body ++ "}"

    parsec :: ParsecK
    parsec = fmap T.pack $ try $ do
      _ <- char '\\'
      _ <- string name'
      when (all isLetter name') $
        notFollowedBy letter
      spc <- pSkipSpaceComments
      opt <- case optarg of
                  Nothing  -> return Nothing
                  Just _   -> (`mplus` optarg) <$> optArg
      args <- count numargs' (pSkipSpaceComments >>
                    (inbraces <|> ctrlseq <|> count 1 anyChar))
      let args' = case opt of
                      Just x  -> x : args
                      Nothing -> args
      return $ apply args' $ body ++ spc

  return $ Macro (T.pack defn) kao parsec

newenvironment :: (Monad m, Stream s m Char)
               => ParsecT s st m Macro
newenvironment = try $ do
  _ <- char '\\'
  -- we ignore differences between these so far:
  _ <- optional (string "re")
  _ <- string "newenvironment"
  _ <- optional (char '*')
  _ <- pSkipSpaceComments
  name <- inbraces <|> ctrlseq
  numargs <- numArgs
  _ <- pSkipSpaceComments

  optarg <- if numargs > 0
    then optArg <* pSkipSpaceComments
    else return Nothing

  let
    numargs' =
      case optarg of
        Just _  -> numargs - 1
        Nothing -> numargs

  opener <- inbraces <|> ctrlseq
  _ <- pSkipSpaceComments
  closer <- inbraces <|> ctrlseq
  let
    defn = "\\newenvironment{" ++ name ++ "}" ++
      (if numargs > 0 then "[" ++ show numargs ++ "]" else "") ++
      case optarg of { Nothing -> ""; Just x -> "[" ++ x ++ "]"} ++
      "%\n{" ++ opener ++ "}%\n" ++ "{" ++ closer ++ "}"

    parsec :: ParsecK
    parsec = fmap T.pack $ try $ do
      _ <- string "\\begin"
      _ <- pSkipSpaceComments
      _ <- char '{'
      _ <- string name
      _ <- pSkipSpaceComments
      _ <- char '}'
      opt <- case optarg of
        Nothing  -> return Nothing
        Just _   -> (`mplus` optarg) <$> optArg
      args <- count numargs' (pSkipSpaceComments >>
                    (inbraces <|> ctrlseq <|> count 1 anyChar))
      let
        args' = case opt of
          Just x  -> x : args
          Nothing -> args
        ender = try $ do
          _ <- string "\\end"
          _ <- pSkipSpaceComments
          _ <- char '{'
          _ <- string name
          char '}'
      body <- manyTill anyChar ender
      return $ apply args'
             $ opener ++ body ++ closer

  return $ Macro (T.pack defn) False parsec

-- | Parser for \DeclareMathOperator(*) command.
declareMathOperator :: (Monad m, Stream s m Char)
                    => ParsecT s st m Macro
declareMathOperator = try $ do
  _ <- string "\\DeclareMathOperator"
  _ <- pSkipSpaceComments
  star <- option "" (string "*")
  _ <- pSkipSpaceComments
  name <- inbraces <|> ctrlseq
  guard (take 1 name == "\\")
  let name' = drop 1 name
  _ <- pSkipSpaceComments
  body <- inbraces <|> ctrlseq
  let
    defn = "\\DeclareMathOperator" ++ star ++ "{" ++ name ++ "}" ++
           "{" ++ body ++ "}"

    parsec :: ParsecK
    parsec = fmap T.pack $ try $ do
      _ <- char '\\'
      _ <- string name'
      when (all isLetter name') $
        notFollowedBy letter
      _ <- pSkipSpaceComments
      return $ "\\operatorname" ++ star ++ "{" ++ body ++ "}"

  return $ Macro (T.pack defn) False parsec

apply :: [String] -> String -> String
apply args ('#':d:xs) | isDigit d, d /= '0' =
  let argnum = read [d]
  in  if length args >= argnum
         then args !! (argnum - 1) ++ apply args xs
         else '#' : d : apply args xs
apply args ('\\':'#':xs) = '\\':'#' : apply args xs
apply args (x:xs) = x : apply args xs
apply _ "" = ""

skipComment :: (Monad m, Stream s m Char)
            => ParsecT s st m ()
skipComment = skipMany comment

comment :: (Monad m, Stream s m Char)
        => ParsecT s st m ()
comment = do
  _ <- char '%'
  skipMany (notFollowedBy newline >> anyChar)
  _ <- newline
  return ()

numArgs :: (Monad m, Stream s m Char)
        => ParsecT s st m Int
numArgs = option 0 $ try $ do
  _ <- pSkipSpaceComments
  _ <- char '['
  _ <- pSkipSpaceComments
  n <- digit
  _ <- pSkipSpaceComments
  _ <- char ']'
  return $ read [n]

optArg :: (Monad m, Stream s m Char)
       => ParsecT s st m (Maybe String)
optArg = option Nothing (Just <$> inBrackets)

escaped :: (Monad m, Stream s m Char)
         => String -> ParsecT s st m String
escaped xs = try $ char '\\' >> oneOf xs >>= \x -> return ['\\',x]

inBrackets :: (Monad m, Stream s m Char)
           => ParsecT s st m String
inBrackets = try $ do
  _ <- char '['
  _ <- pSkipSpaceComments
  res <- manyTill (skipComment >> (escaped "[]" <|> count 1 anyChar))
          (try $ pSkipSpaceComments >> char ']')
  return $ concat res

inbraces :: (Monad m, Stream s m Char)
         => ParsecT s st m String
inbraces = try $ do
  _ <- char '{'
  res <- manyTill (skipComment >>
            (inbraces' <|> count 1 anyChar <|> escaped "{}"))
    (try $ skipComment >> char '}')
  return $ concat res

inbraces' :: (Monad m, Stream s m Char)
          => ParsecT s st m String
inbraces' = do
  res <- inbraces
  return $ '{' : (res ++ "}")
