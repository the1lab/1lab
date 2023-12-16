{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BlockArguments #-}
module IdInfo
  ( HoTTBookRefKind(..)
  , HoTTBookRef(..)
  , LabPragma(..), labPragmas

  , DefInfo
  , defiName, defiAnchor, defiPragmas, defiType

  , IdInfoMap
  , parseIdInfo, typeToText
  , saveIdInfo
  , allIdInfo
  , labInfoDir

  , identifiers

  , definitionAnchor
  , parseRoman
  )
  where

import Text.Parsec hiding ((<|>))
import Control.Applicative
import Control.Monad.IO.Class
import Control.Exception hiding (try)
import Text.Read (readMaybe)
import Agda.Syntax.Common.Pretty (Pretty(..), render)
import Agda.TypeChecking.Pretty (PrettyTCM(..))
import GHC.Generics (Generic)
import Data.Binary
import qualified Data.Text as Text
import Data.Text (Text)
import Agda.Syntax.Common
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.IORef
import Agda.Compiler.Backend
import Data.Foldable
import Control.Monad
import qualified System.Directory as Dir
import System.FilePath
import Agda.Syntax.TopLevelModuleName
import Development.Shake
import Agda.Syntax.Position
import HTML.Base (modToFile)
import Data.Traversable
import Shake.Modules
import Control.Lens hiding ((<.>), anyOf)
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Concrete as Con
import qualified Agda.Syntax.Concrete.Generic as Con
import Data.List.NonEmpty (NonEmpty((:|)))
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.Syntax.Info (exprNoRange)
import qualified Agda.Syntax.Internal.Generic as I

data HoTTBookRefKind = Definition | Theorem | Lemma | Exercise | Example | Corollary | Remark
  deriving (Eq, Show, Bounded, Enum, Generic)
  deriving anyclass (Binary)

data HoTTBookRef = HoTTBookRef
  { _hottRefKind    :: HoTTBookRefKind
  , _hottRefChapter :: !Int
  , _hottRefSection :: !Int
  , _hottRefItem    :: !Int
  , _hottRefBullet  :: Maybe Int
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (Binary)

data LabPragma
  = FoldPragma
  -- ^ Register an identifier as being folded.
  | HoTTBookPragma HoTTBookRef
  -- ^ Register an identifer as corresponding to a given thing in the
  -- HoTT book.
  deriving (Eq, Show, Generic)
  deriving anyclass (Binary)

type Parser = Parsec String ()

instance Pretty LabPragma where
  pretty = pretty . show

hottBookRefKind :: Parser HoTTBookRefKind
hottBookRefKind = choice [ it <$ try (string (show it)) | it <- [minBound..maxBound] ]

spaces1 :: Parser ()
spaces1 = skipMany1 space

anyOf :: String -> Parser Char
anyOf = choice . map char

number :: Parser Int
number = (do
  dig <- many1 digit
  case readMaybe dig of
    Just x  -> pure x
    Nothing -> fail "not an integer") <?> "an integer"

roman :: Parser Int
roman = parseRoman <$> many1 (anyOf "ivxlcdm")

parseRoman :: String -> Int
parseRoman xs = p + l where
  digit 'i' = 1
  digit 'v' = 5
  digit 'x' = 10
  digit 'l' = 50
  digit 'c' = 100
  digit 'd' = 500
  digit 'm' = 1000
  digit _   = undefined

  accumulate (p, l) n
    | n <= l = (p + l, n)
    | otherwise = (p - l, n)

  (p, l) = foldl' accumulate (0, 0) (map digit xs)

hottBookRef :: Parser HoTTBookRef
hottBookRef = do
  ki   <- hottBookRefKind <* spaces1
  chap <- number <* char '.'
  sect <- number <* char '.'
  item <- number
  sub <- optionMaybe (try (char '.' *> roman))
  pure $ HoTTBookRef
    { _hottRefKind    = ki
    , _hottRefChapter = chap
    , _hottRefSection = sect
    , _hottRefItem    = item
    , _hottRefBullet  = sub
    }

labPragma :: Parser [LabPragma]
labPragma =
      [FoldPragma] <$ string "fold"
  <|> map HoTTBookPragma <$> (string "HoTT:" *> spaces1 *> (hottBookRef <* spaces) `sepBy1` (char ',' <* spaces))

labPragmas :: Parser [LabPragma]
labPragmas = concat <$> (spaces *> labPragma) `sepBy1` (char ';' *> spaces)

data PragmaParseException = PragmaParseException { _ppeSource :: String, _ppeErr :: ParseError }
  deriving stock (Show)
  deriving anyclass (Exception)

data DefInfo = DefInfo
  { _defiPrettyName :: Text
  , _defiAnchor     :: Text
  , _defiType       :: Text
  , _defiPragmas    :: [LabPragma]
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (Binary)

newtype IdInfoMap = IdInfoMap { getLabPragmas :: Map (Word64, Word64) DefInfo }
  deriving newtype (Semigroup, Monoid, Binary)

instance Pretty IdInfoMap where
  pretty = pretty . Map.foldr go mempty . getLabPragmas where
    go :: DefInfo -> Map Text [LabPragma] -> Map Text [LabPragma]
    go di = Map.insert (_defiPrettyName di) (_defiPragmas di)

instance Show IdInfoMap where
  show = render . pretty

insertPragmas :: Definition -> Text -> [LabPragma] -> IdInfoMap -> IdInfoMap
insertPragmas def ty [] x = x
insertPragmas def ty xs (IdInfoMap m) | Just anchor <- definitionAnchor def = do
  let
    nm = Text.pack . render . pretty . qnameName . defName
    QName _ (Name (NameId key (ModuleNameHash hash)) _ _ _ _ _) = defName def
    m' = Map.insert (key, hash) DefInfo
      { _defiPrettyName = nm def
      , _defiPragmas    = xs
      , _defiAnchor     = anchor
      , _defiType       = ty
      }
      m
  IdInfoMap m'
insertPragmas _ _ _ m = m

definitionAnchor :: Definition -> Maybe Text
definitionAnchor def | defCopy def = Nothing
definitionAnchor def = f =<< go where
  go :: Maybe FilePath
  go = do
    let name = defName def
    case rangeModule (nameBindingSite (qnameName name)) of
      Just f -> Just (modToFile f "html")
      Nothing -> Nothing
  f modn =
    case rStart (nameBindingSite (qnameName (defName def))) of
      Just pn -> pure $ Text.pack (modn <> "#" <> show (posPos pn))
      Nothing -> Nothing

parseIdInfo :: Definition -> IORef IdInfoMap -> TCM (Maybe Text)
parseIdInfo def dest = do
  let
    parseP (CompilerPragma _ prg) = case parse labPragmas "pragmas" prg of
      Right x -> pure x
      Left e -> liftIO $ throwIO $ PragmaParseException prg e
  prgs <- fold <$> traverse parseP (defCompilerPragmas "1Lab" def)
  case prgs of
    [] -> pure Nothing
    _ -> do
      ty <- typeToText def
      liftIO $ atomicModifyIORef' dest $ \m -> (insertPragmas def ty prgs m, ())
      pure (Just ty)

labInfoDir :: FilePath
labInfoDir = "_build/info"

saveIdInfo :: TopLevelModuleName -> IdInfoMap -> IO ()
saveIdInfo _ (IdInfoMap m) | Map.null m = pure ()
saveIdInfo modn m = do
  Dir.createDirectoryIfMissing False labInfoDir
  encodeFile (labInfoDir </> modToFile modn "bin") m

allIdInfo :: Action IdInfoMap
allIdInfo = do
  agda <- getAllModules >>= \modules ->
    pure ["_build/html0" </> f <.> "json" | (f, _) <- Map.toList modules]
  need agda
  fs <- liftIO (getDirectoryFilesIO labInfoDir ["*.bin"])
  liftIO $ print fs
  let log x = x <$ liftIO (print x)
  traced "decoding" $
    fold <$> traverse (log <=< decodeFile . (labInfoDir </>)) fs

identifiers :: Fold IdInfoMap DefInfo
identifiers = folding (Map.elems . getLabPragmas)

defiName :: Lens' DefInfo Text
defiName f di = f (_defiPrettyName di) <&> \x -> di{ _defiPrettyName = x }

defiAnchor :: Lens' DefInfo Text
defiAnchor f di = f (_defiAnchor di) <&> \x -> di{ _defiAnchor = x }

defiType :: Lens' DefInfo Text
defiType f di = f (_defiType di) <&> \x -> di{ _defiType = x }

defiPragmas :: Lens' DefInfo [LabPragma]
defiPragmas f di = f (_defiPragmas di) <&> \x -> di{ _defiPragmas = x }

prettifyTerm :: I.Type -> I.Type
prettifyTerm = runIdentity . I.traverseTermM unDomName where
  unDomName :: I.Term -> Identity I.Term
  unDomName (I.Pi d x) = pure $ I.Pi d{I.domName = Nothing} x
  unDomName (I.Def q x) = pure $ I.Def q{qnameModule = MName []} x
  unDomName x = pure x

killQual :: Con.Expr -> Con.Expr
killQual = Con.mapExpr wrap where
  work :: Con.QName -> Con.QName
  work (Con.Qual _ x) = work x
  work x = x

  wrap :: Con.Expr -> Con.Expr
  wrap (Con.Ident v)              = Con.Ident (work v)
  wrap (Con.KnownIdent v w)       = Con.KnownIdent v (work w)
  wrap (Con.KnownOpApp v w x y z) = Con.KnownOpApp v w (work x) y z
  wrap (Con.OpApp v w x y)        = Con.OpApp v (work w) x y
  wrap x = x

typeToText :: Definition -> TCM Text
typeToText d = do
  expr <- reify . prettifyTerm $ defType d
  fmap (Text.pack . render . pretty . killQual) .
    abstractToConcrete_ . removeImpls $ expr

removeImpls :: A.Expr -> A.Expr
removeImpls (A.Pi _ (x :| xs) e) =
  makePi (map (A.mapExpr removeImpls) $ filter ((/= Hidden) . getHiding) (x:xs)) (removeImpls e)
removeImpls (A.Fun span arg ret) =
  A.Fun span (removeImpls <$> arg) (removeImpls ret)
removeImpls e = e

makePi :: [A.TypedBinding] -> A.Expr -> A.Expr
makePi [] = id
makePi (b:bs) = A.Pi exprNoRange (b :| bs)
