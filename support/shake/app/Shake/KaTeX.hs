{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Shake rules to compile equations to HTML with KaTeX
module Shake.KaTeX
  ( katexRules
  , getDisplayMath
  , getInlineMath
  , prerenderMaths

  , getParsedPreamble
  , getPreambleFor
  ) where

import Control.Applicative
import Control.Monad

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Map.Strict as Map
import qualified Data.Text.Lazy as LT
import qualified Data.Aeson as Aeson
import qualified Data.Text.IO as T
import qualified Data.Text as T
import Data.Aeson (FromJSON(..), (.:), (.=))
import Data.Text (Text)
import Data.Generics
import Data.Foldable


import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

import Control.Concurrent.Chan
import Control.Exception

import System.Process qualified as Process
import System.IO

import Shake.Utils
import Macros

newtype LatexEquation = LatexEquation (Bool, Text)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

newtype LatexPreamble = LatexPreamble Bool
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

newtype ParsedPreamble = ParsedPreamble ()
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult LatexEquation = Text
type instance RuleResult LatexPreamble = Text
type instance RuleResult ParsedPreamble = Preamble

-- | Convert a display/block-level LaTeX equation to HTML.
getDisplayMath :: Text -> Action Text
getDisplayMath contents = askOracle (LatexEquation (True, contents))

-- | Convert an inline LaTeX equation to HTML.
getInlineMath :: Text -> Action Text
getInlineMath contents = askOracle (LatexEquation (False, contents))

prerenderMaths :: [Text] -> [Text] -> Action ()
prerenderMaths display inline = void . askOracles $ [LatexEquation (True, c) | c <- display] <> [LatexEquation (False, c) | c <- inline]

-- | Get the preamble for a given build ('True' = dark mode)
getPreambleFor :: Bool -> Action Text
getPreambleFor = askOracle . LatexPreamble

-- | Get parsed preamble
getParsedPreamble :: Action Preamble
getParsedPreamble = askOracle $ ParsedPreamble ()

-- * LaTeXML Worker Queues

-- | The handles associated to a katex-worker process.
data KatexWorker = KatexWorker
  { katexWorkerIn :: Handle
  -- ^ Stdin of the katex-worker process.
  , katexWorkerOut :: Handle
  -- ^ Stdout of the katex-worker process.
  , katexWorkerErr :: Handle
  -- ^ Stderr of the katex-worker process.
  }

-- | Spawn a single katex-worker process.
-- If we cannot spawn the process for whatever reason, 'spawnLatexWorker' throws an exception via 'fail'.
spawnKatexWorker :: IO KatexWorker
spawnKatexWorker =
  Process.createProcess workerSpec >>= \case
  (Just katexWorkerIn, Just katexWorkerOut, Just katexWorkerErr, _) ->
    pure (KatexWorker { .. })
  _ -> fail "Spawning katex-worker process failed."
  where
    workerSpec =
      -- FIXME: This aint the right way to do this.
      (Process.proc "./support/katex/katex-worker.js" [])
        { Process.cwd = Nothing
        , Process.std_in = Process.CreatePipe
        , Process.std_out = Process.CreatePipe
        , Process.std_err = Process.CreatePipe
        }

-- | Create a FIFO queue of katex-worker processes.
createKatexWorkerQueue
  :: Int                -- ^ Number of processes to spawn.
  -> IO (Chan KatexWorker)
createKatexWorkerQueue numWorkers = do
  workers <- newChan
  for_ [0..numWorkers] $ \i -> do
    worker <- spawnKatexWorker
    writeChan workers worker
  pure workers

-- | Remove a worker from a worker queue for a given job type
-- and run the provided IO action with that worker.
-- Once completed, return the worker to the queue.
withKatexWorker
  :: Chan KatexWorker
  -> (KatexWorker -> IO a)
  -> IO a
withKatexWorker workerQueue k =
  bracket (readChan workerQueue) (writeChan workerQueue) k

-- | Encode a 'LatexEquation' into a @katex-worker@ job.
encodeKatexJob :: Bool -> Text -> Aeson.Value
encodeKatexJob display tex =
  Aeson.object
  [ "equation" .= tex
  , "options" .=
    Aeson.object
    [ "displayMode" .= display
    , "output" .= ("html" :: Text)
    , "trust" .= True
    ]
  ]

-- | Shake rules required for compiling KaTeX equations.
katexRules :: Rules ()
katexRules = versioned 3 do
  numThreads <- shakeThreads <$> getShakeOptionsRules
  workerQueue <- liftIO $ createKatexWorkerQueue numThreads

  _ <- addOracle \(ParsedPreamble _) -> do
    need ["src/preamble.tex"]
    t <- liftIO $ T.readFile "src/preamble.tex"
    case parsePreamble t of
      Just p -> pure p
      Nothing -> error "Failed to parse preamble.tex!"

  _ <- addOracleCache \(LatexPreamble bool) -> do
    pre <- askOracle (ParsedPreamble ())
    let dark = if bool then darkSettings else mempty
    pure (preambleToLatex pre <> T.pack "\n" <> dark)

  _ <- versioned 3 $ addOracleCache \(LatexEquation (display, tex)) -> do
    pre <- askOracle (ParsedPreamble ())
    result <-
      traced "katex" $
      withKatexWorker workerQueue \KatexWorker{..} ->
      handle (\(SomeException e) -> pure (T.pack $ displayException e)) $ do
        -- [HACK: File Separator Control Characters].
        -- Instead of trying to do some fiddly JSON streaming, we opt to
        -- use a little known feature of ASCII to delimit our requests.
        -- The control character 0x1C in ASCII encodes a file-separator,
        -- which is left up to applications to interpret. We can rely on this never showing up
        -- in our JSON, so it is safe to use this to delimit requests.
        let job = Aeson.encode (encodeKatexJob display (applyPreamble pre tex)) <> "\FS"
        LBS.hPutStr katexWorkerIn job
        hFlush katexWorkerIn
        -- We can't use 'LBS.takeWhile (0x1c /=)' here, as the output can contain utf8-encoded
        -- text. To avoid this, we first decode to utf8.
        LT.toStrict <$> LT.takeWhile ('\FS' /=) <$> LT.decodeUtf8With T.strictDecode <$> LBS.hGetContents katexWorkerOut
    case T.stripPrefix "Ok:" result of
      Just html -> pure (T.strip html)
      Nothing -> error (T.unpack result)

  pure ()

darkSettings :: Text
darkSettings = T.pack "\\newcommand{\\labdark}{yes!}"
