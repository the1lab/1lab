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

import Control.Monad

import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text.Encoding.Error as T
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Lazy as LT
import qualified Data.Aeson as Aeson
import qualified Data.Text.IO as T
import qualified Data.Text as T
import Data.Aeson ((.=))
import Data.Text (Text)
import Data.Generics
import Data.Foldable
import Data.IORef

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

import Control.Concurrent.Chan
import Control.Exception

import System.Process qualified as Process
import System.Process (ProcessHandle)
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
  , katexWorkerResults :: IORef [Text]
  -- ^ Lazily produced stream of HTML chunks from the katex worker.
  , katexProcessHandle :: ProcessHandle
  }

-- | Spawn a single katex-worker process.
-- If we cannot spawn the process for whatever reason, 'spawnLatexWorker' throws an exception via 'fail'.
spawnKatexWorker :: IO KatexWorker
spawnKatexWorker =
  Process.createProcess workerSpec >>= \case
  (Just katexWorkerIn, Just katexWorkerOut, _, katexProcessHandle) -> do
    -- We are going to be delimiting requests with null bytes
    -- (See [NOTE: Delimiting KaTeX jobs]), so we can eek out a bit
    -- more performance by using block buffering over line buffering.
    hSetBuffering katexWorkerIn (BlockBuffering (Just 0x2000))
    hSetBuffering katexWorkerOut (BlockBuffering (Just 0x2000))
    -- [NOTE: Delimiting KaTeX jobs].
    -- Instead of trying to do some fiddly JSON streaming, we opt to
    -- delimit our requests with null bytes. This lets us avoid having to
    -- decode to unicode to determine where a job starts and ends, as 0x00 does not
    -- show up in any multibyte characters.
    bytes <- LBS.hGetContents katexWorkerOut
    let chunks = LT.toStrict . LT.stripEnd . LT.decodeUtf8With T.strictDecode <$> LBS.split 0x00 bytes
    katexWorkerResults <- newIORef chunks
    -- We will only ever read/write bytestrings, so we don't need to
    -- worry about setting handle encodings or dealing with newline conversion.
    pure (KatexWorker { .. })
  _ -> fail "Spawning katex-worker process failed."
  where
    workerSpec =
      (nodeProc "./support/katex/katex-worker.js" [])
        { Process.std_in = Process.CreatePipe
        , Process.std_out = Process.CreatePipe
        , Process.std_err = Process.Inherit
        -- We'd like to report fatal errors to the shake output directly,
        -- so we inherit stderr instead of creating a new pipe.
        }

-- | Create a FIFO queue of katex-worker processes.
createKatexWorkerQueue
  :: Int                -- ^ Number of processes to spawn.
  -> IO (Chan KatexWorker)
createKatexWorkerQueue numWorkers = do
  workers <- newChan
  for_ [0..numWorkers - 1] $ \_ -> do
    worker <- spawnKatexWorker
    writeChan workers worker
  pure workers

-- | Remove a worker from a worker queue for a and run the provided IO action with that worker.
-- Once completed, return the worker to the queue.
withKatexWorker
  :: Chan KatexWorker
  -> (KatexWorker -> IO a)
  -> IO a
withKatexWorker katexWorkerQueue =
  bracket (readChan katexWorkerQueue) (writeChan katexWorkerQueue)

-- | Submit a KaTeX rendering job to a worker.
submitKatexJob
  :: KatexWorker
  -- ^ Katex worker to pass the request to.
  -> Preamble
  -- ^ LaTeX preamble.
  -> LatexEquation
  -- ^ LaTeX to be rendered.
  -> IO ()
submitKatexJob KatexWorker{..} pre (LatexEquation (display, tex)) = do
  LBS.hPut katexWorkerIn $ Aeson.encode (encodeKatexJob display (applyPreamble pre tex)) <> "\NUL"
  hFlush katexWorkerIn

-- | Await the results of a KaTeX rendering job submitted via @submitKatexJob@.
-- If the KaTeX worker exited, return @Nothing@. Otherwise,
-- return a @Just@ containing the result.
awaitKatexResult
  :: KatexWorker
  -- ^ Katex worker we are waiting to respond.
  -> IO (Maybe Text)
awaitKatexResult KatexWorker{..} =
  -- Make sure to force the result text so we don't
  -- hold onto any portion of the output buffer of the process
  -- longer than we have to.
  atomicModifyIORef katexWorkerResults \case
    [] -> ([], Nothing)
    ((!r):rs) -> (rs, Just r)

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
  katexPool <- liftIO $ createKatexWorkerQueue numThreads

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

  _ <- versioned 3 $ addOracleCache \latex -> do
    pre <- askOracle (ParsedPreamble ())
    result <-
      quietly . traced "katex" $ withKatexWorker katexPool \katexWorker -> do
      submitKatexJob katexWorker pre latex
      awaitKatexResult katexWorker
    case result of
      Just html -> pure html
      Nothing -> fail "KaTeX worker exited unexpectedly."

  pure ()

darkSettings :: Text
darkSettings = T.pack "\\newcommand{\\labdark}{yes!}"
