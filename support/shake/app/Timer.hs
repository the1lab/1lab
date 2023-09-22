-- | A basic profiling library, for timing how long it takes to evaluate an
-- expression.
--
-- This works a little like Haskell's SCC (Set Cost Center): one uses `timed' or
-- `timedM' to give an expression a label. That expression is then timed and
-- added to the total time for each label.
{-# LANGUAGE BlockArguments #-}
module Timer
  ( timedM
  , timed
  , reportTimes
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Foldable
import Data.Maybe
import Data.IORef
import Data.Text (Text)

import Control.Monad.IO.Class
import Control.Exception
import Control.DeepSeq
import Control.Monad

import System.IO.Unsafe (unsafePerformIO)
import System.CPUTime

import Text.Printf

totalTimers :: IORef (Map.Map Text Integer)
totalTimers = unsafePerformIO (newIORef mempty)
{-# NOINLINE totalTimers #-}


-- | Time how long a computation takes to run, forcing the returned expression.
timedM :: (MonadIO m, NFData a) => Text -> m a -> m a
timedM label val = do
  start <- liftIO getCPUTime
  val <- val
  () <- liftIO (evaluate (rnf val))
  end <- liftIO getCPUTime

  let duration = end - start
  liftIO $ atomicModifyIORef totalTimers \timers ->
    let total = duration + fromMaybe 0 (Map.lookup label timers)
    in (Map.insert label total timers, ())

  pure val

-- | Time how long an expression takes to fully evaluate.
timed :: NFData a => Text -> a -> a
timed label val = unsafePerformIO (timedM label (pure val))
{-# NOINLINE timed #-}


-- | Print a table of all timings.
reportTimes :: MonadIO m => m ()
reportTimes = liftIO do
  times <- readIORef totalTimers
  unless (Map.null times) (reportTimes times)

  where
    formatPico :: Integer -> Float
    formatPico x = fromIntegral x * 1e-12

    reportTimes :: Map.Map Text Integer -> IO ()
    reportTimes times = do
      let
        max = maximum $ map Text.length $ Map.keys times
        fmt x = "%" ++ show max ++ "s | " ++ x
      printf (fmt "%10s\n") "Label" "Time (s)"
      printf (fmt "%10s\n") (replicate max '=') (replicate 10 '=')

      for_ (Map.toList times) \(label, time) ->
        printf (fmt "%10.2f\n") label (formatPico time)
