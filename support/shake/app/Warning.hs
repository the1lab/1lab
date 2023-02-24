module Warning (putWarning, flushWarnings) where

import System.IO.Unsafe
import System.Exit

import Control.Concurrent.MVar
import Control.Exception
import Control.Monad

import Development.Shake

{-# NOINLINE warnings #-}
warnings :: MVar [String]
warnings = unsafePerformIO $ newMVar []

flushWarnings :: IO ()
flushWarnings = do
  have <- takeMVar warnings
  unless (null have) $ do
    throwIO $ userError $ "The following warnings were encountered:\n"
                       ++ unlines (map ("  " ++ ) (reverse have))

putWarning :: String -> Action ()
putWarning s = do
  liftIO $ do
    modifyMVar_ warnings (pure . (s:))
    putStrLn $ "WARNING: " ++ s
  alwaysRerun
