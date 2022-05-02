module Agda where

import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import Control.Monad.IO.Class
import Agda.Utils.FileName

import System.FilePath

runAgda :: CommandLineOptions -> (String -> TCMT IO a) -> IO a
runAgda opts k = do
  e <- runTCMTop $ do
    p <- setupTCM opts
    k p
  case e of
    Left s -> error (show s)
    Right x -> pure x

setupTCM :: CommandLineOptions -> TCMT IO String
setupTCM options = do
  file <- case optInputFile options of
    Nothing -> error "No input files."
    Just x -> liftIO . absolute $ takeDirectory x

  setCommandLineOptions' file options
  pure (filePath file)
