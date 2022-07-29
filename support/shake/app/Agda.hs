module Agda where

import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import Control.Monad.IO.Class
import Agda.Utils.FileName
import Agda.TypeChecking.Errors
import Control.Monad.Error
import Control.Monad

import System.FilePath

runAgda :: CommandLineOptions -> (String -> TCMT IO a) -> IO a
runAgda opts k = do
  e <- runTCMTop $ do
    p <- setupTCM opts
    (k p
      `catchError` \err -> do
        s2s <- prettyTCWarnings' =<< getAllWarningsOfTCErr err
        s1  <- prettyError err
        let ss = filter (not . null) $ s2s ++ [s1]
        unless (null s1) (error $ unlines ss)
        return undefined)
  case e of
    Left s -> error (tcErrString s)
    Right x -> pure x

setupTCM :: CommandLineOptions -> TCMT IO String
setupTCM options = do
  file <- case optInputFile options of
    Nothing -> error "No input files."
    Just x -> liftIO . absolute $ takeDirectory x

  setCommandLineOptions' file options
  pure (filePath file)
