module Main where

import Control.Concurrent.Async
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Trans.Control
import Data.List
import Data.Monoid
import Options
import Options.Applicative hiding ((<>),(<$>))
import Orphans ()
import Pipes.Concurrent
import Pipes.Safe
import System.Environment
import Workers


ignoredJavaOpts :: [String]
ignoredJavaOpts = ["-Dawt.useSystemAAFontSettings=","-Dswing.aatext=","-Dswing.defaultlaf="]

resetJavaOpts :: IO ()
resetJavaOpts =
  do opts <- lookupEnv "_JAVA_OPTIONS"
     case fmap (filter (\opt -> not $ any (`isPrefixOf` opt) ignoredJavaOpts) . words) opts of
       Nothing -> pure ()
       Just [] -> unsetEnv "_JAVA_OPTIONS"
       Just opts' -> setEnv "_JAVA_OPTIONS" (unwords opts')


main :: IO ()
main =
  do parsedOpts <- execParser opts
     resetJavaOpts
     (output,input,seal) <- spawn' unbounded
     (mergeOutput,mergeInput,mergeSeal) <- spawn' unbounded
     runSafeT .
       runStderrLoggingT .
       filterLogger
         (\_source level -> (optVerbose parsedOpts) || level > LevelDebug) $
       do a <-
            liftBaseDiscard async $
            smtGeneratorWorker (optExamples parsedOpts)
                               (optBuild parsedOpts)
                               (optReve parsedOpts)
                               output
                               seal
          as <-
            forM [(1 :: Int) .. (optProcesses parsedOpts)] $
            const $ liftBaseDiscard async $
            solverWorker input
                         seal
                         mergeOutput
                         mergeSeal
                         (optEldarica parsedOpts)
          b <-
            liftBaseDiscard async $ outputWorker mergeInput mergeSeal
          liftIO $ mapM_ wait (a : b : as)
  where opts =
          info (helper <*> optionParser)
               (fullDesc <> progDesc "Test all examples" <>
                header "reve-test-suite")
