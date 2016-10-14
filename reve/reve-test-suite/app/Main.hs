{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Config
import Control.Concurrent.Async
import Control.Exception
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Reader
import Control.Monad.Trans.Control
import Data.List
import qualified Data.Map as M
import Data.Monoid
import Data.Yaml
import Options
import Options.Applicative hiding ((<>), (<$>))
import Orphans ()
import Pipes.Concurrent
import Pipes.Safe hiding (catch)
import System.Directory
import System.Environment
import System.FilePath
import System.IO.Error
import Workers

ignoredJavaOpts :: [String]
ignoredJavaOpts =
  ["-Dawt.useSystemAAFontSettings=", "-Dswing.aatext=", "-Dswing.defaultlaf="]

resetJavaOpts :: IO ()
resetJavaOpts = do
  opts <- lookupEnv "_JAVA_OPTIONS"
  case fmap
         (filter (\opt -> not $ any (`isPrefixOf` opt) ignoredJavaOpts) . words)
         opts of
    Nothing -> pure ()
    Just [] -> unsetEnv "_JAVA_OPTIONS"
    Just opts' -> setEnv "_JAVA_OPTIONS" (unwords opts')

main :: IO ()
main = do
  opts <- execParser optParser
  conf' <- decodeFileEither (optConfig opts) >>= either throwM return
  let conf =
        conf' & cnfCustomArgs %~ M.mapKeys (optBuild opts </>) &
        cnfCustomEldArgs %~
        M.mapKeys (optBuild opts </>)
  removeDirectoryRecursive (optBuild opts) `catch`
    (\(e :: IOError) -> when (not $ isDoesNotExistError e) (throwIO e))
  resetJavaOpts
  (output, input, seal) <- spawn' (bounded (optProcesses opts))
  (mergeOutput, mergeInput, mergeSeal) <- spawn' (bounded (optProcesses opts))
  runSafeT .
    flip runReaderT (opts, conf) .
    runStderrLoggingT .
    filterLogger (\_source level -> (optVerbose opts) || level > LevelDebug) $ do
    a <- liftBaseDiscard async $ smtGeneratorWorker output seal
    as <-
      forM [(1 :: Int) .. (optProcesses opts)] $
      const $ liftBaseDiscard async $ solverWorker input seal mergeOutput
    b <- liftBaseDiscard async $ outputWorker mergeInput mergeSeal
    liftIO $ mapM_ wait (a : as)
    liftIO $ atomically mergeSeal
    liftIO $ wait b
  where
    optParser =
      info
        (helper <*> optionParser)
        (fullDesc <> progDesc "Test all examples" <> header "reve-test-suite")
