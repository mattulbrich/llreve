{-# LANGUAGE FlexibleContexts #-}
module Workers
  (solverWorker
  ,smtGeneratorWorker
  ,outputWorker
  ) where

import           Config
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Options
import           Output
import           Pipes
import           Pipes.Concurrent
import           Pipes.Files as P
import qualified Pipes.Prelude as P hiding (find)
import           Pipes.Safe
import           Process
import           System.FilePath
import           Text.PrettyPrint.ANSI.Leijen (putDoc)
import           Types

solverWorker :: (MonadLogger m, MonadSafe m, MonadReader (Options, Config) m)
             => Input FilePath -> STM () -> Output (FilePath,Status) -> STM () -> m ()
solverWorker input seal mergeOutput mergeSeal =
  flip finally (liftIO $ atomically (seal >> mergeSeal)) $ runEffect $
    fromInput input >-> P.mapM solveSmt
                    >-> toOutput mergeOutput

smtGeneratorWorker :: (MonadSafe m, MonadReader (Options, Config) m)
                   => Output FilePath -> STM () -> m ()
smtGeneratorWorker output seal = do
  (opts,config) <- ask
  flip finally (liftIO $ atomically seal) $
    runEffect $
      P.find (optExamples opts)
               (when_ (pathname_ (`elem` (map (optExamples opts </>) $
                                            cnfIgnoredDirs config ++ cnfIgnoredFiles config)))
                        prune_ >>
                  glob "*_1.c") >->
      P.mapM (generateSmt opts) >->
      toOutput output

outputWorker :: MonadSafe m
             => Input (FilePath, Status) -> STM b -> m ()
outputWorker mergeInput mergeSeal = flip finally (liftIO $ atomically mergeSeal) $ runEffect $
  fromInput mergeInput >->
  P.map printResult >->
  P.mapM_ (liftIO . putDoc)
