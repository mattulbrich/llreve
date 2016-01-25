module Workers
  (solverWorker,smtGeneratorWorker,outputWorker) where

import           Config
import           Control.Monad.Logger
import           Options
import           Output
import           Pipes
import           Pipes.Concurrent
import           Pipes.Files as P
import qualified Pipes.Prelude as P hiding (find)
import           Pipes.Safe
import           Process
import           Text.PrettyPrint.ANSI.Leijen (putDoc)
import           Types

solverWorker :: (MonadLogger m,MonadSafe m)
             => Options -> Input FilePath -> STM () -> Output (FilePath,Status) -> STM () -> m ()
solverWorker options input seal mergeOutput mergeSeal =
  flip finally (liftIO $ atomically (seal >> mergeSeal)) $ runEffect $
    fromInput input >-> P.mapM (solveSmt (optBuild options) (optEldarica options) (optZ3 options))
                    >-> toOutput mergeOutput

smtGeneratorWorker :: MonadSafe m
                   => Options -> Output FilePath -> STM () -> m ()
smtGeneratorWorker opts output seal =
  flip finally
  (liftIO $ atomically seal) $
  runEffect $
    P.find (optExamples opts)
           (when_ (filename_ (`elem` (ignoredDirectories ++ ignoredFiles))) prune_ >>
            glob "*_1.c") >->
    P.mapM (generateSmt opts) >->
    toOutput output

outputWorker :: MonadSafe m
             => Input (FilePath, Status) -> STM b -> m ()
outputWorker mergeInput mergeSeal = flip finally (liftIO $ atomically mergeSeal) $ runEffect $
  fromInput mergeInput >->
  P.map printResult >->
  P.mapM_ (liftIO . putDoc)
