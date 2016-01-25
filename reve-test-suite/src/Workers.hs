module Workers
  (solverWorker,smtGeneratorWorker,outputWorker) where

import           Config
import           Control.Monad.Logger
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
             => Input FilePath -> STM () -> Output (FilePath,Status) -> STM () -> FilePath -> m ()
solverWorker input seal mergeOutput mergeSeal eldarica =
  flip finally (liftIO $ atomically (seal >> mergeSeal)) $ runEffect $
    (fromInput input >-> P.mapM (solveSmt eldarica) >-> toOutput mergeOutput)

smtGeneratorWorker :: MonadSafe m
                   => FilePath -> FilePath -> String -> Output FilePath -> STM () -> m ()
smtGeneratorWorker examples build reve output seal =
  flip finally
  (liftIO $ atomically seal) $
  runEffect $
    P.find examples
           (when_ (filename_ (`elem` (ignoredDirectories ++ ignoredFiles))) prune_ >>
            glob "*_1.c") >->
    P.mapM (generateSmt build reve examples) >->
    toOutput output

outputWorker :: MonadSafe m
             => Input (FilePath, Status) -> STM b -> m ()
outputWorker mergeInput mergeSeal = flip finally (liftIO $ atomically mergeSeal) $ runEffect $
  fromInput mergeInput >->
  P.map printResult >->
  P.mapM_ (liftIO . putDoc)
