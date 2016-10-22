{-# LANGUAGE FlexibleContexts #-}
module Workers
  (solverWorker
  ,smtGeneratorWorker
  ,outputWorker
  ) where

import           Config
import           Control.Lens hiding (ignored)
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Data.DirStream
import           Data.List
import           Data.String
import qualified Filesystem.Path.CurrentOS as F
import           Options
import           Output
import           Pipes
import           Pipes.Concurrent
import qualified Pipes.Prelude as P hiding (find)
import           Pipes.Safe
import           Process
import           System.FilePath
import           Text.PrettyPrint.ANSI.Leijen (putDoc)
import           Types

solverWorker :: (MonadLogger m, MonadSafe m, MonadReader (Options, Config) m)
             => Input FilePath -> STM () -> Output (FilePath,Status) -> m ()
solverWorker input seal mergeOutput =
  flip finally (liftIO (atomically seal)) $ runEffect $
    fromInput input >-> P.mapM solveSmt
                    >-> toOutput mergeOutput

smtGeneratorWorker :: (MonadSafe m, MonadReader (Options, Config) m, MonadLogger m)
                   => Output FilePath -> STM () -> m ()
smtGeneratorWorker output seal = do
  (opts, config) <- ask
  let ignored =
        map
          (fromString . (optExamples opts </>))
          (config ^. cnfIgnoredDirs ++ config ^. cnfIgnoredFiles)
  flip finally (liftIO (atomically seal)) $
    runEffect $
    every (sourceFiles ignored (fromString $ optExamples opts)) >->
    P.map F.encodeString >->
    P.mapM generateSmt >->
    toOutput output

sourceFiles :: (MonadSafe m) => [F.FilePath] -> F.FilePath -> ListT m F.FilePath
sourceFiles ignored path = do
  child <- childOf path
  guard (not $ child `elem` ignored)
  isDir <- liftIO $ isDirectory child
  if isDir
    then sourceFiles ignored child
    else do
      guard ("_1.c" `isSuffixOf` F.encodeString (F.filename child))
      return child

outputWorker :: MonadSafe m
             => Input (FilePath, Status) -> STM b -> m ()
outputWorker mergeInput mergeSeal = flip finally (liftIO (atomically mergeSeal)) $ runEffect $
  fromInput mergeInput >->
  P.map printResult >->
  P.mapM_ (liftIO . putDoc)
