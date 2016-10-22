{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
module Process
  (solveSmt,generateSmt) where

import           Config
import qualified Control.Exception as Ex
import qualified Control.Foldl as F
import           Control.Lens hiding (Fold1)
import           Control.Monad.IO.Class
import           Control.Monad.Logger
import           Control.Monad.Reader
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Text as T
import           Options
import           Pipes
import qualified Pipes.ByteString as PB
import           Pipes.Safe hiding (handle)
import qualified Pipes.Text as P hiding (find,map,last)
import qualified Pipes.Text.IO as PT
import qualified Pipes.Transduce.Text as PT
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO hiding (utf8)
import           System.Process
import           System.Process.Streaming
import           Types

solveSmt
  :: (MonadIO m, MonadSafe m, MonadLogger m, MonadReader (Options,Config) m)
  => FilePath -> m (FilePath,Status)
solveSmt smt = do
  (opts, conf) <- ask
  let baseName = dropFromEnd 5 smt -- remove '.smt2'
  if | baseName `elem` map (optBuild opts </>) (conf ^. cnfZ3Files) ->
       solveZ3 smt
     | baseName `elem` map (optBuild opts </>) (conf ^. cnfNativeZ3Files) ->
       solveNativeZ3 smt
     | otherwise -> solveEldarica (optEldarica opts) smt

utf8Lines :: Transducer Delimited P.ByteString e T.Text
utf8Lines = PT.lines PT.utf8x

foldUtf8Lines :: Fold1 T.Text e r -> Streams e r
foldUtf8Lines fold = foldOutErr (combined utf8Lines utf8Lines fold)

solveZ3
  :: ( Monad m
     , MonadIO m
     , MonadSafe m
     , MonadLogger m
     , MonadReader (Options, a) m
     )
  => FilePath -> m (FilePath, Status)
solveZ3 smt = do
  opts <- asks fst
  let simplifySMT handle =
        execute
          (piped $ proc (optEldarica opts) ["-t:300", "-sp", smt])
          (foldUtf8Lines (withConsumer (PT.toHandle handle)))
      smt' = smt <> ".z3"
  bracket (liftIO $ openFile smt' WriteMode) (liftIO . hClose) $
    liftIO . simplifySMT
  $logDebug $ "Solving using z3: " <> (T.pack smt')
  let z3Producer =
        execute
          (piped $ proc (optZ3 opts) ["-T:300", "fixedpoint.engine=duality", smt'])
          (foldUtf8Lines (withFold solverFold))
  output <- liftIO z3Producer
  pure (smt', solverStatus output)

solveNativeZ3
  :: ( Monad m
     , MonadIO m
     , MonadSafe m
     , MonadLogger m
     , MonadReader (Options, a) m
     )
  => FilePath -> m (FilePath, Status)
solveNativeZ3 smt = do
  opts <- asks fst
  $logDebug $ "Solving using z3: " <> (T.pack smt)
  let z3Producer =
        execute
          (piped $ proc (optZ3 opts) ["-T:300", "fixedpoint.engine=duality", smt])
          (foldUtf8Lines (withFold solverFold))
  output <- liftIO z3Producer
  pure (smt, invertStatus $ solverStatus output)

solverFold :: F.Fold P.Text SolverOutput
solverFold =
  (SolverOutput <$> F.any (== "unsat") <*> F.any (== "sat") <*>
   F.any (== "unknown") <*>
   F.list)

invertStatus :: Status -> Status
invertStatus Unsat = Sat
invertStatus Sat = Unsat
invertStatus Unknown = Unknown
invertStatus (Error t) = Error t
invertStatus Timeout = Timeout

solverStatus :: SolverOutput -> Status
solverStatus (SolverOutput{..})
  | solverUnsat = Unsat
  | solverSat = Sat
  | solverUnknown = Unknown
  | otherwise = Error (T.unlines solverOutput)

solveEldarica
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m, MonadReader (Options,Config) m)
  => FilePath -> FilePath -> m (FilePath,Status)
solveEldarica eldarica smt = do
  customArgs <- asks (_cnfCustomEldArgs . snd)
  let args = M.lookup smt customArgs
      producer =
        execute
          (piped $ proc eldarica $ ["-t:300", smt] ++ fromMaybe [] args)
          (foldUtf8Lines $ withFold solverFold)
  $logDebug $
    "Solving using eldarica: " <> (T.pack smt) <> " " <> T.pack (show args)
  output <- liftIO producer
  pure (smt, solverStatus output)

generateSmt
  :: (MonadIO m, MonadReader (Options, Config) m, MonadLogger m)
  => FilePath -> m FilePath
generateSmt path = do
  (opts, conf) <- ask
  let path' = makeRelative (optExamples opts) path
      relativeBasename = dropFromEnd 4 path'
      smtfile = (optBuild opts) </> relativeBasename -<.> "smt2"
      file1 = path
      basename = dropFromEnd 4 file1
      file2 = basename <> "_2" -<.> "c"
  liftIO $ createDirectoryIfMissing True (takeDirectory smtfile)
  let reveOpts =
        [file1, file2, "-o", smtfile, "-I", "/usr/lib/clang/3.8.1/include"] ++
        optionsFor (conf ^. cnfCustomArgs) smtfile ++
        if (relativeBasename `elem` conf ^. cnfNativeZ3Files)
          then ["-muz"]
          else []
  $logDebug $ "Running reve: " <> T.pack (show reveOpts)
  liftIO $ safeReadProcess (optReve opts) reveOpts
  pure smtfile

optionsFor :: M.Map FilePath [String] -> FilePath -> [String]
optionsFor m file =
  "-inline-opts" :
  fromMaybe [] (M.lookup file m)

dropFromEnd :: Int -> [a] -> [a]
dropFromEnd n xs = zipWith const xs (drop n xs)

safeReadProcess :: FilePath -> [String] -> IO ()
safeReadProcess cmd args =
  safeCreateProcess
    ((proc cmd args) {std_in = CreatePipe
                     ,std_out = CreatePipe
                     ,std_err = CreatePipe}) $
  \(_,_,Just err,handle) ->
    do ex <- waitForProcess handle
       case ex of
         ExitSuccess -> pure ()
         (ExitFailure _) -> runEffect $ PB.fromHandle err >-> PB.stdout


safeCreateProcess :: CreateProcess
                  -> ((Maybe Handle,Maybe Handle,Maybe Handle,ProcessHandle) -> IO a)
                  -> IO a
safeCreateProcess p f =
  Ex.bracket (createProcess p)
             (\(stdin',stdout',stderr',process) ->
                mapM_ hClose stdin' >> mapM_ hClose stdout' >>
                mapM_ hClose stderr' >>
                terminateProcess process)
             f
