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
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Logger
import           Control.Monad.Reader
import qualified Data.Map as M
import           Data.Monoid
import qualified Data.Text as T
import           Options
import           Pipes
import qualified Pipes.ByteString as PB
import           Pipes.Group
import qualified Pipes.Prelude as P
import           Pipes.Safe hiding (handle)
import           Pipes.Shell hiding (cmd)
import qualified Pipes.Text as P hiding (find,map,last)
import           Pipes.Text.Encoding
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO hiding (utf8)
import           System.Process
import           Types

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m, MonadReader (Options,Config) m)
  => FilePath -> m (FilePath,Status)
solveSmt smt =
  do (opts,conf) <- ask
     if smt `elem` map (optBuild opts </>) (conf ^. cnfZ3Files)
        then solveZ3 smt
        else solveEldarica (optEldarica opts) smt

solveZ3 :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m,MonadReader (Options,a) m)
        => FilePath -> m (FilePath,Status)
solveZ3 smt =
  do opts <- asks fst
     let producer =
           producerCmd (optEldarica opts <> " -t:60 -sp " <> smt) >->
           P.map (either (const "") id)
         smt' = smt <> ".z3"
     bracket (liftIO $ openFile smt' WriteMode)
             (liftIO . hClose) $
       \handle -> do runEffect $ producer >-> PB.toHandle handle
     $logDebug $ "Solving using z3: " <> (T.pack smt')
     let z3Producer = producerCmd (optZ3 opts <> " fixedpoint.engine=duality " <> smt') >-> P.map (either id id)
     output <- F.purely P.fold solverFold (void $ concats $ z3Producer ^. utf8 . P.lines)
     pure (smt',solverStatus output)


solverFold :: F.Fold P.Text SolverOutput
solverFold =
  (SolverOutput <$> F.any (== "unsat") <*> F.any (== "sat") <*>
   F.any (== "unknown") <*>
   F.list)

solverStatus :: SolverOutput -> Status
solverStatus (SolverOutput{..})
  | solverUnsat = Unsat
  | solverSat = Sat
  | solverUnknown = Unknown
  | otherwise = Error (T.unlines solverOutput)

solveEldarica
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => FilePath -> FilePath -> m (FilePath,Status)
solveEldarica eldarica smt =
  do let producer =
           producerCmd (eldarica <> " -t:60 " <> smt) >-> P.map (either id id)
     $logDebug $ "Solving using eldarica: " <> (T.pack smt)
     output <-
       F.purely P.fold solverFold (void $ concats $ producer ^. utf8 . P.lines)
     pure (smt,solverStatus output)

generateSmt :: (MonadIO m, MonadThrow m, MonadReader (Options,Config) m)
            => FilePath -> m FilePath
generateSmt path =
  do (opts,conf) <- ask
     let path' =
           makeRelative (optExamples opts)
                        path
         smtfile = (optBuild opts) </> (dropFromEnd 4 path') -<.> "smt2"
         file1 = path
         file2 = (dropFromEnd 4 path) <> "_2" -<.> "c"
     liftIO $
       createDirectoryIfMissing True
                                (takeDirectory smtfile)
     liftIO $ putStrLn $ "starting process: " ++ smtfile
     liftIO $
       safeReadProcess
         (optReve opts)
         ([file1,file2,"-o",smtfile,"-I","/usr/lib/clang/3.7.1/include"] ++
          optionsFor (conf ^. cnfCustomArgs)
                     smtfile)
     liftIO $ putStrLn $ "process finished: " ++ smtfile
     pure smtfile

optionsFor :: M.Map FilePath [String] -> FilePath -> [String]
optionsFor m file =
  case M.lookup file m of
    Nothing -> ["-off-by-n"]
    Just opts -> opts

dropFromEnd :: Int -> [a] -> [a]
dropFromEnd n xs = zipWith const xs (drop n xs)

safeReadProcess :: FilePath -> [String] -> IO ()
safeReadProcess cmd args =
  safeCreateProcess
    ((proc cmd
           args) {std_in = CreatePipe
                 ,std_out = CreatePipe
                 ,std_err = CreatePipe}) $
  \(_,_,_,handle) ->
    do ex <- waitForProcess handle
       case ex of
         ExitSuccess -> pure ()
         (ExitFailure _) -> throwM ex

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
