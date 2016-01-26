{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
module Process
  (solveSmt,generateSmt) where

import           Config
import qualified Control.Foldl as F
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Logger
import           Data.Monoid
import qualified Data.Text as T
import           Options
import           Pipes
import qualified Pipes.ByteString as PB
import           Pipes.Group
import qualified Pipes.Prelude as P
import           Pipes.Safe hiding (handle)
import           Pipes.Shell
import qualified Pipes.Text as P hiding (find,map,last)
import           Pipes.Text.Encoding
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO hiding (utf8)
import           System.Process
import           Types

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => [FilePath] -> FilePath -> FilePath -> FilePath -> FilePath -> m (FilePath,Status)
solveSmt z3Files build eldarica z3 smt
   | smt `elem` map (build</>) z3Files = solveZ3 eldarica z3 smt
   | otherwise = solveEldarica eldarica smt

solveZ3 :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
        => FilePath -> FilePath -> FilePath -> m (FilePath,Status)
solveZ3 eldarica z3 smt =
  do let producer =
           producerCmd (eldarica <> " -t:60 -sp " <> smt) >->
           P.map (either (const "") id)
         smt' = smt <> ".z3"
     bracket (liftIO $ openFile smt' WriteMode)
             (liftIO . hClose) $
       \handle -> do runEffect $ producer >-> PB.toHandle handle
     $logDebug $ "Solving using z3: " <> (T.pack smt')
     let z3Producer = producerCmd (z3 <> " fixedpoint.engine=duality " <> smt') >-> P.map (either id id)
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

generateSmt :: (MonadIO m, MonadThrow m)
            => Options -> FilePath -> m FilePath
generateSmt opts path =
  do let path' = makeRelative (optExamples opts) path
         smtfile = (optBuild opts) </> (dropFromEnd 4 path') -<.> "smt2"
         file1 = path
         file2 = (dropFromEnd 4 path) <> "_2" -<.> "c"
     liftIO $
       createDirectoryIfMissing True
                                (takeDirectory smtfile)
     (code,_,_) <-
       liftIO $
       readProcessWithExitCode
         (optReve opts)
         [file1
         ,file2
         ,"-o"
         ,smtfile
         ,"-off-by-n"
         ,"-I"
         ,"/usr/lib/clang/3.7.1/include"]
         []
     case code of
       ExitSuccess -> pure ()
       (ExitFailure _) -> throwM code
     pure smtfile

dropFromEnd :: Int -> [a] -> [a]
dropFromEnd n xs = zipWith const xs (drop n xs)
