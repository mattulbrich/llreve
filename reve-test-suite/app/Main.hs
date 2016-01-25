{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import           Control.Concurrent.Async
import qualified Control.Foldl as F
import           Control.Lens
import           Control.Monad
import           Control.Monad.Logger
import           Control.Monad.Trans.Control
import           Data.List
import           Data.Monoid
import qualified Data.Text as T
import           Options
import           Options.Applicative hiding ((<>),(<$>))
import           Pipes
import           Pipes.Concurrent
import           Pipes.Files as P
import           Pipes.Group
import qualified Pipes.Prelude as P hiding (find)
import           Pipes.Safe
import           Pipes.Shell
import qualified Pipes.Text as P hiding (find,map,last)
import           Pipes.Text.Encoding
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.Process
import           Text.PrettyPrint.ANSI.Leijen hiding ((<>),(</>),(<$>))

instance MonadSafe m => MonadSafe (LoggingT m) where
  type Base (LoggingT m) = Base m
  liftBase = lift . liftBase
  register = lift . register
  release = lift . release

printResult :: (FilePath,Status) -> Doc
printResult (path,status) =
  fill 30 (text path) <+> ":" <+> printStatus status <> line

printStatus :: Status -> Doc
printStatus Sat = green $ "sat"
printStatus Unsat = yellow $ "unsat"
printStatus Unknown = red $ "unknown"
printStatus Timeout = yellow $ "timeout"
printStatus (Error s) = red $ "error:" <+> dquotes (text (T.unpack s))

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
            liftBaseDiscard async $
            flip finally (atomically $ mergeSeal) $ runEffect $
              fromInput mergeInput >->
              P.map printResult >->
              P.mapM_ (liftIO . putDoc)
          liftIO $ mapM_ wait (a : b : as)
  where opts =
          info (helper <*> optionParser)
               (fullDesc <> progDesc "Test all examples" <>
                header "reve-test-suite")

data Status = Sat | Unsat | Timeout | Unknown | Error T.Text deriving (Show,Eq,Ord)

ignoredDirectories :: [FilePath]
ignoredDirectories =
  ["ignored"
  ,"notyetworking"
  ,"discuss"
  ,"argon2"
  ,"coreutils"
  ,"redis"
  ,"git"
  ,"linux"
  ,"torch"]

ignoredFiles :: [FilePath]
ignoredFiles =
  ["a_1.c"
  ,"linux_1.c"
  ,"add-horn_1.c"
  ,"cocome1_1.c"
  ,"triangular_1.c"
  ,"selsort_1.c"
  ,"findmax_1.c"
  ,"fib_1.c"]

data EldaricaOutput =
  EldOutput {eldUnsat :: Bool
            ,eldSat :: Bool
            ,eldUnknown :: Bool
            ,eldOutput :: [T.Text]}

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => FilePath -> FilePath -> m (FilePath,Status)
solveSmt eldarica smt =
  do let producer =
           producerCmd (eldarica <> " -t:60 " <> smt) >-> P.map (either id id)
     $logDebug $ "Solving " <> (T.pack smt)
     EldOutput{..} <-
       F.purely P.fold
                (EldOutput <$> F.any (== "unsat") <*> F.any (== "sat") <*>
                 F.any (== "unknown") <*>
                 F.list)
                (void $ concats $ producer ^. utf8 . P.lines)
     pure . (smt,) $
       if |  eldUnsat -> Unsat
          |  eldSat -> Sat
          |  eldUnknown -> Unknown
          |  otherwise -> Error (T.unlines eldOutput)

generateSmt :: (MonadIO m, MonadThrow m)
            => FilePath -> String -> FilePath -> FilePath -> m FilePath
generateSmt buildDir reve examples path =
  do let path' = makeRelative examples path
         smtfile = buildDir </> (dropFromEnd 4 path') -<.> "smt2"
         file1 = path
         file2 = (dropFromEnd 4 path) <> "_2" -<.> "c"
     liftIO $
       createDirectoryIfMissing True
                                (takeDirectory smtfile)
     (code,_,_) <-
       liftIO $
       readProcessWithExitCode
         reve
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
