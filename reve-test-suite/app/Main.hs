{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import qualified Control.Foldl as F
import           Control.Concurrent.Async
import           Control.Lens
import           Control.Monad
import           Control.Monad.Logger
import           Control.Monad.Trans.Control
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
import           System.Exit
import           System.FilePath
import           System.Process
import           Text.PrettyPrint.ANSI.Leijen hiding ((<>),(</>),(<$>))

instance MonadSafe m => MonadSafe (LoggingT m) where
  type Base (LoggingT m) = Base m
  liftBase = lift . liftBase
  register = lift . register
  release = lift . release

printResult :: (FilePath,Maybe Status) -> Doc
printResult (path,status) =
  fill 20 (text path) <+>
  ":" <+>
  (case status of
     Nothing -> red (text "missing output")
     Just s -> printStatus s) <>
  line

printStatus :: Status -> Doc
printStatus Sat = green $ "sat"
printStatus Unsat = yellow $ "unsat"
printStatus Unknown = red $ "unknown"
printStatus Timeout = yellow $ "timeout"
printStatus (ParseError s) = red $ "error:" <+> dquotes (text (T.unpack s))

solverWorker :: (MonadLogger m,MonadSafe m)
             => Input FilePath -> STM b -> Output (FilePath,Maybe Status) -> FilePath -> m b
solverWorker input seal mergeOutput eldarica =
  do runEffect $
       (fromInput input >-> P.mapM (solveSmt eldarica) >-> toOutput mergeOutput)
     liftIO $ atomically seal

smtGeneratorWorker
  :: MonadSafe m =>
     FilePath -> FilePath -> String -> Output FilePath -> STM b -> m b
smtGeneratorWorker examples build reve output seal =
  do runEffect $
       P.find examples
              (when_ (filename_ (`elem` (ignoredDirectories ++ ignoredFiles))) prune_ >>
               glob "*_1.c") >->
       P.mapM (generateSmt build reve examples) >->
       toOutput output
     liftIO $ atomically seal

main :: IO ()
main =
  do parsedOpts <- execParser opts
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
            const $
            liftBaseDiscard async $
            solverWorker input
                         seal
                         mergeOutput
                         (optEldarica parsedOpts)
          b <-
            liftBaseDiscard async $
            do runEffect $
                 fromInput mergeInput >-> P.map printResult >->
                 P.mapM_ (liftIO . putDoc)
               liftIO $ atomically mergeSeal
          liftIO $ mapM_ wait (a : b : as)
  where opts =
          info (helper <*> optionParser)
               (fullDesc <> progDesc "Test all examples" <>
                header "reve-test-suite")

data Status = Sat | Unsat | Timeout | Unknown | ParseError T.Text deriving (Show,Eq,Ord)

ignoredDirectories :: [FilePath]
ignoredDirectories = ["ignored","notyetworking","discuss","argon2"]

ignoredFiles :: [FilePath]
ignoredFiles = ["a_1.c","linux_1.c"]

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => FilePath -> FilePath -> m (FilePath,Maybe Status)
solveSmt eldarica smt =
  do let producer =
           producerCmdEnv (Just [("_JAVA_OPTIONS","")]) (eldarica <> " -t:60 " <> smt) >-> P.map (either id id)
     $logDebug $ "Solving " <> (T.pack smt)
     (lastLine,accumulated) <- F.purely P.fold ((,) <$> F.last <*> F.list) (void $ concats $ producer ^. utf8 . P.lines)
     pure . (smt,) $
       case lastLine of
         Nothing -> Nothing
         Just "unsat" -> Just Unsat
         Just "sat" -> Just Sat
         Just "unknown" -> Just Unknown
         Just s ->
           if |  "Elapsed Time:" `T.isPrefixOf` s -> Just Timeout
              |  otherwise -> Just (ParseError (T.unlines accumulated))

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
