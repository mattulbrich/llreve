{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
module Main where

import           Control.Concurrent.Async
import           Control.Lens
import           Control.Monad
import           Control.Monad.Logger
import           Data.Monoid
import qualified Data.Text as T
import           Options
import           Options.Applicative hiding ((<>))
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


newtype LoggingT' m a =
  LoggingT' {runLoggingT' :: LoggingT m a}
  deriving (MonadMask,MonadTrans,MonadCatch,MonadThrow,Monad,Functor,Applicative,MonadIO,MonadLogger)

instance MonadSafe m => MonadSafe (LoggingT' m) where
  type Base (LoggingT' m) = Base m
  liftBase = lift . liftBase
  register = lift . register
  release = lift . release

run :: Effect (LoggingT' (SafeT IO)) r -> IO r
run = runSafeT . runStderrLoggingT . runLoggingT' . runEffect

main :: IO ()
main =
  do parsedOpts <- execParser opts
     (output,input,seal) <- spawn' unbounded
     (mergeOutput,mergeInput,mergeSeal) <- spawn' unbounded
     do a <-
          async $
          do run $
               P.find (optExamples parsedOpts)
                      (when_ (filename_ (`elem` (ignoredDirectories ++
                                                 ignoredFiles)))
                             prune_ >>
                       glob "*_1.c") >->
               P.mapM (generateSmt (optBuild parsedOpts)
                                   (optReve parsedOpts)
                                   (optExamples parsedOpts)) >->
               toOutput output
             atomically seal
        as <-
          liftIO $
          forM [(1 :: Int) .. (optProcesses parsedOpts)] $
          const $
          async $
          do runSafeT $
               runStderrLoggingT $
               runLoggingT' $
               runEffect (fromInput input >->
                          P.mapM (solveSmt (optEldarica parsedOpts)) >->
                          toOutput mergeOutput)
             atomically seal
        b <- async $ do run $ fromInput mergeInput >-> P.print
                        atomically mergeSeal
        liftIO $ mapM_ wait (a:b:as)
  where opts =
          info (helper <*> optionParser)
               (fullDesc <> progDesc "Test all examples" <>
                header "reve-test-suite")

data Status = Sat | Unsat | Timeout | Unknown | ParseError T.Text deriving (Show,Eq,Ord)

ignoredDirectories :: [FilePath]
ignoredDirectories = ["ignored","notyetworking","discuss","argon2"]

ignoredFiles :: [FilePath]
ignoredFiles = ["a_1.c"]

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => FilePath -> FilePath -> m (FilePath,Maybe Status)
solveSmt eldarica smt =
  do let producer =
           producerCmd (eldarica <> " -t:60 " <> smt) >-> P.map (either id id)
     $(logDebug) $ "Solving " <> (T.pack smt)
     lastLine <- P.last (void $ concats $ producer ^. utf8 . P.lines)
     pure . (smt,) $
       case lastLine of
         Nothing -> Nothing
         Just "unsat" -> Just Unsat
         Just "sat" -> Just Sat
         Just "unknown" -> Just Unknown
         Just s ->
           if |  "Elapsed Time:" `T.isPrefixOf` s -> Just Timeout
              |  otherwise -> Just (ParseError s)

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
