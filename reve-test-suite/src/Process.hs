{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
module Process
  (solveSmt,generateSmt) where

import qualified Control.Foldl as F
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Logger
import           Data.Monoid
import qualified Data.Text as T
import           Pipes
import           Pipes.Group
import qualified Pipes.Prelude as P
import           Pipes.Safe
import           Pipes.Shell
import qualified Pipes.Text as P hiding (find,map,last)
import           Pipes.Text.Encoding
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.Process
import           Types

solveSmt
  :: (Monad m, MonadIO m, MonadSafe m, MonadLogger m)
  => FilePath -> FilePath -> m (FilePath,Status)
solveSmt eldarica smt =
  do let producer =
           producerCmd (eldarica <> " -t:60 " <> smt) >-> P.map (either id id)
     $logDebug $ "Solving " <> (T.pack smt)
     EldOutput{..} <- F.purely P.fold
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
