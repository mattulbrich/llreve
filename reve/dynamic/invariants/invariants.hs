#!/usr/bin/env stack
-- stack --resolver nightly-2016-04-10 --install-ghc runghc --package turtle --package optparse-generic
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
import qualified Data.Set as S
import qualified Data.Text as T
import           Data.Maybe
import           Prelude hiding (FilePath)
import           Turtle
import qualified Control.Foldl as F
import           Options.Generic

data Opts =
  Opts {out :: FilePath
       ,dir :: FilePath} deriving (Generic,Show,Eq,Ord)

instance ParseRecord Opts

main :: IO ()
main =
  do opts <- getRecord "invariants"
     output (out opts) $
       do file <- find (suffix ".smt2") (dir opts)
          guard $ not (any (`T.isSuffixOf`format fp file) ignoredList)
          echo (format fp file)
          invariant <- getInvariant (file)
          pure $
            format (fp % ": " %s)
                   file
                   (fromMaybe "ERROR" invariant)

getInvariant :: MonadIO io => FilePath -> io (Maybe Text)
getInvariant file =
  flip fold F.last $ inproc "eld" (["-ssol",file'] <> abstract) ""
  where abstract =
          guard (any (`T.isSuffixOf` file') abstractList) >>
          pure "-abstract:off"
        file' = format fp file


abstractList :: [T.Text]
abstractList = ["rec/mccarthy91.smt2","rec/ackermann.smt2","heap/swaparray.smt2","heap/selsort.smt2","libc/strcspn_3.smt2"]

ignoredList :: [T.Text]
ignoredList = ["libc/strncasecmp_1.smt2"]
