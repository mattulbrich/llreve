#!/usr/bin/env stack
-- stack --resolver nightly-2016-04-10 --install-ghc runghc --package turtle --package optparse-generic
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
import           Control.Monad
import qualified Data.Text as T
import           Data.Maybe
import           Prelude hiding (FilePath)
import           Turtle
import           Options.Generic

data Opts =
  Opts {out :: FilePath
       ,dir :: FilePath} deriving (Generic,Show,Eq,Ord)

instance ParseRecord Opts

main :: IO ()
main =
  do opts <- getRecord "invariants"
     output (out opts) $
       do file <-
            find (suffix ".smt2")
                 (dir opts)
          guard $ not (any (`T.isSuffixOf` format fp file) ignoredList)
          echo (format fp file)
          invariant <- getInvariant (file)
          case invariant of
            Nothing -> pure $ format (fp % ": ERROR") file
            Just invariants ->
              pure (format (fp % ":") file) <|> (select invariants) <|> pure ""

getInvariant :: MonadIO io => FilePath -> io (Maybe [T.Text])
getInvariant file =
  flip fold invariantFold $ inproc "eld" (["-ssol",file'] <> abstract) ""
  where abstract =
          guard (any (`T.isSuffixOf` file') abstractList) >>
          pure "-abstract:off"
        file' = format fp file


abstractList :: [T.Text]
abstractList =
  ["rec/mccarthy91.smt2"
  ,"rec/ackermann.smt2"
  ,"heap/swaparray.smt2"
  ,"heap/selsort.smt2"
  ,"libc/strcspn_3.smt2"]

ignoredList :: [T.Text]
ignoredList = ["libc/strncasecmp_1.smt2"]

invariantFold :: Fold T.Text (Maybe [T.Text])
invariantFold = Fold step Nothing (fmap ($[]))
  where step :: Maybe ([T.Text] -> [T.Text]) -> T.Text -> Maybe ([T.Text] -> [T.Text])
        step Nothing "sat" = Just id
        step Nothing _ = Nothing
        step (Just f) x = Just (f . (x:))
