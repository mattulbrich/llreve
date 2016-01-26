{-# LANGUAGE OverloadedStrings #-}
module Config
  (Config(..)
  ) where

import Data.Aeson

data Config = Conf {cnfIgnoredDirs :: [FilePath]
                   ,cnfIgnoredFiles :: [FilePath]
                   ,cnfZ3Files :: [FilePath]}

instance FromJSON Config where
  parseJSON (Object v) = Conf <$>
                         v .: "ignored-dirs" <*>
                         v .: "ignored-files" <*>
                         v .: "z3-files"
  parseJSON _ = mempty
