{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module Config
  (Config(..)
  ,cnfIgnoredDirs
  ,cnfIgnoredFiles
  ,cnfZ3Files
  ,cnfCustomArgs
  ) where

import           Control.Lens
import           Data.Aeson
import qualified Data.Map as M

data Config = Conf {_cnfIgnoredDirs :: [FilePath]
                   ,_cnfIgnoredFiles :: [FilePath]
                   ,_cnfZ3Files :: [FilePath]
                   ,_cnfCustomArgs :: M.Map FilePath [String]}

makeLenses ''Config

instance FromJSON Config where
  parseJSON (Object v) = Conf <$>
                         v .: "ignored-dirs" <*>
                         v .: "ignored-files" <*>
                         v .: "z3-files" <*>
                         v .: "custom-args"
  parseJSON _ = mempty
