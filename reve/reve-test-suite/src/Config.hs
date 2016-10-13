{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module Config
  (Config(..)
  ,cnfIgnoredDirs
  ,cnfIgnoredFiles
  ,cnfZ3Files
  ,cnfNativeZ3Files
  ,cnfCustomArgs
  ,cnfCustomEldArgs
  ) where

import           Control.Lens
import           Data.Aeson
import qualified Data.Map as M

data Config = Conf {_cnfIgnoredDirs :: [FilePath]
                   ,_cnfIgnoredFiles :: [FilePath]
                   ,_cnfZ3Files :: [FilePath] -- ^ Files preprocessed by eldarica and then run via z3
                   ,_cnfNativeZ3Files :: [FilePath] -- ^ Files passed to z3 in muz syntax
                   ,_cnfCustomArgs :: M.Map FilePath [String]
                   ,_cnfCustomEldArgs :: M.Map FilePath [String]}

makeLenses ''Config

instance FromJSON Config where
  parseJSON (Object v) = Conf <$>
                         v .: "ignored-dirs" <*>
                         v .: "ignored-files" <*>
                         v .: "z3-files" <*>
                         v .: "native-z3-files" <*>
                         v .: "custom-args" <*>
                         v .: "custom-eldarica-args"
  parseJSON _ = mempty
