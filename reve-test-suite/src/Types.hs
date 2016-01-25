module Types
  (Status(..)
  ,EldaricaOutput(..)
  ) where

import qualified Data.Text as T

data Status
  = Sat
  | Unsat
  | Timeout
  | Unknown
  | Error T.Text
  deriving (Show,Eq,Ord)

data EldaricaOutput =
  EldOutput {eldUnsat :: Bool
            ,eldSat :: Bool
            ,eldUnknown :: Bool
            ,eldOutput :: [T.Text]}
