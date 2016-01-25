module Types
  (Status(..)
  ,SolverOutput(..)
  ) where

import qualified Data.Text as T

data Status
  = Sat
  | Unsat
  | Timeout
  | Unknown
  | Error T.Text
  deriving (Show,Eq,Ord)

data SolverOutput =
  SolverOutput {solverUnsat :: Bool
               ,solverSat :: Bool
               ,solverUnknown :: Bool
               ,solverOutput :: [T.Text]}
