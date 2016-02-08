{-# LANGUAGE OverloadedStrings #-}
module Output where

import qualified Data.Text as T
import           Text.PrettyPrint.ANSI.Leijen
import           Types

printResult :: (FilePath,Status) -> Doc
printResult (path,status) =
  fill 30 (text path) <+> ":" <+> printStatus status <> line

printStatus :: Status -> Doc
printStatus Sat = green $ "sat"
printStatus Unsat = yellow $ "unsat"
printStatus Unknown = red $ "unknown"
printStatus Timeout = yellow $ "timeout"
printStatus (Error s) = red $ "error:" <+> dquotes (text (T.unpack s))
