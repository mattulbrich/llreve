module Main where

import qualified Options.Applicative as OP
import           Options.Applicative hiding (Parser,runParser,Failure,Success)
import           Parser
import           Simplify
import           System.IO
import           System.Process
import           Text.PrettyPrint.HughesPJClass hiding ((<>))
import           Text.Trifecta hiding (err)

main :: IO ()
main =
  do options <- execParser opts
     inFile <-
       readProcess (optEld options)
                   ["-sp",optIn options]
                   ""
     let res =
           parseString (runParser smt)
                       mempty
                       inFile
     case res of
       Failure err -> hPrint stderr err
       Success a ->
         writeFile (optOut options)
                   (show . pPrint . mergeNotExists . simplify $ a)
  where opts =
          info (helper <*> optionParser)
               (fullDesc <>
                progDesc "Convert SMT to a format compatible with Z3" <>
                header "smt-conv - hornify smt")

data Options =
  Options {optIn :: FilePath
          ,optOut :: FilePath
          ,optEld :: FilePath}

optionParser :: OP.Parser Options
optionParser =
  Options <$>
  strOption (short 'i' <> metavar "INPUT" <>
             help "Path to smt that should be converted") <*>
  strOption (short 'o' <> metavar "OUTPUT" <>
             help "Path where the converted smt should be written to") <*>
  strOption (long "eldarica" <> metavar "PATH" <> help "Path to eldarica" <> value "eld")
