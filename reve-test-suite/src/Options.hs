module Options where

import Options.Applicative

data Options = Options {optReve :: FilePath
                       ,optEldarica :: FilePath
                       ,optZ3 :: FilePath
                       ,optExamples :: FilePath
                       ,optBuild :: FilePath
                       ,optProcesses :: Int}

optionParser :: Parser Options
optionParser =
  Options <$>
  strOption (long "reve" <> metavar "PATH" <> help "Path to reve executable" <>
             value "../reve/build/reve") <*>
  strOption (long "eldarica" <> metavar "PATH" <>
             help "Path to eldarica executable" <>
             value "eld") <*>
  strOption (long "z3" <> metavar "PATH" <> help "Path to z3 executable" <>
             value "z3") <*>
  strOption (long "examples" <> metavar "PATH" <>
             help "Directory containing the examples" <>
             value "../examples") <*>
  strOption (long "build" <> metavar "PATH" <>
             help "Directory where the smt files are placed in" <>
             value "build") <*>
  option auto
         (short 'j' <> metavar "PROCESSES" <>
          help "Number of parallel solver instances" <>
          value 1)
