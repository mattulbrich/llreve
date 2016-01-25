module Config
  (ignoredDirectories
  ,ignoredFiles
  ,z3Files) where

ignoredDirectories :: [FilePath]
ignoredDirectories =
  ["ignored"
  ,"notyetworking"
  ,"discuss"
  ,"argon2"
  ,"coreutils"
  ,"redis"
  ,"git"
  ,"linux"
  ,"torch"]

ignoredFiles :: [FilePath]
ignoredFiles =
  ["a_1.c"
  ,"linux_1.c"
  ,"cocome1_1.c"
  ,"triangular_1.c"
  ,"selsort_1.c"
  ,"findmax_1.c"
  ,"fib_1.c"]

z3Files :: [FilePath]
z3Files = ["rec/add-horn.smt2"]
