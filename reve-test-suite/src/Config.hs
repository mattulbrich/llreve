module Config
  (ignoredDirectories
  ,ignoredFiles) where

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
  ,"add-horn_1.c"
  ,"cocome1_1.c"
  ,"triangular_1.c"
  ,"selsort_1.c"
  ,"findmax_1.c"
  ,"fib_1.c"]
