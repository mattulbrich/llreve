{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main where

import           Control.DeepSeq
import           Data.Binary
import           Data.Data
import           Data.Hashable
import           Data.Monoid
import           Development.Shake
import           Development.Shake.FilePath
import           Development.Shake.Util

getStdout :: Action (Stdout String) -> Action String
getStdout a = a >>= \(Stdout (r :: String)) -> pure r

main :: IO ()
main =
  shakeArgs (shakeOptions {shakeFiles = "_build"}) $
  do getLLVMLibs <-
       addOracle $
       \(LLVMLibs _) -> getStdout $ cmd llvmConfig "--libfiles" llvmComponents
     getClangLibs <-
       addOracle $
       \(ClangLibs _) -> pure (unwords $ map ("-lclang" ++) clangComponents)
     getLLVMCXXFlags <-
       addOracle $ \(LLVMCXXFlags _) -> getStdout $ cmd llvmConfig "--cxxflags"
     getLLVMLDFlags <-
       addOracle $ \(LLVMLDFlags _) -> getStdout $ cmd llvmConfig "--ldflags"
     getLLVMSystemLibs <-
       addOracle $
       \(LLVMSystemLibs _) ->
         do libs <- getStdout $ cmd llvmConfig "--system-libs"
            llvmCXXFlags <- getLLVMCXXFlags (LLVMCXXFlags ())
            if "-stdlib=libc++" `elem` words llvmCXXFlags
               then pure $ libs <> " -lc++ -lc++abi"
               else pure libs
     getCXXFlags <-
       addOracle $
       \(CXXFlags _) ->
         do llvmCXXFlags <- getLLVMCXXFlags (LLVMCXXFlags ())
            pure (llvmCXXFlags <> " " <> unwords cxxFlags)
     want [buildDir </> "reve" <.> exe]
     phony "clean" $
       do putNormal "Cleaning files in _build"
          removeFilesAfter buildDir
                           ["//*"]
     buildDir <//> "*.o" %>
       \out ->
         do let c = dropDirectory1 $ out -<.> "cpp"
            need [c]
            cxxFlags' <- getCXXFlags (CXXFlags ())
            cmd "clang++ -c -Iinclude"
                cxxFlags'
                [c]
                "-o"
                [out]
     buildDir </> "reve" <.> exe %>
       \out ->
         do cpps <-
              getDirectoryFiles ""
                                ["*.cpp"]
            llvmLDFlags <- getLLVMLDFlags (LLVMLDFlags ())
            llvmSystemLibs <- getLLVMSystemLibs (LLVMSystemLibs ())
            llvmLibs <- getLLVMLibs (LLVMLibs ())
            clangLibs <- getClangLibs (ClangLibs ())
            let os = map (\cpp -> buildDir </> cpp -<.> "o") cpps
            need os
            cmd "clang++ -o" [out] os llvmLDFlags llvmSystemLibs clangLibs llvmLibs

newtype LLVMLibs =
  LLVMLibs ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype LLVMSystemLibs =
  LLVMSystemLibs ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype LLVMLDFlags =
  LLVMLDFlags ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype LLVMLibDir =
  LLVMLibDir ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype LLVMCXXFlags =
  LLVMCXXFlags ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype ClangLibs =
  ClangLibs ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)
newtype CXXFlags =
  CXXFlags ()
  deriving (Show,Eq,Binary,Typeable,Hashable,NFData)

llvmConfig :: String
llvmConfig = "llvm-config"

llvmComponents :: [String]
llvmComponents =
  ["bitwriter","irreader","linker","objcarcopts","option","passes","x86codegen"]

clangComponents :: [String]
clangComponents =
  ["Frontend"
  ,"Driver"
  ,"Serialization"
  ,"CodeGen"
  ,"Parse"
  ,"Sema"
  ,"AST"
  ,"Analysis"
  ,"Basic"
  ,"Edit"
  ,"Lex"]

buildDir :: String
buildDir = "_build"

cxxFlags :: [String]
cxxFlags =
  ["-Weverything"
  ,"-Wno-c++98-compat"
  ,"-Wno-exit-time-destructors"
  ,"-Wno-global-constructors"
  ,"-Wno-padded"
  ,"-Wno-switch-enum"
  ,"-Wno-shadow"]
