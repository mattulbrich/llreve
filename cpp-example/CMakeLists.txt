cmake_minimum_required(VERSION 2.8.8)
project(llvm-cpp-example)
set(CMAKE_CXX_COMPILER "/usr/bin/clang++")
set(CMAKE_CXX_FLAGS
"-Weverything \
-Wno-c++98-compat \
-Wno-exit-time-destructors \
-Wno-global-constructors \
-std=c++1z")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

add_executable(example Example.cpp UniqueNamePass.cpp AnnotStackPass.cpp)

llvm_map_components_to_libnames(llvm_libs
  core
  support
  option
  bitreader
  mcparser
  transformutils
  instrumentation
  profiledata
  x86codegen
  ipo
  bitwriter
  objcarcopts
  irreader
  linker
  mcjit
  )

target_link_libraries(example
  -Wl,--start-group
  # clang
  # clangARCMigrate
  clangAST
  # clangASTMatchers
  clangAnalysis
  clangBasic
  clangCodeGen
  clangDriver
  # clangDynamicASTMatchers
  clangEdit
  # clangFormat
  clangFrontend
  # clangFrontendTool
  # clangIndex
  clangLex
  clangParse
  # clangRewrite
  # clangRewriteFrontend
  clangSema
  clangSerialization
  # clangStaticAnalyzerCheckers
  # clangStaticAnalyzerCore
  # clangStaticAnalyzerFrontend
  # clangTooling
  # clangToolingCore
  ${llvm_libs}
 -Wl,--end-group
  )
