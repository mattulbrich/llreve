cmake_minimum_required(VERSION 2.8.8)
project(llvm-reve)
set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors")
set(CXX_STANDARD_FLAGS "-std=c++1z")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

add_executable(reve Reve.cpp UniqueNamePass.cpp AnnotStackPass.cpp Mem2Reg.cpp)

llvm_map_components_to_libnames(llvm_libs
  bitwriter
  irreader
  linker
  objcarcopts
  option
  passes
  x86codegen
  )

target_link_libraries(reve
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
