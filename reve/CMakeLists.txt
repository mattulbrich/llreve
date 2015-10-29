cmake_minimum_required(VERSION 2.8.8)
project(llvm-reve)
set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_STANDARD_FLAGS "-std=c++11")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

file(GLOB sources *.cpp)

add_executable(reve ${sources})

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
  clangFrontend
  clangDriver
  clangSerialization
  clangCodeGen
  clangParse
  clangSema
  clangAST
  clangAnalysis
  clangBasic
  clangEdit
  clangLex
  ${llvm_libs}
  )
