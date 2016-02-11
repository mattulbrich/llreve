cmake_minimum_required(VERSION 2.8.8)
project(llvm-reve)
set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang")
set(CXX_STANDARD_FLAGS "-std=c++11 -stdlib=libc++ -fno-rtti")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")

find_package(LLVM 3.7 REQUIRED CONFIG)

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

ADD_LIBRARY(clangFrontend STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangFrontend PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangFrontend.a)
ADD_LIBRARY(clangDriver STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangDriver PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangDriver.a)
ADD_LIBRARY(clangSerialization STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangSerialization PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangSerialization.a)
ADD_LIBRARY(clangCodeGen STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangCodeGen PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangCodeGen.a)
ADD_LIBRARY(clangParse STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangParse PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangParse.a)
ADD_LIBRARY(clangSema STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangSema PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangSema.a)
ADD_LIBRARY(clangAST STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangAST PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangAST.a)
ADD_LIBRARY(clangAnalysis STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangAnalysis PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangAnalysis.a)
ADD_LIBRARY(clangBasic STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangBasic PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangBasic.a)
ADD_LIBRARY(clangEdit STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangEdit PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangEdit.a)
ADD_LIBRARY(clangLex STATIC IMPORTED)
SET_TARGET_PROPERTIES(clangLex PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangLex.a)
target_link_libraries(reve
  c++abi
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
