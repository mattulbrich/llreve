cmake_minimum_required(VERSION 2.8.8)
project(llvm-reve)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang")
set(CXX_STANDARD_FLAGS "-std=c++11 -stdlib=libc++ -fno-rtti")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")

find_package(LLVM 3.8 REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

file(GLOB sources *.cpp)
file(GLOB headers include/*.h)

add_executable(reve ${sources} ${headers})

llvm_map_components_to_libnames(llvm_libs
  bitwriter
  irreader
  linker
  objcarcopts
  option
  passes
  x86codegen
  )

add_library(clangFrontend STATIC IMPORTED)
set_target_properties(clangFrontend PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangFrontend.a)
add_library(clangDriver STATIC IMPORTED)
set_target_properties(clangDriver PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangDriver.a)
add_library(clangSerialization STATIC IMPORTED)
set_target_properties(clangSerialization PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangSerialization.a)
add_library(clangCodeGen STATIC IMPORTED)
set_target_properties(clangCodeGen PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangCodeGen.a)
add_library(clangParse STATIC IMPORTED)
set_target_properties(clangParse PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangParse.a)
add_library(clangSema STATIC IMPORTED)
set_target_properties(clangSema PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangSema.a)
add_library(clangAST STATIC IMPORTED)
set_target_properties(clangAST PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangAST.a)
add_library(clangAnalysis STATIC IMPORTED)
set_target_properties(clangAnalysis PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangAnalysis.a)
add_library(clangBasic STATIC IMPORTED)
set_target_properties(clangBasic PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangBasic.a)
add_library(clangEdit STATIC IMPORTED)
set_target_properties(clangEdit PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangEdit.a)
add_library(clangLex STATIC IMPORTED)
set_target_properties(clangLex PROPERTIES
    IMPORTED_LOCATION /usr/local/lib/libclangLex.a)
target_link_libraries(reve
  c++
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
