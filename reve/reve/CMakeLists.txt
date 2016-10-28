cmake_minimum_required(VERSION 3.0)
project(llreve)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/")
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors")
  if("Ninja" STREQUAL ${CMAKE_GENERATOR})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fcolor-diagnostics")
  endif()
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(CXX_WARNINGS_FLAGS "-Wall")
endif()
if (NOT "${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(CXX_WARNINGS_FLAGS "${CXX_WARNING_FLAGS} -Wno-padded -Wno-switch-enum -Wno-shadow")
  set(CXX_OTHER_FLAGS "-fno-omit-frame-pointer")
  set(CXX_STANDARD_FLAGS "-std=c++14 -fno-rtti")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")
  set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")
endif()

find_package(LLVM 3.9 REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
find_package (Threads REQUIRED)

exec_program(llvm-config ARGS --cxxflags OUTPUT_VARIABLE LLVM_CXXFLAGS)
separate_arguments(LLVM_CXXFLAGS)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
set(REVE_USE_LIBCXX "NO")
#if ("-stdlib=libc++" IN_LIST LLVM_CXXFLAGS)
## The following command does the same as IN_LIST above but is compatible to version 3.0
if (";${LLVM_CXXFLAGS};" MATCHES ";-stdlib=libc\\+\\+;")
  set(REVE_USE_LIBCXX "YES")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif ()

message(STATUS "use libcxx: ${REVE_USE_LIBCXX}")

find_path(Z3_INCLUDE_DIRS NAMES z3++.h)
find_library(Z3_LIB NAMES z3 libz3)
include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

file(GLOB sources lib/*.cpp)
file(GLOB headers include/*.h)

add_library(llreve-cl
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib/CommandLine.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib/CommandLine.h)
target_include_directories(llreve-cl PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib)
export(TARGETS llreve-cl FILE llreve-cl-exports.cmake)

add_library(libreve ${sources} ${headers})
target_include_directories(libreve PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include)

# Export libreve to be used within other projects.
# Note that this is not designed for installation, yet.
# Can only be used from build directory.
export(TARGETS libreve FILE libreve-exports.cmake)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)
add_executable(reve Reve.cpp ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp ${headers})

llvm_map_components_to_libnames(llvm_libs
  bitwriter
  irreader
  linker
  objcarcopts
  option
  passes
  x86codegen
  )

if (REVE_USE_LIBCXX)
  target_link_libraries(libreve c++ c++abi)
endif ()

target_link_libraries(libreve
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
  ${Z3_LIB}
  ${CMAKE_THREAD_LIBS_INIT}
  llreve-cl
  )
target_link_libraries(reve
  libreve
  )
