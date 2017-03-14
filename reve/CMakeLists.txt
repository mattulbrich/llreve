cmake_minimum_required (VERSION 3.3)
project (llreve)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")
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

option(LLREVE_STATIC "Link binaries statically" OFF)

if(${LLREVE_STATIC})
  set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  set(CMAKE_EXE_LINKER_FLAGS "-static")
endif()

option(LLREVE_SANITIZE "Enable sanitizers" OFF)

if(${LLREVE_SANITIZE})
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=undefined -fsanitize=address")
endif()

find_package(LLVM 4.0 REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
find_package(Threads REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)
find_package(GMP REQUIRED)

exec_program(llvm-config ARGS --cxxflags OUTPUT_VARIABLE LLVM_CXXFLAGS)
separate_arguments(LLVM_CXXFLAGS)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
set(REVE_USE_LIBCXX "NO")
if ("-stdlib=libc++" IN_LIST LLVM_CXXFLAGS)
  set(REVE_USE_LIBCXX "YES")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif ()

message(STATUS "use libcxx: ${REVE_USE_LIBCXX}")

find_path(Z3_INCLUDE_DIRS NAMES z3++.h)
find_library(Z3_LIB NAMES z3 libz3)
include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

configure_file(CMakeLists.txt.in googletest-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "CMake step for googletest failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "Build step for googletest failed: ${result}")
endif()
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
add_subdirectory(${CMAKE_BINARY_DIR}/googletest-src
                 ${CMAKE_BINARY_DIR}/googletest-build)

# # The gtest/gtest_main targets carry header search path
# # dependencies automatically when using CMake 2.8.11 or
# # later. Otherwise we have to add them here ourselves.
# if (CMAKE_VERSION VERSION_LESS 2.8.11)
#   include_directories("${gtest_SOURCE_DIR}/include")
# endif()

enable_testing()

add_subdirectory(version)
add_subdirectory(reve)
add_subdirectory(dynamic/llreve-dynamic)
