cmake_minimum_required(VERSION 3.0)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/../dynamic/interpreter/cmake/")
project(llvm-reve)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CXX_WARNINGS_FLAGS "-Wall -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_STANDARD_FLAGS "-std=c++14 -fno-rtti -O3")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")

find_package(LLVM 3.8 REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
find_package(Z3)

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

include_directories(${LLVM_INCLUDE_DIRS} include)
add_definitions(${LLVM_DEFINITIONS})

file(GLOB sources lib/*.cpp)
file(GLOB headers include/*.h)

add_library(libreve ${sources} ${headers})

# Export libreve to be used within other projects.
# Note that this is not designed for installation, yet.
# Can only be used from build directory.
export(TARGETS libreve FILE libreve-exports.cmake)
target_include_directories(libreve PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

add_executable(reve Reve.cpp ${headers})

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
  ${Z3_LIBRARIES}
  )
target_link_libraries(reve
  libreve
  )
