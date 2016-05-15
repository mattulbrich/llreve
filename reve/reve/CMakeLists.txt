cmake_minimum_required(VERSION 3.0)
project(llvm-reve)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang -fno-omit-frame-pointer")
set(CXX_STANDARD_FLAGS "-std=c++11 -stdlib=libc++ -fno-rtti")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")

find_package(LLVM 3.8 REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

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

target_link_libraries(libreve
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
target_link_libraries(reve
  libreve
  )
