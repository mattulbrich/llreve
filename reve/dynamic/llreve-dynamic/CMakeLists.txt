cmake_minimum_required(VERSION 2.8.8)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")
project(reve-interpreter)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

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
find_package(GMP)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(include ${CMAKE_CURRENT_BINARY_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/../../reve/include ${LLVM_INCLUDE_DIRS} ${GMP_INCLUDE_DIR} ${Z3_INCLUDE_DIR})
add_definitions(${LLVM_DEFINITIONS})

find_package(BISON)
find_package(FLEX)

file(GLOB sources lib/llreve/dynamic/*.cpp)
file(GLOB headers include/llreve/dynamic/*.h)

BISON_TARGET(PatternParser lib/llreve/dynamic/PatternParser.y ${CMAKE_CURRENT_BINARY_DIR}/llreve/dynamic/PatternParser.cpp)
FLEX_TARGET(PatternLexer lib/llreve/dynamic/PatternLexer.l  ${CMAKE_CURRENT_BINARY_DIR}/llreve/dynamic/PatternLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(PatternLexer PatternParser)

BISON_TARGET(SMTParser lib/llreve/dynamic/SMTParser.y ${CMAKE_CURRENT_BINARY_DIR}/llreve/dynamic/SMTParser.cpp)
FLEX_TARGET(SMTLexer lib/llreve/dynamic/SMTLexer.l  ${CMAKE_CURRENT_BINARY_DIR}/llreve/dynamic/SMTLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(SMTLexer SMTParser)

set_source_files_properties(${BISON_PatternParser_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
set_source_files_properties(${FLEX_PatternLexer_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
set_source_files_properties(${BISON_SMTParser_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
set_source_files_properties(${FLEX_SMTLexer_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../../reve ${CMAKE_CURRENT_BINARY_DIR}/reve)
add_library(libreve-interpreter
  ${sources}
  ${headers}
  ${BISON_PatternParser_OUTPUTS}
  ${FLEX_PatternLexer_OUTPUTS}
  ${BISON_SMTParser_OUTPUTS}
  ${FLEX_SMTLexer_OUTPUTS})
add_executable(llreve-dynamic src/LlreveDynamic.cpp ${headers})

target_link_libraries(libreve-interpreter
  libreve
)
target_link_libraries(llreve-dynamic
  libreve-interpreter
  ${GMP_LIBRARIES}
  ${GMPXX_LIBRARIES}
  ${FL_LIBRARY}
)
