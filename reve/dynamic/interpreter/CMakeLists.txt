cmake_minimum_required(VERSION 2.8.8)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")
project(reve-interpreter)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# Everything breaks if I enable this, probably because the include sets it again. Srsly cmake is a giant pile of crap and should die in a fire.
# set(CMAKE_CXX_COMPILER "clang++")
set(CXX_WARNINGS_FLAGS "-Weverything -Wno-c++98-compat -Wno-c99-extensions -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
set(CXX_OTHER_FLAGS "--system-header-prefix=llvm --system-header-prefix=clang -fno-omit-frame-pointer -fno-exceptions")
set(CXX_STANDARD_FLAGS "-std=c++11 -fno-rtti")
set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS}")
set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")

find_package(LLVM 3.8 REQUIRED CONFIG)
find_package(GMP)
find_package(CBOR)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(include ${CMAKE_CURRENT_SOURCE_DIR}/../..//reve/include ${LLVM_INCLUDE_DIRS} ${GMP_INCLUDE_DIR})
add_definitions(${LLVM_DEFINITIONS})

find_package(BISON)
find_package(FLEX)

file(GLOB sources lib/*.cpp)
file(GLOB headers include/*.h)

set_source_files_properties(lib/PatternLexer.cpp PROPERTIES COMPILE_FLAGS /W0)

BISON_TARGET(PatternParser lib/PatternParser.y ${CMAKE_CURRENT_BINARY_DIR}/PatternParser.cpp VERBOSE ${CMAKE_CURRENT_BINARY_DIR}/pattern.output)
FLEX_TARGET(PatternLexer lib/PatternLexer.l  ${CMAKE_CURRENT_BINARY_DIR}/PatternLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(PatternLexer PatternParser)
set_source_files_properties(${BISON_PatternParser_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
set_source_files_properties(${FLEX_PatternLexer_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../../reve ${CMAKE_CURRENT_BINARY_DIR}/reve)
add_library(libreve-interpreter
  ${sources}
  ${headers}
  ${BISON_PatternParser_OUTPUTS}
  ${FLEX_PatternLexer_OUTPUTS})
add_executable(reve-interpreter src/ReveInterpreter.cpp ${headers})
add_executable(reve-analyzer src/ReveAnalyzer.cpp ${headers})

target_link_libraries(libreve-interpreter
  libreve
)
target_link_libraries(reve-analyzer
  libreve
  libreve-interpreter
  ${GMP_LIBRARIES}
  ${GMPXX_LIBRARIES}
  ${CBOR_LIBRARIES}
  ${FL_LIBRARY}
  )

target_link_libraries(reve-interpreter
  libreve
  libreve-interpreter
  ${GMP_LIBRARIES}
  ${GMPXX_LIBRARIES}
  ${CBOR_LIBRARIES}
  )
