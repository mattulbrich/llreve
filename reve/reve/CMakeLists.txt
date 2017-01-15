file(GLOB sources lib/*.cpp)

add_library(llreve-cl
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib/CommandLine.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib/CommandLine.h)
target_include_directories(llreve-cl PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/cllib)

BISON_TARGET(SMTParser lib/SMTParser.yy ${CMAKE_CURRENT_BINARY_DIR}/smtparser/SMTParser.cpp)
FLEX_TARGET(SMTLexer lib/SMTLexer.ll  ${CMAKE_CURRENT_BINARY_DIR}/smtparser/SMTLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(SMTLexer SMTParser)

if(CXX_HAS_"${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  set_source_files_properties(${BISON_SMTParser_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
  set_source_files_properties(${FLEX_SMTLexer_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
endif()

add_library(libllreve ${sources} ${BISON_SMTParser_OUTPUTS} ${FLEX_SMTLexer_OUTPUTS})

target_include_directories(libllreve PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include)

add_executable(llreve Reve.cpp)

llvm_map_components_to_libnames(llvm_libs
  bitwriter
  irreader
  linker
  objcarcopts
  option
  passes
  x86codegen
  )

if (LLREVE_USE_LIBCXX)
  target_link_libraries(libllreve c++ c++abi)
endif ()

target_link_libraries(libllreve
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
target_link_libraries(llreve
  libllreve
  llreve-version
  )
