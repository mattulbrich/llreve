file(GLOB sources lib/llreve/dynamic/*.cpp)

BISON_TARGET(PatternParser lib/llreve/dynamic/PatternParser.y ${CMAKE_CURRENT_BINARY_DIR}/patternparser/llreve/dynamic/PatternParser.cpp)
FLEX_TARGET(PatternLexer lib/llreve/dynamic/PatternLexer.l  ${CMAKE_CURRENT_BINARY_DIR}/patternparser/llreve/dynamic/PatternLexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(PatternLexer PatternParser)

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  set_source_files_properties(${BISON_PatternParser_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
  set_source_files_properties(${FLEX_PatternLexer_OUTPUTS} PROPERTIES COMPILE_FLAGS "-Wno-everything")
endif()

add_library(libllreve-interpreter
  ${sources}
  ${BISON_PatternParser_OUTPUTS}
  ${FLEX_PatternLexer_OUTPUTS})

target_include_directories(libllreve-interpreter
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include
  PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/patternparser
  PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(libllreve-interpreter
  libllreve
)

add_executable(llreve-dynamic src/LlreveDynamic.cpp)

target_link_libraries(llreve-dynamic
  libllreve-interpreter
  llreve-version
  ${GMPXX_LIBRARIES}
  ${GMP_LIBRARIES}
  ${FL_LIBRARY}
)
