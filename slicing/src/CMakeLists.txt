cmake_minimum_required(VERSION 3.0)
project(llvm-reve-slicing VERSION 0.1)

### =======================================================
### ========== Macros for bedder readability ==============
### =======================================================

macro(set_compiler_settings)
	set(CXX_WARNINGS_FLAGS "-Wno-c++98-compat -Wno-exit-time-destructors -Wno-global-constructors -Wno-padded -Wno-switch-enum -Wno-shadow")
	set(CXX_STANDARD_FLAGS "-std=c++14 -fno-rtti -g -fpermissive")
	#Use cmake -D CLANG_FLAGS=yourFlags to add custom flags
	set(USER_FLAGS "${CLANG_FLAGS}")
	set(CMAKE_CXX_FLAGS "${CXX_WARNINGS_FLAGS} ${CXX_STANDARD_FLAGS} ${CXX_OTHER_FLAGS} ${USER_FLAGS}")
	set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")
endmacro(set_compiler_settings)

#Find llvm and make it aviable
macro (load_llvm)
	find_package(LLVM 3.9 REQUIRED CONFIG)
	find_package(Clang REQUIRED CONFIG)

	message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
	message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

	include_directories(${LLVM_INCLUDE_DIRS})
	add_definitions(${LLVM_DEFINITIONS})
endmacro(load_llvm)

#Compile libreve, make it aviable, make sure it is recompiled on change
macro (load_libreve)
	set(REVE_USE_LIBCXX "YES")

	set(reve_build_dir ${CMAKE_BINARY_DIR}/reve)
	set(reve_dir ${CMAKE_CURRENT_SOURCE_DIR}/../../reve/reve)

	file(MAKE_DIRECTORY ${reve_build_dir})

	# First, we need to compile lib reve, otherwise we would not have
	# 'libreve-exports.cmake' and cmake would not now where to find
	# the library to link against.
	#
	# Will be run on initial 'cmake' or after changes to this file.
	execute_process(COMMAND ${CMAKE_COMMAND} ${reve_dir}
			WORKING_DIRECTORY ${reve_build_dir}
		)
	execute_process(COMMAND ${CMAKE_COMMAND} --build .
			WORKING_DIRECTORY ${reve_build_dir}
		)

	# This command will make libreve aviable.
	# Note, that adding include directory is not neccessary as
	# target_include_directories() was used in the other cmake file.
	include(${reve_build_dir}/llreve-cl-exports.cmake)
	include(${reve_build_dir}/libreve-exports.cmake)

	# Second, we add a custom target. This is neccessary to automaticaly
	# recompile libreve on changes after the initial run of cmake.
	#
	# Will be run on every 'make'.
	add_custom_target(librevebuild
			COMMAND ${CMAKE_COMMAND} --build .
			WORKING_DIRECTORY ${reve_build_dir}
		)
endmacro(load_libreve)

macro(find_sources)
	include_directories(${CMAKE_CURRENT_SOURCE_DIR})
	file(GLOB_RECURSE sources "*.cpp")
	file(GLOB test_sources "test/*.cpp")
	file(GLOB exec_sources "*.cpp")

	foreach (tmp_file ${test_sources})
		list(REMOVE_ITEM sources ${tmp_file})
	endforeach (tmp_file)

	foreach (tmp_file ${exec_sources})
		list(REMOVE_ITEM sources ${tmp_file})
	endforeach (tmp_file)
endmacro(find_sources)


### =======================================================
### ============ Start of doing things ====================
### =======================================================

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/../bin)
set_compiler_settings()
load_llvm()
load_libreve()
find_sources()

add_custom_target(version
		COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/../scripts/createVersion ${PROJECT_VERSION}
		WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
	)

# Pack all non executable sources into library to prevent
# repeated building of source files.
add_library(all_sources ${sources})
target_link_libraries(all_sources libreve)

# Add a dependencie to librevebuild, to ensure it is build befor the main project.
add_dependencies(all_sources librevebuild)

add_executable(slicing main.cpp)
add_executable(testing test.cpp ${test_sources})
add_dependencies(slicing version)
add_dependencies(testing version)

# Find librarys for components
# To get a list of all aviable components use 'llvm-config --components'
llvm_map_components_to_libnames(llvm_libs
		support
	)

target_link_libraries(slicing
		${llvm_libs}
		libreve
		all_sources
	)

target_link_libraries(testing
		${llvm_libs}
		libreve
		all_sources
	)

