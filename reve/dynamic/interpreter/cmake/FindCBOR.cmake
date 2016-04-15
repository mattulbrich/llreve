# Try to find the GMP librairies
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP

if (CBOR_INCLUDE_DIR AND CBOR_LIBRARIES)
		# Already in cache, be silent
		set(CBOR_FIND_QUIETLY TRUE)
endif (CBOR_INCLUDE_DIR AND CBOR_LIBRARIES)

find_path(CBOR_INCLUDE_DIR NAMES cbor.h )
find_library(CBOR_LIBRARIES NAMES cbor libcbor )

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(CBOR DEFAULT_MSG CBOR_INCLUDE_DIR CBOR_LIBRARIES)

mark_as_advanced(CBOR_INCLUDE_DIR CBOR_LIBRARIES)
