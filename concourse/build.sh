#!/bin/bash
set -o nounset
set -o errexit
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "${DIR}/../reve/dynamic/llreve-dynamic/"
mkdir build
cd build
cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXE_LINKER_FLAGS=-static
ninja
cp reve/reve "${DIR}/../../static-binaries/llreve"
cp llreve-dynamic "${DIR}/../../static-binaries/llreve-dynamic"
