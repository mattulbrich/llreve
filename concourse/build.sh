#!/bin/bash
set -o nounset
set -o errexit
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "${DIR}/../reve/"
mkdir build
cd build
cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXE_LINKER_FLAGS=-static
ninja
cp reve/llreve "${DIR}/../../static-binaries/llreve"
cp dynamic/llreve-dynamic/llreve-dynamic "${DIR}/../../static-binaries/llreve-dynamic"
