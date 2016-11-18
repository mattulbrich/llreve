#!/bin/bash
# currently we assume that an image named cocreature/llreve:llvm-3.9_z3-4.5 already exists
set -o nounset
set -o errexit
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
LLREVE_DIR="${DIR}/../../"
BUILD_COMMAND='rm -rf /llreve/reve/reve/build /llreve/reve/dynamic/llreve-dynamic/build && \
               mkdir /llreve/reve/reve/build /llreve/reve/dynamic/llreve-dynamic/build && \
               echo "Building llreve" && \
               cd /llreve/reve/reve/build && \
               cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXE_LINKER_FLAGS=-static && \
               ninja && \
               echo "Building llreve-dynamic" && \
               cd /llreve/reve/dynamic/llreve-dynamic/build && \
               cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXE_LINKER_FLAGS=-static && \
               ninja'
CONTAINER="$(docker create cocreature/llreve:llvm-3.9_z3-4.5 sh -c "${BUILD_COMMAND}")"
function finish {
    docker rm "${CONTAINER}"
}
trap finish EXIT
echo "Created container with id ${CONTAINER}"
echo "Copying llreve repository in container"
docker cp "${LLREVE_DIR}" $CONTAINER:/llreve
echo "Starting build of llreve"
docker start $CONTAINER
docker wait $CONTAINER
echo "Copying llreve into the current directory"
docker cp $CONTAINER:/llreve/reve/reve/build/reve llreve
echo "Copying llreve-dynamic into the current directory"
docker cp $CONTAINER:/llreve/reve/dynamic/llreve-dynamic/build/llreve-dynamic llreve-dynamic
