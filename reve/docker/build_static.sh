#!/bin/bash
# currently we assume that an image named cocreature/llreve:llvm-4.0_z3-4.5 already exists
set -o nounset
set -o errexit
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
LLREVE_DIR="${DIR}/../../"
BUILD_COMMAND='rm -rf /llreve/reve/build && \
               mkdir /llreve/reve/build && \
               echo "Building llreve" && \
               cd /llreve/reve/build && \
               cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release \
                                -DLLREVE_STATIC=ON \
               ninja'
CONTAINER="$(docker create cocreature/llreve:llvm-4.0_z3-4.5 sh -c "${BUILD_COMMAND}")"
function finish {
    docker rm "${CONTAINER}"
}
trap finish EXIT
echo "Created container with id ${CONTAINER}"
echo "Copying llreve repository in container"
docker cp "${LLREVE_DIR}" $CONTAINER:/llreve
echo "Starting build"
docker start $CONTAINER
docker wait $CONTAINER
echo "Copying llreve into the current directory"
docker cp $CONTAINER:/llreve/reve/build/reve/llreve llreve
echo "Copying llreve-dynamic into the current directory"
docker cp $CONTAINER:/llreve/reve/build/dynamic/llreve-dynamic/llreve-dynamic llreve-dynamic
