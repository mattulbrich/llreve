#!/bin/bash
cd /vagrant/reve
echo "set(CMAKE_EXE_LINKER_FLAGS \"-static\")" >> CMakeLists.txt
rm -r build
mkdir build
cd build
export CC=clang
export CXX=clang++
cmake ..
make -j4
