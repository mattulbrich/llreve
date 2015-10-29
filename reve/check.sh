#!/usr/bin/env bash

cd build
cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..
make
./reve ../../examples/break_1.c ../../examples/break_2.c
cd ..
echo "Running clang-tidy"
clang-tidy -fix -p build *.cpp
