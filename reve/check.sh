#!/usr/bin/env bash

cd build
cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..
make
./reve ~/code/reve/Horn/experiments/production/while/loop_1.spl ~/code/reve/Horn/experiments/production/while/loop_2.spl
cd ..
echo "Running clang-tidy"
clang-tidy -p build *.cpp
