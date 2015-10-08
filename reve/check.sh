#!/usr/bin/env bash

cd build
make clean
cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..
make
./reve ~/code/reve/Horn/experiments/production/while/loop_1.spl ~/code/reve/Horn/experiments/production/while/loop_2.spl
sources=(../*.cpp)
echo "Running clang-tidy"
clang-tidy "${sources[@]}"
echo "Running clang-modernize"
clang-modernize -summary -p . -include ..
echo "Running cncc"
for file in ${sources[@]}
do
    cncc --style=../../.cncc.style --dbdir . "$file"
done
