#!/usr/bin/env bash
set -e
mkdir -p tmp
cd tmp
for file in ../examples/libc/*_1.c
do
    filepath=${file:0:-4}
    filename=`basename $filepath`
    echo "${filename}"
    if [ "$filename" = "strncasecmp_1" ]
    then
        echo "skipping"
    else
        time (/usr/bin/bash -c "../reve/_build/reve \"${filepath}_1.c\" \"${filepath}_2.c\" -o \"${filename}.smt2\" -resource-dir /usr/local/lib/clang/3.8.0/ -inline-opts && eld-client -sp \"${filename}.smt2\" > \"${filename}.z3.smt2\" && z3 fixedpoint.engine=duality -v:1 -T:300 \"${filename}.z3.smt2\"")
    fi
done
cd ..
