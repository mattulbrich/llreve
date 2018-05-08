#!/usr/bin/env bash
#set -e
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
        time (/bin/bash -c "../build/reve/llreve \"${filepath}_1.c\" \"${filepath}_2.c\" -o \"${filename}.smt2\" -I ../examples/headers -inline-opts && eld-client -sp \"${filename}.smt2\" > \"${filename}.z3.smt2\" && z3 fixedpoint.engine=${Z3_ENGINE:-duality} -v:${Z3_VERBOSE:-0} -T:300 \"${filename}.z3.smt2\"")
    fi
done
cd ..
