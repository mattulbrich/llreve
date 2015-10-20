clang-3.7 -emit-llvm -O0 -c $1.c -o $1.bc
opt-3.7 -mem2reg $1.bc > $1_mr.bc
llvm-dis-3.7 $1_mr.bc 
