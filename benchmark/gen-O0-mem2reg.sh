#!/bin/bash

clang $1.c -emit-llvm -Xclang -disable-O0-optnone -g -c -O0 -o $1.bc
llvm-dis $1.bc -o $1.ll.tmp
opt -mem2reg -S $1.ll.tmp -o $1.ll
