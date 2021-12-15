#!/bin/zsh
if [ -n $1 ]; then
    file=$(basename $1 .c)
    clang -S -g -c -Xclang -disable-O0-optnone -fno-discard-value-names -emit-llvm $1 -o $file.ll
else
echo "please give the .c file"
fi