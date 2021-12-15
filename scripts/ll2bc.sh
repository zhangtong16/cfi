#!/bin/zsh
if [ -n $1 ]; then
    file=$(basename $1 .ll)
    llvm-as $1 -o $file.bc
else
echo "please give the .ll file"
fi