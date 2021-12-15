#!/bin/zsh
clang -ldl -lpthread -lcrypt -lpcre -lz nginx.bc -o nginx