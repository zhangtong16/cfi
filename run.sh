#!/bin/bash

opt -load-pass-plugin ./build/lib/libFLTA.so -passes=flta -S ./bc/nginx.bc
