#!/bin/bash

opt -load-pass-plugin ./build/lib/libMLTA.so -passes=mlta -S ./bc/nginx.O2.bc
