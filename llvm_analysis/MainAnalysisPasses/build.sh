#!/bin/bash
BASEDIR=$(dirname "$0")
LLVM_DIR=$LLVM_ROOT/../cmake
echo "[*] Trying to Run Cmake"
mkdir build_dir
cd build_dir
cmake ..
echo "[*] Trying to make"
make -j8
cd $BASEDIR
