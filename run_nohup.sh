#!/bin/bash
#To run SUTURE on the specified program module.
#$1: ".bc" file
#$2: entry point config file

nohup opt -load llvm_analysis/MainAnalysisPasses/build_dir/SoundyAliasAnalysis/libSoundyAliasAnalysis.so -dr_checker -entryConfig=$2 -outputFile=$2.warn.json -instrWarnings=$2.iwarn.json $1 -o /dev/null >$2.log 2>&1 &