#!/bin/bash
#To collect and classify the warnings from the raw log file.
#$1: path/to/log

#Create a dedicated directory to hold the warnings.
log_pref=${1%/*}
log=${1##*/}
dir=${log_pref}/warns-${log%.*}-$(date +%F)
echo "Make dir: "$dir
mkdir $dir

#Generate a unified bug report including all kinds of supported warnings.
echo "Generate a unified bug report including all warning types..."
python ext_warns.py $1 IntegerOverflowDetector TaintedLoopBoundDetector TaintedPointerDereferenceChecker ImproperTaintedDataUseDetector > $dir/all  
#Extract the various warnings and put them into separate files.
echo "Extract the warnings: IntegerOverflowDetector."
python ext_warns.py $1 IntegerOverflowDetector > $dir/int_overflow  
echo "Extract the warnings: TaintedLoopBoundDetector."
python ext_warns.py $1 TaintedLoopBoundDetector > $dir/taint_loopbound 
echo "Extract the warnings: TaintedPointerDereferenceChecker."
python ext_warns.py $1 TaintedPointerDereferenceChecker > $dir/taint_ptr_def 
echo "Extract the warnings: ImproperTaintedDataUseDetector."
python ext_warns.py $1 ImproperTaintedDataUseDetector > $dir/taint_data_use 
