# SUTURE

SUTURE is a static points-to and high-order taint analysis tool (for C) based on LLVM IR and built upon [Dr. Checker](https://github.com/ucsb-seclab/dr_checker) (many thanks to its creators!),
two highlights are:  

- **High-Precision**: Multiple practical and/or innovative precision enhancements packed, SUTURE is inter-procedure, flow-, contex-, field-, index-, and opportunistically path-sensitive, with on-the-fly memory SSA construction, multi-source multi-sink pairing, careful pointer arithmetic handling and indirect call resolution for Linux kernels.
- **High-Order**: SUTURE is able to construct high-order taint flows and discover high-order taint vulnerabilities (e.g., the user input flows to a global variable in the 1st syscall invocation, then the global variable flows to a sensitive statement in the 2nd syscall invocation, making a 2nd-order taint vulnerability).  

We name it SUTURE in the hope that it can be surgically precise, while being able to stitch multiple syscalls/entry functions together to construct high-order data flows. For more details please refer to our paper: [Statically Discovering High-Order Taint Style Vulnerabilities in OS Kernels](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf) in *ACM CCS'21*.

## 0x0 Setup  

First clone the repo:  
`~$ git clone https://github.com/seclab-ucr/SUTURE.git suture`  

Then setup the LLVM environment for SUTURE:  
`~$ cd suture`  
`~/suture$ python setup_suture.py -o ../suture_deps`  
**Options** (for `setup_suture.py`):  
- `-b` specifies the branch name of LLVM to be set up for SUTURE, it defaults to "release_90" (i.e., LLVM 9.0) in [this LLVM mirror repo](https://github.com/llvm-mirror/llvm).
- `-o` specifies the folder to host all stuff required by SUTURE (e.g., LLVM), use any folder you prefer.  
  
Depending on your hardware, the LLVM setup may take quite some time. After it finishes, a srcipt file named `env.sh` will be generated under the SUTURE root folder, it contains commands to set the environment variables used by SUTURE.  
**IMPORTANT**: Be sure to activate this `env.sh` every time before building/using SUTURE (you can also add its contained commands to *.bashrc* for automatic activation upon shell login)!  
`~/suture$ source env.sh`

Next we're gonna build SUTURE:  
`~/suture$ cd llvm_analysis`  
`~/suture/llvm_analysis$ ./build.sh`  
Upon a successful build, SUTURE is ready to use.

## 0x1 Vulnerability Discovery w/ an Example  

SUTURE can be used to discover high-order taint vulnerabilities out-of-the-box, in this section we walk through this process w/ an example (e.g., the motivating example as shown in Section 2.1 in our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf)).  

### 0x10 Prepare the Input  

To discover vulnerabilities SUTURE requires two types of input: (1) a program module compiled to LLVM bitcode (e.g., a *.bc* file), and (2) a configuration file for the module that manifests its entry functions and user-controlled arguments.  

Let's first prepare the LLVM bitcode for our motivating example:  
`~/suture$ cd benchmark`  
`~/suture/benchmark$ ./gen.sh motivating_example`  
**NOTE**: for convenience we provide `gen.sh` to compile a *.c* to *.bc* and *.ll* (human readable LLVM bitcode), with `-O1` optimization level.  
Now we should have the *motivating_example.bc* under the same *benchmark* folder, that's the input program module for SUTURE.  

Then it comes to the configuration file, we have already prepared one for the  motivating example:  
```
~/suture/benchmark$ cat conf_motivating_example  
entry0 MY_IOCTL 1  
entry1 NULL_ARG  
entry2 NULL_ARG  
```  
**Explanation**: Each line in the config file describes the information of one entry function (e.g., the top-level function w/o callers and usually serves as the external interface) in the program module, it contains up to 3 space-separated tokens:  
- [func_name] The name of the entry function (e.g., "entry0" is one entry function in *motivating_example.c*)  
- [func_type] The type of the entry function, we often use two types: (1) NULL_ARG means no function parameters are user-controllable, and (2) MY_IOCTL by default means the last parameter is user-controllable (e.g., to match the usual semantics of the *ioctl()* functions of Linux device drivers). However, the user_controllable parameters of MY_IOCTL can also be arbitrarily specified by additional arguments (see below).
- [additional_args] For now only MY_IOCTL accepts an additional argument, in the RE form of \d+(_\d+)\*, specifying which function parameters are user-controllable. Once provided, this argument will override the default behavior of MY_IOCTL (i.e., the last parameter is user-controlled). For example, if *entry_x()* has 4 parameters (from left to right: parameter 0, 1, 2 and 3) and the parameter 0 and 2 are provided by user, we can specify it in the config like `entry_x MY_IOCTL 0_2`.  

So as shown above, *conf_motivating_example* specifies that there are three entry functions in *motivating_example.c*: *entry0* (parameter 1 is user-controlled), *entry1* and *entry2* (no user-controlled parameters). This matches the code of the motivating example:  
```
~/suture/benchmark$ cat -n motivating_example.c
     1  #include<stdio.h>
     2  #include<stdlib.h>
     3
     4  typedef struct data {
     5      __int32_t a;
     6      char b[4];
     7  } data;
     8  data d;
     9
    10  int __attribute__((noinline)) foo(int n, char c) {
    11      if (n == 0) {
    12          d.b[1] = c;
    13      }
    14      return 0;
    15  }
    16
    17  int entry0(int cmd, char user_input) {
    18      switch (cmd)
    19      {
    20      case 0:
    21          d.b[0] = user_input;
    22          break;
    23      default:
    24          foo(cmd,user_input);
    25      }
    26      return 0;
    27  }
    28
    29  int __attribute__((noinline)) bar(char *p) {
    30      *(p+4) += 0xf0; //Overflow site (1)
    31      return 0;
    32  }
    33
    34  int entry1() {
    35      bar((char*)&d);
    36      d.b[0] = 0;
    37      return 0;
    38  }
    39
    40  int entry2() {
    41      char a[8];
    42      a[0] = d.b[1] + 0xf0; //Overflow site (2)
    43      printf("%c\n",a[0]);
    44      return 0;
    45  }
    46
    47  //This "main()" exists only to make the file compilable, we can assume that this module
    48  //only has three entry functions which are entry0 - entry2 defined above.
    49  int main(int argc, char **argv) {
    50      entry0(argc,**argv);
    51      entry1();
    52      entry2();
    53      return 0;
    54  }

```

### 0x11 Run the Analysis  

Once the program bitcode and the entry config file are ready, we can run SUTURE to discover taint vulnerabilities:  
`~/suture$ ./run_nohup.sh benchmark/motivating_example.bc benchmark/conf_motivating_example`  
**Explanation**: *run_nohup.sh* is a simple script invoking the compiled LLVM analysis passes of SUTURE:  
```
~/suture$ ./run_nohup.sh [path/to/program.bc] [path/to/entry_func_config]
```  

Once started, depending on the actual hardware and the complexity of the target program, the required time for SUTURE to finish the analysis and vulnerability discovery varies a lot. A simple program like our motivating example usually finishes instantly, though.  
**Decide whether the analysis finishes**: During execution, SUTURE keeps logging into a file under the same directory of the *entry config file*, suppose the config file path is */path/to/conf_program*, the log file will be */path/to/conf_program.log*. We can decide whether the analysis finishes by monitoring the log:  
`~/suture$ grep "Bug Detection Phase finished" benchmark/conf_motivating_example.log`

### 0x12 Inspect the Output  
The aforementioned log file is also SUTURE's output, SUTURE will embed its discovered potential vulnerabilities in the log file, which can be extracted and organized into a final warning report after the analysis finishes:  
`~/suture$ ./ext_warns.sh benchmark/conf_motivating_example.log`  
**Explanation**: *ext_warns.sh* will extract all warnings (in JSON) embedded in the given log file, re-organize and pretty-print them into the final warning reports. The warning reports will be put into a folder under the same path of the log file, suppose the log file is */path/to/conf_program.log*, the warning report folder will be */path/to/warns-conf_program-yyyy-mm-dd*.  
```
~/suture$ ls benchmark/warns-conf_motivating_example-2021-11-10/
all  int_overflow  taint_data_use  taint_loopbound  taint_ptr_def
```  
In the folder there are 5 warning reports, *all* contains all types of warnings grouped together according to their data flow relationship, while other reports only contain specific types of warnings (e.g., integer overflow, tainted pointer dereference, etc.), more details about how we group warnings can be found in our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf) (Section 4). We usually only use the unified report *all*.  
```
~/suture$ cat -n benchmark/warns-conf_motivating_example-2021-11-10/all
     1  =========================GROUP 0 (2 - 2)=========================
     2  #####Warned Insts#####
     3  (u'motivating_example.c', 30, [u'IntegerOverflowDetector'])
     4  ######################
     5
     6  ++++++++++++++++WARN 0 (2 - 2)++++++++++++++++
     7  IntegerOverflowDetector says: motivating_example.c@30 (bar :   %add = add i8 %0, -16, !dbg !31)
     8  ********Trace 0(2)********
     9  #####CTX##### entry0
    10  entry0 (motivating_example.c@18)
    11  #####INSTS#####
    12  >>>>>>>>>>>>>>>>>>tag: 0x55b206570420 tf: 0x55b20695b1b0 (2)>>>>>>>>>>>>>>>>>>
    13  motivating_example.c@18 (  %cond = icmp eq i32 %cmd, 0, !dbg !31)
    14  motivating_example.c@21 (  store i8 %user_input, i8* getelementptr inbounds (%struct.data, %struct.data* @d, i64 0, i32 1, i64 0), align 4, !dbg !32, !tbaa !34)
    15  #####CTX##### entry1 -> bar
    16  entry1 (motivating_example.c@35)
    17  ----> (motivating_example.c@35 :   %call = tail call i32 @bar(i8* bitcast (%struct.data* @d to i8*)), !dbg !27)
    18  bar (motivating_example.c@30)
    19  #####INSTS#####
    20  >>>>>>>>>>>>>>>>>>tag: 0x55b2065e7050 tf: 0x55b2068174f0 (1)>>>>>>>>>>>>>>>>>>
    21  motivating_example.c@30 (  %0 = load i8, i8* %add.ptr, align 1, !dbg !31, !tbaa !32)
    22  motivating_example.c@30 (  %add = add i8 %0, -16, !dbg !31)
    23
```  
**Explanation**: At a high level, the warning report contains some warning **groups**, each group contains several **warnings**, and each warning contains several taint **traces** that originate from a user input and sink to a same sensitive program statement. In other words, one **warning** is raised for a certain program statement and of a specific type (e.g., integer overflow), while a **group** contains multiple closely related warnings from the data flow perspective (see Section 4 in our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf)), thus a **group** may have multiple warned program statements and include different warning types.  

Take the above warning report as an example:  
- Line 1: The header line of a warning group, the format is `===GROUP No. (min_order - max_order)===`, where `min_order` is the minimal order (e.g., simply put, *order* is the times of the entry function invocations required in the taint propagation, see Section 3.2 in our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf) for a more formal definition.) of the taint traces within this group, and `max_order` the max.  
- Line 2-4: A summary of the warned program statements and warning types of this group.  
- Line 6: The header line of a warning, following the same format as the group header line, but note that the `WARN No.` is local to its group.  
- Line 7: The warned program statement and type of this warning (e.g., line 30 in *motivating_example.c*).  
- Line 8: The header line of a taint trace of the warning, following the format `***Trace No. (order)***`, a taint trace always has a unique *order* that can be calculated (e.g., not a range).
- Line 9-22: The detailed statement/instruction sequence of this taint trace. The sequence is organized in some consecutive context-inst segments, for example, assume we have 10 instructions in the sequence and the first 6 of them locate in *A()*, and the remaining 4 in *B()*, which is a callee of *A()*. In this situation we will have two context-inst segments: the first one contains the leading 6 instructions under the calling context *A()*, and the second contains the remaining 4 under the calling context *A()->B()*.
Coming back to our motivating example warning report, Line 9-14 is the 1st segment in the trace, where we need to invoke *entry0()* (Line 10) and walk through two instructions (Line 13-14) in *entry0()* (so that *user_input* of *entry0()* is propagated to the global variable *d.b[0]* in *motivating_example.c*), then Line 15-22 is the second segment, where we need to invoke *entry1()* first (Line 16), which then calls *bar()* (Line 17), and within *bar()* (Line 18) we need to go through two program statements (Line 21-22) to finish the taint propagation and trigger the vulnerability (*d.b[0]* is propagated to the overflow site (1) in *motivating_example.c*). Since we need two entry function invocations (e.g., first *entry0()* then *entry1()*), this taint trace is 2nd-order.  
- Line 12, 20: These special lines are internally used by us for debugging purposes.  

The warning report pinpoints a valid integer overflow vulnerability in the motivating example, while avoiding potential false alarms that a less precise static analysis tool may generate, details can be found in Section 2.1 of our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf).  

## 0x2 Other Helpful Utilities  

This repo also contains some other tools/scripts that you may find useful.  

### 0x20 Entry Point Identifier (for Linux Device Drivers)  

`~/suture$ python llvm_analysis/AnalysisHelpers/EntryPointIdentifier/entry_point_identifier.py /path/to/prog_module.bc`  
`~/suture$ cat /path/to/prog_module.bc.all_entries`  
**Explanation**: This script can identify some common entry functions in a Linux device driver module (e.g., *ioctl()*, *read()*, *write()*, etc.), which helps the construction of the entry config file as the input to SUTURE. This utility is mostly implemented by the original [Dr. Checker](https://github.com/ucsb-seclab/dr_checker) based on some kernel domain knowledges (e.g., specific data structures like *file_operations* used to define driver entry points), we then made some improvements (e.g., make the heuristics more robust).  

### 0x21 False Alarm Filter  

`~/suture$ python flt_warns.py /path/to/warn_report [Regex] > /path/to/filtered_warn_report`  
**Explanation**: From our experience, many false alarms in the warning report often share a same problematic sub-taint-trace (see Section 6.3 in our [paper](https://www.cs.ucr.edu/~zhiyunq/pub/ccs21_static_high_order.pdf)). As long as the warning reviewer inspects one false alarm and recognizes the FP-inducing sub-trace, naturally, she can try to automatically exclude all other similar false alarms containing the same sub-trace, reducing the reviewer-perceived false alarm rate.
For this purpose, we provide this simple *flt_warns.py* that takes the original warning report and a python regular expression as inputs, it then will match the RE against every taint trace in the report, once matched, the taint trace will be treated as a false alarm. The script will generate a new filtered warning report excluding all matched taint traces.

## 0x3 Possible Questions and Answers  

### 0x30 Use SUTURE as a general-purpose static analysis?  

You might be interested in using SUTURE as a general-purpose static analysis (e.g., get the points-to/taint set of a variable at a certain program location), this is for sure doable, but unlike the vulnerability discovery, you need to get hands dirty and dive into the code of SUTURE to be familiarized with the main data structures it uses and some important functions. I hope the following tips can help:  

- [Read [the original Dr. Checker paper](https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/machiry)] SUTURE is based on Dr. Checker and inherits its high-level architecture, design principles and many important code and data structures, for brevity we omit details on Dr. Checker's design and implementation in our paper, but they are very important to understand the codebase. I strongly recommend to read [the Dr. Checker paper](https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/machiry) first, which contains these important details.  
- [Focus on the important source files] All the points-to/taint records of top-level LLVM variables locate in *suture/llvm_analysis/MainAnalysisPasses/SoundyAliasAnalysis/include/ModuleState.h*, while all such information for address-taken memory objects are in *llvm_analysis/MainAnalysisPasses/SoundyAliasAnalysis/include/AliasObject.h*. I suggest to focus on these two files and the APIs defined within them to retrieve the points-to/taint records. Last but not least, the start point of all SUTURE's LLVM analysis passes (e.g., *runOnModule()*) is in *llvm_analysis/MainAnalysisPasses/SoundyAliasAnalysis/src/SoundyAliasAnalysis.cpp*.  

### 0x31 Adapt SUTURE to newer LLVM Versions?  

LLVM evolves very quickly, without a guarantee on backward compatiability. So very likely you will encounter some compilation errors when trying to build SUTURE with a newer LLVM version (e.g., > 9.0). But fortunately, such compilation errors are usually easy to resolve (e.g., often the case we just need to replace the out-of-date LLVM APIs with the newer ones).
So basically, to adapt SUTURE to a newer LLVM version, first we need to setup a newer LLVM in 0x0 (e.g., need to modify the *setup_suture.py* to clone LLVM repo from an active source and specify the newer branch name), and then try to build SUTURE against it, solving the encountered compilation errors.