"""
This script clones and setups llvm and friends in the provided folder.
"""

import argparse
from multiprocessing import cpu_count
import os
import sys


def log_info(*args):
    log_str = "[*] "
    for curr_a in args:
        log_str = log_str + " " + str(curr_a)
    print(log_str)


def log_error(*args):
    log_str = "[!] "
    for curr_a in args:
        log_str = log_str + " " + str(curr_a)
    print(log_str)


def log_warning(*args):
    log_str = "[?] "
    for curr_a in args:
        log_str = log_str + " " + str(curr_a)
    print(log_str)


def log_success(*args):
    log_str = "[+] "
    for curr_a in args:
        log_str = log_str + " " + str(curr_a)
    print(log_str)
    

LLVM_GIT_HUB_BASE = "https://github.com/llvm-mirror/"


def setup_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('-b', action='store', dest='target_branch', default='release_90',
                        help='Branch (i.e. version) of the LLVM to setup. Default: release_90 e.g., release_90')

    parser.add_argument('-o', action='store', dest='output_folder',
                        help='Folder where everything needs to be setup.')

    return parser


def usage():
    log_error("Invalid Usage.")
    log_error("Run: python ", __file__, "--help", ", to know the correct usage.")
    sys.exit(-1)


def main():
    arg_parser = setup_args()
    parsed_args = arg_parser.parse_args()
    # step 1: Setup common dictionary
    reps_to_setup = {'tools': ['clang'], 'projects': ['compiler-rt', 'libcxx', 'libcxxabi', 'openmp']}
    if parsed_args.output_folder is None:
        usage()
    base_output_dir = os.path.join(parsed_args.output_folder, "llvm")
    target_branch = parsed_args.target_branch
    log_info("Preparing setup in:", parsed_args.output_folder)
    backup_dir = os.getcwd()
    log_info("Cloning LLVM...")
    os.system('mkdir -p ' + str(base_output_dir))
    git_clone_cmd = "git clone " + LLVM_GIT_HUB_BASE + "llvm" + " -b " + \
                    str(target_branch) + " " + base_output_dir
    os.system(git_clone_cmd)

    for curr_folder in reps_to_setup:
        rep_folder = os.path.join(base_output_dir, curr_folder)
        for curr_rep in reps_to_setup[curr_folder]:
            dst_folder = os.path.join(rep_folder, curr_rep)
            git_clone_cmd = "git clone " + LLVM_GIT_HUB_BASE + str(curr_rep) + " -b " + \
                            str(target_branch) + " " + dst_folder
            log_info("Cloning ", curr_rep, " repo.")
            os.system(git_clone_cmd)

    log_success("Cloned all the repositories.")

    log_info("Build llvm...")
    build_dir = os.path.join(base_output_dir, "build")
    log_info("Trying to build in ", build_dir)
    os.system('mkdir -p ' + build_dir)
    os.chdir(build_dir)
    os.system('cmake ..')
    multi_proc_count = cpu_count()
    if multi_proc_count > 0:
        log_info("Building in multiprocessing mode on ", multi_proc_count, " cores.")
        os.system('make -j' + str(multi_proc_count))
    else:
        log_info("Building in single core mode.")
        os.system('make')
    log_success("Build Complete.")
    print("")
    os.chdir(backup_dir)
    with open('env.sh','w') as ef:
        ef.write("export LLVM_ROOT=" + os.path.abspath(build_dir) + "\n")
        ef.write("export PATH=$LLVM_ROOT/bin:$PATH")
    log_success("IMPORTANT: We have generated the " + backup_dir + "/env.sh which will set environment variables for SUTURE.")
    log_success("IMPORTANT: Be sure to set the ENV variables before building/using SUTURE, with \"source " + backup_dir + "/env.sh\".")
    print("")
    log_success("Setup Complete.")

if __name__ == "__main__":
    main()