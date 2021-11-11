#!/usr/bin/python

import sys,os

#Extract the raw warnings lines from the log file (in case the log is very large).
def ext_warns_raw(log):
    global warns
    is_warn = False
    with open(log,'r') as f:
        for l in f:
            if l.startswith('@@@@@@'):
                is_warn = (not is_warn)
                print(l.strip())
            elif is_warn:
                #One line per warning.
                print(l.strip())

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: ./ext_warns.py log')
    else:
        ext_warns_raw(sys.argv[1])
