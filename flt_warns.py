#!/usr/bin/python

import sys,os
import re

#warning groups
grps = []
#The user-specified pattern to match the traces
regex = None

def is_regex_valid(s):
    global regex
    try:
        regex = re.compile(s)
    except re.error:
        return False
    return True

#Output the filtered warning report.
def output():
    global grps
    grp_cnt = 0
    for grp in grps:
        print('=========================GROUP %d (%d - %d)=========================' % (grp_cnt, grp['order'][0], grp['order'][1]))
        print('#####Warned Insts#####')
        for tgt in grp['target']:
            print(tgt)
        print('######################')
        print('')
        #Print the warnings
        war_cnt = 0
        for war in grp['warns']:
            print('++++++++++++++++WARN %d (%d - %d)++++++++++++++++' % (war_cnt, war['order'][0], war['order'][1]))
            print(war['target'])
            #Print the traces of this warning
            tr_cnt = 0
            for tr in war['tr']:
                print('********Trace %d(%d)********' % (tr_cnt, tr['order']))
                print('\n'.join(tr['seq']))
                print('')
                tr_cnt += 1
            war_cnt += 1
        grp_cnt += 1

def is_tr_fp(tr):
    global regex
    seq = ''.join(tr['seq'])
    match = re.search(regex,seq)
    return (not not match)

#Read all the traces of the current warning.
#pre-cond: we're at the header line of the 1st trace of the current warning
#Return: the next line after the blank line ending the last trace in the warning. 
def read_traces(hrep,warn):
    while True:
        ln = hrep.readline().strip()
        if '**Trace' in ln:
            #This is the start of a new trace, create a trace and record some meta info.
            tr = {'order':0,'seq':[]}
            tr['order'] = int(ln[ln.find('(') + 1 : ln.find(')')])
            #Read in the instruction sequence of the taint trace (up to next blank line).
            seq = []
            while True:
                ln = hrep.readline().strip()
                if not ln:
                    break
                seq.append(ln)
            tr['seq'] = seq
            #Now decide whether this trace matches the user-specified pattern, if not, include it in the warning.
            if not is_tr_fp(tr):
                warn['tr'].append(tr)
        else:
            #This means we have read in all the traces of the current warning.
            return ln

#Read all the warnings belonging to the current group.
#pre-cond: we're at the line after the header line of the 1st warning of the group.
#Return: the first non-blank line after all warnings of the current group. 
def read_warns(hrep,grp):
    while True:
        #Create a new warning
        warn = {'target' : '', 'tr' : [], 'order' : []}
        #Collect the string of the warned inst, which is the line below the warning header line.
        warn['target'] = hrep.readline().strip()
        #Read in the traces of this warning.
        rl = read_traces(hrep,warn)
        #Add the warning to the group if it has any valid traces.
        if len(warn['tr']) > 0:
            #Calculate the order range of the warning.
            ords = [x['order'] for x in warn['tr']]
            warn['order'] = [min(ords),max(ords)]
            #Enqueue
            grp['warns'].append(warn)
        if not '++WARN' in rl:
            return rl
        #Continue to process the next warning.

#Read in the warning report, group by group.
def read_warn_report(fp):
    global grps
    with open(fp,'r') as hrep:
        while True:
            #Locate the starting line of the 1st warning in the current group.
            grp_tgts = []
            while True:
                ln = hrep.readline().strip()
                if not ln:
                    ln = hrep.readline().strip()
                    if not ln:
                        #EOF reached
                        return
                if '++WARN' in ln:
                    #1st warning header reached
                    break
                if ln.startswith('('):
                    #These are the warned inst lines of this group.
                    grp_tgts.append(ln)
            #We are at the 1st warning header, now create a new group read in all its warnings.
            grp = {'warns': [], 'order' : [], 'target' : []}
            rl = read_warns(hrep, grp)
            #Enqueue the grp to the global record if it contains any valid warnings.
            if len(grp['warns']) > 0:
                #Calculate the order range of the group.
                ords0 = [x['order'][0] for x in grp['warns']]
                ords1 = [x['order'][1] for x in grp['warns']]
                grp['order'] = [min(ords0),max(ords1)]
                #Summarize the target insts of the group.
                tgts = set([x['target'] for x in grp['warns']])
                grp['target'] = sorted(list(tgts))
                grps.append(grp)
            if not rl:
                return

#This script intends to filter out all false alarm taint traces containing a given pattern, and re-generate a filtered report.
#A pattern is formulated with a python regular expression that is used to match the plain "trace" texts in the warning report.
#Note that this script will strip all linebreaks of the "trace" texts for RE matching (to avoid the hassle of multi-line RE matching).
#An example pattern:
#'-> kbase_mmu_insert_pages_no_flush(?! )((?!\#CTX\#).)*mali_kbase_mmu\.c#1343'
#It means as long as a trace goes through line 1343 in 'mali_kbase_mmu.c' in the function 'kbase_mmu_insert_pages_no_flush', it will be filtered out.
#Any RE can be used, be sure to check the actual texts in the warning report, and make good use of "lookaround" feature of python RE!

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print('Usage: ./warns_filter.py warns_file pattern')
    else:
        if is_regex_valid(sys.argv[2]):
            read_warn_report(sys.argv[1])
            output()
        else:
            print('Invalid regular expression provided: ' + sys.argv[2])