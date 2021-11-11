#!/usr/bin/python

import sys,os

#Raw log file content
log = []
#line -> call chain
cc = {}
#lines that are inst events, record the line num.
insts = []

#To match the vim, we change 0-based to 1-based
def println(ln,s):
    print('%-*d: %s' % (10,ln+1,s))

def print_cc(ln,c):
    println(ln,'##CC: ' + '->'.join(c))

def print_inst(ln,s):
    println(ln,'--INST: ' + s)

def print_match(ln,s):
    println(ln,'    ' + s)

#decide whether a line is a inst visit/update event.
def is_inst_line(i):
    global log
    #After seeing a prefix string, we need to match the "!dbg" within the Nth line next, if matched, then it's an inst line.
    pref = [
        'AliasAnalysisVisitor::visit', 0,
        'TaintAnalysisVisitor::visit', 0,
        'updatePointsToObjects for', 0,
        'TaintUtils::updateTaintInfo() for', 0,
        '*********fetchPointsToObjects', 1,
        '*********FieldAccess', 1,
    ]
    if i < 0 or i >= len(log) or log[i].find('!dbg') < 0:
        return False
    for k in range(0,len(pref),2):
        off = pref[k+1]
        if i-off >= 0 and log[i-off].startswith(pref[k]):
            return True
    return False

def inst_analyze():
    global log,insts
    for i in range(len(log)):
        if is_inst_line(i):
            insts.append(i)

#TODO: add context lines to the identified obj lines when appropriate.
def obj_slice(k):
    global log,cc,insts
    #For each tuple entry k, if the matched obj line contains k[1], then we will try to include the context
    #up to the line including k[0] and down to the line including k[2].
    #To to safe and conservative, we will not include the context lines that are out of current inst scope.
    ctx = [
        ('updateFieldPointsTo() for', 'updateFieldPointsTo', 'After updates'),
        ('createEmbObj(): host type', 'createEmbObj', 'createEmbObj(): the embedded obj created'),
    ]
    cc_index = sorted(list(cc))
    cur_cc = 0
    cur_in = -1
    next_in = -1
    i = 0
    while i < len(log):
        if log[i].find(k) >= 0:
            #Print the post-inst visit context of the previous matched line if needed.
            if cur_in > -1 and cur_in + 1 < len(insts) and i >= insts[cur_in + 1]:
                print_inst(insts[cur_in + 1],log[insts[cur_in + 1]])
                cur_in += 1
            #First print the cc history to this matched line.
            while cur_cc < len(cc_index) and i >= cc_index[cur_cc]:
                print_cc(cc_index[cur_cc],cc[cc_index[cur_cc]])
                cur_cc += 1
            #Then print the nearest previous inst visit.
            j = cur_in
            while j + 1 < len(insts) and i >= insts[j+1]:
                j += 1
            if j != cur_in:
                cur_in = j
                print_inst(insts[j],log[insts[j]])
            #INVARIANT: 'cur_in' is the nearest previous inst visit of the current matched obj line.
            #Print the matched obj line w/ necessary contexts.
            has_ctx = False
            #Current inst scope
            ui = (0 if cur_in < 0 else insts[cur_in])
            di = (insts[cur_in+1] if cur_in+1 < len(insts) else len(log))
            for t in ctx:
                if log[i].find(t[1]) >= 0:
                    #Identify the start and the end of the context.
                    up = down = i
                    while t[0] and up > ui and log[up].find(t[0]) < 0:
                        up -= 1
                    while t[2] and down < di and log[down].find(t[2]) < 0:
                        down += 1
                    #print '-----------------' + 'ui:' + str(ui) + ' di:' + str(di) + ' up:' + str(up) + ' down:' + str(down) + ' i:' + str(i)
                    #Printing..
                    for m in range(up,down+1):
                        print_match(m,log[m])
                    i = down
                    has_ctx = True
                    break
            if not has_ctx:
                print_match(i,log[i])
        i += 1

def tag_slice(k):
    pass

#Analyze the call chain at each line in the log.
def cc_analyze():
    global log,cc
    cur_cc = []
    ln = 0
    for l in log:
        #E.g. line format:
        #[TIMING] Start func(5) snd_seq_pool_new: Thu Feb 13 13:50:05 2020  
        #[TIMING] End func(5) snd_seq_pool_new in: 1.122699e+01s 
        if l.startswith('[TIMING] Start func'):
            tks = l.split(' ')
            if len(tks) < 4:
                cur_cc.append('!ERR')
            else:
                cur_cc.append(tks[3][:-1])
            cc[ln] = list(cur_cc)
        elif l.startswith('[TIMING] End func'):
            if len(cur_cc) > 0:
                cur_cc.pop()
            cc[ln] = list(cur_cc)
        ln += 1

def cc_slice():
    global cc
    for i in sorted(list(cc)):
        print_cc(i,cc[i])

#The log file is in general very large, this script tries to slice only information of interest (e.g. all events related to a certain object)
#and output them in a well-organized readable format, so that our life can be made easier when debugging...
if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: ./log_slicer.py log_file key_type(tag/obj) key(ID)')
    else:
        #First read in the log file.
        with open(sys.argv[1],'r') as f:
            for l in f:
                log.append(l[:-1])
        #Preliminary callchain analysis
        cc_analyze()
        if len(sys.argv) < 4:
            cc_slice()
        else:
            inst_analyze()
            k = sys.argv[3]
            if sys.argv[2] == 'tag':
                tag_slice(k)
            elif sys.argv[2] == 'obj':
                obj_slice(k)
            else:
                #By default perform a callchain analysis for each line in the log.
                cc_slice()
