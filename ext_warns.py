#!/usr/bin/python

#Extract and process the warnings in the log output.

import sys,os
import datetime
import json

warns = []
jwarns = {}

def get_last_func_name(tr):
    if not tr:
        return None
    ctx = tr[-1].get('ctx',[])
    if ctx:
        return ctx[-1].get('at_func',None)
    return None

def get_warned_inst(j):
    return (j.get('at_file','unk_file'),j.get('at_line',-2))

def get_trace_suffix(tr):
    suff = []
    ctx = []
    for i in range(len(tr)-1,0,-1):
        #Get the context str of current inst.
        cur_ctx = get_ctx_strs(tr[i].get('ctx',[])) 
        if i == len(tr) - 1:
            ctx = cur_ctx
        elif ctx != cur_ctx:
            #We have collected the inst trace beloging to the last calling context.
            break
        #Append current inst to the suffix, in the reverse order.
        suff.insert(0,(tr[i].get('at_file','UNK'),tr[i].get('at_line',-1)))
    return suff

#If all traces in the warning share a same suffix trace (i.e. the inst trace in the last calling context), return that suffix trace,
#otherwise return None.
#Note that there is a bottom line: at least all traces of a warning end with one same inst - the warned inst, so the suffix contains
#at least one inst.
#The trace is in the format [(file,line),...]
def get_warn_suffix_trace(j):
    wi = get_warned_inst(j)
    fu = j.get('at_func','unk_func')
    trsk = [s for s in j if s.startswith('inst_trace')]
    suff = []
    for k in trsk:
        tr = j.get(k,{}).get('tr',[])
        last_func = get_last_func_name(tr)
        cur = get_trace_suffix(tr)
        if not cur:
            cur = [wi]
        elif last_func and last_func == fu:
            if cur[-1] != wi:
                cur.append(wi)
        else:
            cur = [wi]
        if len(suff) == 0 or str(suff)[1:].endswith(str(cur)[1:]):
            #Current is the 1st trace we have, or current trace has a shorter suffix in common.
            suff = cur
        elif not str(cur)[1:].endswith(str(suff)[1:]):
            #Incompatiable, no common suffix.
            return [wi]
    return suff

#Return the first inst of the inst trace belonging to the last calling context.
def get_initial_trace_inst(j):
    suff = get_warn_suffix_trace(j)
    return (suff[0][0],suff[0][1]) if suff else get_warned_inst(j)

def ext_warns(log, *tys):
    global warns
    is_warn = False
    cnt = 0
    cnt_total = 0
    with open(log,'r') as f:
        for l in f:
            if l.startswith('@@@@@@'):
                is_warn = (not is_warn)
            elif is_warn:
                cnt_total += 1
                if tys and all([l.find(ty) < 0 for ty in tys]):
                    continue
                #One line per warning.
                l = l.strip()
                if l.startswith('\"warn_data\":'):
                    #warns.append(l)
                    j = json.loads(l[12:])
                    #Calculate the 'key' of the warning..
                    wi = get_warned_inst(j)
                    fi = get_initial_trace_inst(j)
                    jwarns.setdefault(wi,{}).setdefault(fi,[]).append(j)
                    cnt += 1
                    if cnt % 10 == 0:
                        sys.stderr.write(str(cnt) + '/' + str(cnt_total) + '\n') 
    #TODO: Do some filtering, grouping, etc according to the warning json content.

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

def dump_warns_raw():
    global warns
    #Dump the warning
    for l in warns:
        print(l)

#Below are for msm kernel code
PATH_PREFIX_MSM = 'private/msm-google/'
#Special hack for msm sound driver path.
TECH_AUDIO_PREFIX = 'techpack/audio/'
URL_PREFIX_MSM = 'https://android.googlesource.com/kernel/msm/+/refs/tags/android-10.0.0_r0.56/'
URL_MSM_EXTRA_PREFIX = 'https://android.googlesource.com/kernel/msm-extra/+/refs/tags/android-10.0.0_r0.56/'

def mkurl_msm(j):
    fp = j.get('at_file','')
    ln = j.get('at_line',0)
    if fp.startswith(PATH_PREFIX_MSM):
        fp = fp[len(PATH_PREFIX_MSM):]
    pref = URL_PREFIX_MSM
    if fp.startswith(TECH_AUDIO_PREFIX):
        fp = fp[len(TECH_AUDIO_PREFIX):]
        pref = URL_MSM_EXTRA_PREFIX
    return pref + fp + '#' + str(ln)

#Below are for Xiaomi kernel repo
URL_PREFIX_XM = 'https://github.com/MiCode/Xiaomi_Kernel_OpenSource/blob/1d7e679cb766e78e28f8cd11f3b7aff1a9bddeaf/'

def mkurl_xm(j):
    fp = j.get('at_file','')
    fp = fp.replace('\\','')
    if fp.startswith('../'):
        fp = fp[3:]
    ln = j.get('at_line',0)
    return URL_PREFIX_XM + fp + '#L' + str(ln)

#Below are for huawei kernel repo
URL_PREFIX_HW = 'https://github.com/cpumask/huawei_NOH_AN00_kernel/blob/master/'

def mkurl_hw(j):
    fp = j.get('at_file','')
    fp = fp.replace('\\','')
    if fp.startswith('kernel/'):
        fp = fp[7:]
    ln = j.get('at_line',0)
    return URL_PREFIX_HW + fp + '#L' + str(ln)

#Below are for huawei kernel repo
URL_PREFIX_SM = 'https://github.com/cpumask/SM-G780F-CIS-RR-Kernel/blob/master/'

def mkurl_sm(j):
    fp = j.get('at_file','')
    fp = fp.replace('\\','')
    ln = j.get('at_line',0)
    return URL_PREFIX_SM + fp + '#L' + str(ln)

def mkurl_default(j):
    fp = j.get('at_file','')
    fp = fp.replace('\\','')
    ln = j.get('at_line',0)
    return fp + '@' + str(ln)

def mkurl(j):
    return mkurl_default(j)

def get_ctx_strs(ctx):
    if (not ctx) or len(ctx) == 0:
        return []
    chain = []
    chain_comp = []
    is_entry = True
    for inst in ctx:
        func = inst.get('at_func','UNK_FUNC')
        furl = mkurl(inst)
        if is_entry:
            chain.append(func)
            s = func + ' (' + furl + ')'
            chain_comp.append(s)
        else:
            #Record the callsite info.
            ins = inst.get('instr','UNK_INST')
            s = '----> (' + furl + ' : ' + ins + ')'
            chain_comp.append(s)
        is_entry = (not is_entry)
    chain_comp.append(' -> '.join(chain))
    return chain_comp

def pprint_trace(tr):
    cur_ctx = None
    for ins in tr:
        #First we need to output the context of this inst - if we haven't done so already.
        ctx = get_ctx_strs(ins.get('ctx',[]))
        if (not cur_ctx) or cur_ctx != ctx:
            print('#####CTX##### ' + ctx[-1])
            for i in range(len(ctx)-1):
                print(ctx[i])
            print('#####INSTS#####')
            cur_ctx = ctx
        #Is current inst a high-order "breakpoint"?
        tag = ins.get('tag','')
        tf = ins.get('tf','')
        if tag:
            print('>>>>>>>>>>>>>>>>>>tag: ' + tag + ' tf: ' + tf + ' (' + str(ins.get('icnt',0)) + ')>>>>>>>>>>>>>>>>>>')
        #Now print current inst.
        furl = mkurl(ins)
        inst = ins.get('instr','UNK_INST')
        print(furl + ' (' + inst + ')')

#Print out the json bug report in a concise and easily readable way.
def pprint(j):
    ty = j.get('by','UNK')
    func = j.get('at_func','UNK_FUNC')
    furl = mkurl(j)
    inst = j.get('instr','UNK_INST')
    #Print heading part: the warned instr and its src location.
    print(ty + ' ' + furl + ' (' + func + ' : ' + inst + ')')
    #Print the taint trace to the warned instr.
    trsk = [s for s in j if s.startswith('inst_trace')]
    cnt = 0
    #TODO: Sort the traces within the warning.
    for k in trsk:
        tr = j.get(k,{})
        print('********Trace %d(%d)********' % (cnt, tr.get('order',0)))
        pprint_trace(tr.get('tr',[]))
        cnt += 1
        print('')

#Calculate the 'order' of a warning, which is the average of the 'order' of each trace.
def get_warn_order_avg(jw):
    orders = [jw.get(s,{}).get('order',0) for s in jw if s.startswith('inst_trace')]
    if len(orders) == 0:
        return 0
    jw['order'] = sum(orders)/float(len(orders))
    return jw['order']

#Calculate the range of the 'order' of a warning, which is bound w/ the min/max of the 'order' of each trace.
def get_warn_order_range(jw):
    orders = [jw.get(s,{}).get('order',0) for s in jw if s.startswith('inst_trace')]
    if not orders:
        orders = [0]
    jw['order'] = (min(orders),max(orders))
    return jw['order']

#Sort the warnings inside one group by 'order' and return the 'order' of the whole group.
def sort_one_group(g):
    if len(g) == 0:
        return (0,0)
    orders = [get_warn_order_range(j) for j in g]
    g.sort(key = lambda x : x['order'][0] * 1000 + x['order'][1], reverse = True)
    return (min([x[0] for x in orders]), max([x[1] for x in orders]))

#(1) Sort the warn groups by the "order" (e.g. necessary invocation times of entry functions to trigger the bug)
#(2) Sort the warnings inside each group by their "order"
def sort_warn_groups(grps):
    for g in grps:
        g['order'] = sort_one_group(g.get('warns',[]))
    grps.sort(key = lambda x : x['order'][0] * 1000 + x['order'][1], reverse = True)

#The "k" is the warned inst location (e.g. file + line) as used for the 1st layer key in 'jwarns',
#this function returns all the warning types (e.g. int overflow) associated w/ the given inst.
def get_warn_tys(k):
    global jwarns
    s = set()
    for i in jwarns.get(k,{}):
        for j in jwarns[k][i]:
            ty = j.get('by','').split(' ')[0]
            if ty:
                s.add(ty)
    return sorted(list(s))

#Try to group the related warnings (e.g. warnings who share the same root cause)
def group_warns():
    global jwarns
    res = []
    wis = set(jwarns)
    while len(wis) > 0:
        i = wis.pop()
        tmp = []
        for k in jwarns[i]:
            tmp += jwarns[i][k]
        merged = set()
        for j in wis:
            if set(jwarns[j]).intersection(set(jwarns[i])):
                for k in jwarns[j]:
                    tmp += jwarns[j][k]
                merged.add(j)
        wis.difference_update(merged)
        #For debug purpose, print out the merged warned insts.
        merged.add(i)
        ml = list(merged)
        ml.sort(key = lambda x : x[1])
        res.append({'warns' : tmp, 'insts' : map(lambda x : (x[0],x[1],get_warn_tys(x)), ml)})
    sort_warn_groups(res)
    return res

def dump_warns_pretty():
    warn_grps = group_warns()
    gcnt = 0
    hcnt = 0
    for grp in warn_grps:
        if grp['order'][1] > 1:
            hcnt += 1
        print('=========================GROUP %d (%d - %d)=========================' % (gcnt, grp['order'][0], grp['order'][1]))
        print('#####Warned Insts#####')
        #Print all warned insts in this group
        for wi in grp.get('insts',[]):
            print(wi)
        print('######################')
        print('')
        wcnt = 0
        for j in grp.get('warns',[]):
            print('++++++++++++++++WARN %d (%d - %d)++++++++++++++++' % (wcnt, j['order'][0], j['order'][1]))
            pprint(j)
            wcnt += 1
        gcnt += 1
    #Output some quick statistics
    sys.stderr.write('high-order/total: %d/%d\n' % (hcnt, gcnt)) 

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print('Usage: ./ext_warns.py log warn_type_0 warn_type_1 ...')
    else:
        ext_warns(sys.argv[1],*sys.argv[2:])
        dump_warns_pretty()
