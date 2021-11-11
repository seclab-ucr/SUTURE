#!/usr/bin/python

import sys,os
import fileinput

rl = [
    ('SoundyAliasAnalysis/src/AliasAnalysisVisitor.cpp','#define DEBUG_GET_ELEMENT_PTR','//#define DEBUG_GET_ELEMENT_PTR'),
    ('SoundyAliasAnalysis/src/AliasAnalysisVisitor.cpp','#define DEBUG_STORE_INSTR','//#define DEBUG_STORE_INSTR'),
    ('SoundyAliasAnalysis/src/AliasAnalysisVisitor.cpp','#define DEBUG_CAST_INSTR','//#define DEBUG_CAST_INSTR'),
    ('SoundyAliasAnalysis/src/AliasAnalysisVisitor.cpp','#define DEBUG_UPDATE_POINTSTO','//#define DEBUG_UPDATE_POINTSTO'),
    ('SoundyAliasAnalysis/src/AliasAnalysisVisitor.cpp','#define DEBUG_HANDLE_INLINE_POINTER','//#define DEBUG_HANDLE_INLINE_POINTER'),
    ('SoundyAliasAnalysis/src/TaintUtils.cpp','#define DEBUG_ADD_NEW_TAINT_FLAG','//#define DEBUG_ADD_NEW_TAINT_FLAG'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CREATE_DUMMY_OBJ_IF_NULL','//#define DEBUG_CREATE_DUMMY_OBJ_IF_NULL'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_FETCH_POINTS_TO_OBJECTS','//#define DEBUG_FETCH_POINTS_TO_OBJECTS'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CHANGE_HEAPLOCATIONTYPE','//#define DEBUG_CHANGE_HEAPLOCATIONTYPE'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_UPDATE_FIELD_POINT','//#define DEBUG_UPDATE_FIELD_POINT'),
    ('SoundyAliasAnalysis/include/TaintInfo.h','#define DEBUG_UPDATE_FIELD_TAINT','//#define DEBUG_UPDATE_FIELD_TAINT'),
    ('SoundyAliasAnalysis/include/TaintInfo.h','#define DEBUG_FETCH_FIELD_TAINT','//#define DEBUG_FETCH_FIELD_TAINT'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CREATE_EMB_OBJ','//#define DEBUG_CREATE_EMB_OBJ'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CREATE_EMB_OBJ_CHAIN','//#define DEBUG_CREATE_EMB_OBJ_CHAIN'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CREATE_HOST_OBJ','//#define DEBUG_CREATE_HOST_OBJ'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_CREATE_HOST_OBJ_CHAIN','//#define DEBUG_CREATE_HOST_OBJ_CHAIN'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_SPECIAL_FIELD_POINTTO','//#define DEBUG_SPECIAL_FIELD_POINTTO'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_SHARED_OBJ_CACHE','//#define DEBUG_SHARED_OBJ_CACHE'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_INFER_CONTAINER','//#define DEBUG_INFER_CONTAINER'),
    ('SoundyAliasAnalysis/include/AliasObject.h','#define DEBUG_OBJ_COPY','//#define DEBUG_OBJ_COPY'),
    ('Utils/include/InstructionUtils.h','#define TIMING','//#define TIMING'),
]

#Turn on/off the debug switch defined in the src files.
#sys.argv[1]: /path/to/MainAnalysisPasses-folder
def debug_switch(m):
    io = 1
    ir = 2
    if sys.argv[2] != '0':
        #turn on, so we should search for the off state string
        io = 2
        ir = 1
    cr = 0
    for r in rl:
        fp = sys.argv[1] + '/' + r[0]
        if not os.path.exists(fp):
            continue
        cr = cr + 1
        for l in fileinput.input(fp, backup='.bak',inplace = True):
            if l.find(r[io]) >= 0:
                print r[ir]
            else:
                print l.rstrip()
    print 'Replaced: %d' % cr

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print 'Usage: ./debug_switch.py /path/to/MainAnalysisPasses 0|1'
    else:
        if sys.argv[2] == '0':
            debug_switch(0)
        else:
            debug_switch(1)
