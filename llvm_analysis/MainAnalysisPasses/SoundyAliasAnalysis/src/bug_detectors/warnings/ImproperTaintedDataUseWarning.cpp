//
// Created by machiry on 1/31/17.
//

#include <InstructionUtils.h>
#include "bug_detectors/warnings/ImproperTaintedDataUseWarning.h"

using namespace llvm;

namespace DRCHECKER {

    void ImproperTaintedDataUseWarning::printCompleteWarning(llvm::raw_ostream &O) const {
        O << this->warning_string << ", detected by:" << this->found_by << "\n";
        O << "  at: ";
        InstructionUtils::printInst(this->target_instr,O);
        O << "  Call Context:";
        for(Instruction *currCallSite : this->callSiteTrace) {
            O << "   ";
            InstructionUtils::printInst(currCallSite,O);
        }
        O << "  Object containing tainted data: " << InstructionUtils::getValueStr(this->targetObj) << "\n";
    }

    void ImproperTaintedDataUseWarning::printWarning(llvm::raw_ostream &O) {
        O << "\"warn_data\":{";
        O << "\"by\":\"";
        O << InstructionUtils::escapeJsonString(this->found_by);
        O << "\",";
        O << "\"warn_str\":\"";
        O << InstructionUtils::escapeJsonString(this->warning_string);
        O << "\",";
        InstLoc il(this->target_instr,&this->callSiteTrace);
        printInstlocJson(&il,O);
        int i = 0;
        for (std::vector<InstLoc*> *trace : this->traces) {
            if (trace == nullptr) {
                continue;
            }
            O << ",\"inst_trace_" << i++ << "\":";
            printInstlocTraceJson(trace,O);
        }
        O << ",\"tainted_obj\":\"" << InstructionUtils::escapeValueString(this->targetObj) << "\"";
        O << "}\n";
    }
}
