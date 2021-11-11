//
// Created by machiry on 12/27/16.
//

#include "bug_detectors/TaintedPointerDereference.h"
#include "bug_detectors/warnings/VulnerabilityWarning.h"

using namespace llvm;

#include "TaintUtils.h"

namespace DRCHECKER {

/*#define DEBUG_LOAD_INSTR
#define DEBUG_STORE_INSTR*/
#define ONLY_ONE_WARNING
#define NO_POINTER_CHECK

    void TaintedPointerDereference::visitLoadInst(LoadInst &I) {
        // warning already raised for this instruction.
        if(this->warnedInstructions.find(&I) != this->warnedInstructions.end()) {
            return;
        }
#ifdef DEBUG_LOAD_INSTR
        dbgs() << TAG << " Visiting Load Instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                                      this->currFuncCallSites,
                                                                      srcPointer);
        if(srcTaintInfo == nullptr) {
            srcPointer = srcPointer->stripPointerCasts();
            srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                    this->currFuncCallSites,
                                                    srcPointer);
        }

        // OK, the src pointer is tainted.
        // we are trying to dereference tainted pointer.
        if (srcTaintInfo != nullptr) {
            std::set<std::vector<InstLoc*>*> tchains;
            this->currState.getAllUserTaintChains(srcTaintInfo,tchains);
            if (tchains.empty()) {
                //No taint from user inputs.
                return;
            }
            std::string warningMsg = "Trying to read from a user pointer.";
            VulnerabilityWarning *currWarning = new VulnerabilityWarning(this->currFuncCallSites,
                                                                         &tchains,
                                                                         warningMsg, &I,
                                                                         TAG);
            this->currState.addVulnerabilityWarning(currWarning);
            if(this->warnedInstructions.find(&I) == this->warnedInstructions.end()) {
                this->warnedInstructions.insert(&I);
            }
        }
    }

    void TaintedPointerDereference::visitStoreInst(StoreInst &I) {
        // warning already raised for this instruction.
        if(this->warnedInstructions.find(&I) != this->warnedInstructions.end()) {
            return;
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << TAG << " Visiting Store Instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                                      this->currFuncCallSites,
                                                                      srcPointer);
        if(srcTaintInfo == nullptr) {
            srcPointer = srcPointer->stripPointerCasts();
            srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                    this->currFuncCallSites,
                                                    srcPointer);
        }

        // OK, the src pointer is tainted.
        // we are trying to dereference tainted pointer.
        if (srcTaintInfo != nullptr) {
            std::set<std::vector<InstLoc*>*> tchains;
            this->currState.getAllUserTaintChains(srcTaintInfo,tchains);
            if (tchains.empty()) {
                //No taint from user inputs.
                return;
            }
            std::string warningMsg = "Trying to write to a user pointer.";
            VulnerabilityWarning *currWarning = new VulnerabilityWarning(this->currFuncCallSites,
                                                                         &tchains,
                                                                         warningMsg, &I,
                                                                         TAG);
            this->currState.addVulnerabilityWarning(currWarning);
            if(this->warnedInstructions.find(&I) == this->warnedInstructions.end()) {
                this->warnedInstructions.insert(&I);
            }
        }
    }

    void TaintedPointerDereference::visitGetElementPtrInst(GetElementPtrInst &I) {
#ifdef NO_POINTER_CHECK
        return;
#endif
        // warning already raised for this instruction.
        if(this->warnedInstructions.find(&I) != this->warnedInstructions.end()) {
            return;
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << TAG << " Visiting GetElementPtr Instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        std::set<TaintFlag*> resultTaintFlags;
        for (unsigned i=0; i<I.getNumOperands(); i++) {
            Value *currOp = I.getOperand(i);
            std::set<TaintFlag*> *srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                                          this->currFuncCallSites,
                                                                          currOp);
            if (srcTaintInfo == nullptr) {
                srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                        this->currFuncCallSites,
                                                        currOp->stripPointerCasts());
            }
            if (srcTaintInfo != nullptr && !srcTaintInfo->empty()) {
                //Issue a warning for the current tainted operand.
                std::set<std::vector<InstLoc*>*> tchains;
                this->currState.getAllUserTaintChains(srcTaintInfo,tchains);
                if (tchains.empty()) {
                    //No taint from user inputs.
                    continue;
                }
                std::string warningMsg = "Trying to use tainted value as index.";
                VulnerabilityWarning *currWarning = new VulnerabilityWarning(this->currFuncCallSites,
                                                                            &tchains,
                                                                            warningMsg, &I,
                                                                            TAG);
                this->currState.addVulnerabilityWarning(currWarning);
                this->warnedInstructions.insert(&I);
            }
        }
        return;
    }

    VisitorCallback* TaintedPointerDereference::visitCallInst(CallInst &I, Function *targetFunction,
                                                              std::vector<Instruction *> *oldFuncCallSites,
                                                              std::vector<Instruction *> *currFuncCallSites) {
        if (!targetFunction->isDeclaration()) {
            // only if the function has source.
            TaintedPointerDereference *newVis = new TaintedPointerDereference(this->currState, targetFunction,
                                                                              currFuncCallSites, nullptr);
            return newVis;
        }
        return nullptr;
    }

}

