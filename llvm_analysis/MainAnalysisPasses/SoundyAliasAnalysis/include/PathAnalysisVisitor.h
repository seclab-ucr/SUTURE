//
// Created by hz on 8/13/20.
//

#ifndef PROJECT_PATHANALYSISVISITOR_H
#define PROJECT_PATHANALYSISVISITOR_H

#include "ModuleState.h"
#include "VisitorCallback.h"
#include "../../Utils/include/CFGUtils.h"
#include "../../Utils/include/Constraint.h"

using namespace llvm;

namespace DRCHECKER {

    /***
     * The main class that implements the path analysis, which makes the static analysis partially path-sensitive,
     * e.g. it can detect some infeasible paths according to the path conditions, or collect path constraints.
     */
    class PathAnalysisVisitor : public VisitorCallback {

    public:
        GlobalState &currState;
        Function *targetFunction;

        // context of the analysis, basically list of call sites
        std::vector<Instruction*> *currFuncCallSites;

        PathAnalysisVisitor(GlobalState &targetState,
                            Function *toAnalyze,
                            std::vector<Instruction*> *srcCallSites): currState(targetState) {
            this->targetFunction = toAnalyze;
            // Initialize the call site list
            this->currFuncCallSites = srcCallSites;
            // ensure that we have a context for current function.
            targetState.getOrCreateContext(this->currFuncCallSites);
        }

        ~PathAnalysisVisitor() {
        }

        //virtual void visit(Instruction &I);

        virtual void visitSwitchInst(SwitchInst &I);

        virtual void visitBranchInst(BranchInst &I);

        virtual VisitorCallback* visitCallInst(CallInst &I, Function *targetFunction,
                                               std::vector<Instruction *> *oldFuncCallSites,
                                               std::vector<Instruction *> *currFuncCallSites);

    }; //PathAnalysisVisitor class definition

} //namespace DRCHECKER

#endif //PROJECT_PATHANALYSISVISITOR_H
