//
// Created by hz on 8/13/20.
//

#include "PathAnalysisVisitor.h"

using namespace llvm;

namespace DRCHECKER {

    #define DEBUG_VISIT_SWITCH_INST
    #define DEBUG_VISIT_BRANCH_INST
    #define DEBUG_CALL_INST

    void PathAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "PathAnalysisVisitor::visitSwitchInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *cond_var = I.getCondition();
        BasicBlock *def_bb = I.getDefaultDest();
        unsigned num = I.getNumCases();
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "PathAnalysisVisitor::visitSwitchInst(): Cond Var: " << InstructionUtils::getValueStr(cond_var) << " Default BB: "
        << InstructionUtils::getBBStrID(def_bb) << " #cases: " << num << "\n";
#endif
        //Collect the cases and values of this switch.
        //case bb -> the switch value(s) to it.
        std::map<BasicBlock*,std::set<int64_t>> caseMap;
        std::set<int64_t> cns;
        for (auto c : I.cases()) {
            ConstantInt *val = c.getCaseValue();
            int64_t c_val = val->getSExtValue();
            //uint64_t c_val = val->getZExtValue();
            cns.insert(c_val);
            BasicBlock *bb = c.getCaseSuccessor();
#ifdef DEBUG_VISIT_SWITCH_INST
            dbgs() << "Case Value: " << c_val << " Dst BB: " << InstructionUtils::getBBStrID(bb) << "\n";
#endif
            if (!val || !bb) {
                continue;
            }
            caseMap[bb].insert(c_val);
        }
        //Now inspect each branch of this switch, test the feasibility, and update the constraints of "cond_var" in each branch.
        //First need to see whether there are existing constaints for the "cond_var" at this point.
        Constraint *c = this->currState.getConstraints(this->currFuncCallSites, cond_var, true);
        assert(c);
        for (auto &e : caseMap) {
            BasicBlock *bb = e.first;
            //We now need to ensure that "bb" is dominated by the switch BB, otherwise we cannot enforce the constraints
            //posed by the switch inst to it.
            if (InstructionUtils::getSinglePredecessor(bb) != I.getParent()) {
                dbgs() << "!!! PathAnalysisVisitor::visitSwitchInst(): current case BB is not dominated by the switch BB!\n";
                continue;
            }
            //Get all BBs dominated by "bb", these are BBs belonging only to the current case branch.
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(bb, dombbs);
            //Update the constraints.
            expr cons = c->getEqvExpr(e.second);
            c->addConstraint2BBs(&cons,dombbs);
        }
        //Deal with the default case.
        if (def_bb && InstructionUtils::getSinglePredecessor(def_bb) == I.getParent()) {
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(def_bb, dombbs);
            expr e = c->getNeqvExpr(cns);
            c->addConstraint2BBs(&e,dombbs);
        }
        //Now let's see whether there are any infeasible BBs due to the constraint conflicts, if any, update them to
        //the global state in order to guide the BB exploration.
        this->currState.updateDeadBBs(this->currFuncCallSites, c->deadBBs);
        return;
    }

    VisitorCallback* PathAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                        std::vector<Instruction*> *oldFuncCallSites,
                                                        std::vector<Instruction*> *callSiteContext) {
#ifdef DEBUG_CALL_INST
        dbgs() << "PathAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << ", callee: " 
        << currFunc->getName().str() << "\n";
#endif
        // if this is a kernel internal function, just skip it for now.
        if(currFunc->isDeclaration()) {
            //this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }
        // Ok, we need to propagate the constraints from the actual args to the formal args, if any.
        int arg_no = -1;
        for (Value *arg : I.args()) {
            ++arg_no;
            //Get the formal argument.
            Argument *farg = InstructionUtils::getArg(currFunc,arg_no);
            if (!arg || !farg) {
                continue;
            }
            Constraint *nc = nullptr;
            if (!dyn_cast<ConstantInt>(arg)) {
                //The actual argument is a variable, see whether it has any constraints at current point.
                Constraint *cons = this->currState.getConstraints(this->currFuncCallSites, arg, false);
                if (!cons) {
                    //Try to strip the pointer cast.
                    cons = this->currState.getConstraints(this->currFuncCallSites, arg->stripPointerCasts(), false);
                }
                if (!cons) {
                    // No constraints for current actual arg.
                    continue;
                }
                expr *e = cons->getConstraint(I.getParent());
                if (!e) {
                    // No constraints in current BB.
                    continue;
                }
#ifdef DEBUG_CALL_INST
                dbgs() << "PathAnalysisVisitor::visitCallInst(): propagate constraint for arg " << arg_no
                << ": " << InstructionUtils::getValueStr(arg) << " -> " << InstructionUtils::getValueStr(farg) 
                << ", constraint: " << e->to_string() << "\n";
#endif
                nc = new Constraint(farg,currFunc);
                expr *ne = new expr(z3c);
                *ne = (*e && (get_z3v_expr_bv((void*)farg) == get_z3v_expr_bv((void*)arg)));
                nc->addConstraint2AllBBs(ne);
            }else {
                //The actual argument is a constant, so obviously we need to add a constraint to the formal arg.
                nc = new Constraint(farg,currFunc);
                int64_t c_val = dyn_cast<ConstantInt>(arg)->getSExtValue();
                std::set<int64_t> vs;
                vs.insert(c_val);
                expr e = nc->getEqvExpr(vs);
#ifdef DEBUG_CALL_INST
                dbgs() << "PathAnalysisVisitor::visitCallInst(): actual arg " << arg_no << " is a constant int: "
                << c_val << ", so add the constraint " << e.to_string() << " to the formal arg: " 
                << InstructionUtils::getValueStr(farg) << "\n";
#endif
                nc->addConstraint2AllBBs(&e);
            }
            //Add the formal arg constraint to the global state.
            this->currState.setConstraints(callSiteContext,farg,nc);
        }
        // In the end create a new PathAnalysisVisitor for the callee.
        PathAnalysisVisitor *vis = new PathAnalysisVisitor(currState, currFunc, callSiteContext);
        return vis;
    }

    //We collect and solve simple conditionals in the form of "V op C", where V is a variable and C constant, op is simple
    //binary operators (e.g., ==, <, >, <=, >=).
    void PathAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //First see whether this "br" is a simple comparison of the form we consider.
        if (!I.isConditional()) {
            return;
        }
        Value *cond = I.getCondition();
        if (!cond) {
            return;
        }
        CmpInst *ci = dyn_cast<CmpInst>(cond);
        Value *v = nullptr;
        int64_t sc = 0;
        uint64_t uc = 0;
        CmpInst::Predicate pred, rpred;
        if (ci) {
            //Ok, see whether it's the desired form (i.e., variable vs. constant).
            Value *op0 = ci->getOperand(0);
            Value *op1 = ci->getOperand(1);
            if (!op0 || !op1) {
                return;
            }
            if (dyn_cast<ConstantData>(op0) || dyn_cast<ConstantData>(op1)) {
                if (!dyn_cast<ConstantData>(op0)) {
                    if (!InstructionUtils::getConstantValue(dyn_cast<Constant>(op1),&sc,&uc)) {
                        return;
                    }
                    v = op0;
                    pred = ci->getPredicate();
                    rpred = ci->getInversePredicate();
                }else if (!dyn_cast<ConstantData>(op1)) {
                    if (!InstructionUtils::getConstantValue(dyn_cast<Constant>(op0),&sc,&uc)) {
                        return;
                    }
                    v = op1;
                    pred = ci->getInversePredicate();
                    rpred = ci->getPredicate();
                }else {
                    //Both are constants? Surprising that this is not optimized out by the compiler...
                    //TODO: need to find a way to skip the dead code since we can already evaluate the conditional.
                    return;
                }
                //Construct the Z3 constraint on the variable "v"...
            }else {
                //Both are variables, ignore.
                return;
            }
        }else {
            //This means the conditional is about a boolean variable (e.g., if(b)), for which we should pose constraints.
            //NOTE: here we convert the boolean true to "1".
            v = cond;
            pred = CmpInst::Predicate::ICMP_EQ;
            rpred = CmpInst::Predicate::ICMP_NE;
            sc = uc = 1;
        }
#ifdef DEBUG_VISIT_BRANCH_INST
        dbgs() << "PathAnalysisVisitor::visitBranchInst(): Processing BR: " << InstructionUtils::getValueStr(&I) 
        << ", pred: " << pred << ", sc: " << sc << ", uc: " << uc << "\n";
#endif
        //Ok, we're ready to construct the z3 expression now.
        //Get/Create constraints for "v" in this calling context.
        Constraint *c = this->currState.getConstraints(this->currFuncCallSites, v, true);
        assert(c);
        //Figure out the BBs belonging to each branch..
        BasicBlock *tb = I.getSuccessor(0);
        BasicBlock *fb = I.getSuccessor(1);
        //If there are other paths to the initial branch BB (i.e., bypass the conditional), we will not pose the constraints.
        if (tb && InstructionUtils::getSinglePredecessor(tb) == I.getParent()) {
            //Get all dominated BBs, these are BBs belonging only to the current branch.
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(tb, dombbs);
            //Update the constraints.
            expr cons = c->getExpr(pred,sc,uc);
            c->addConstraint2BBs(&cons,dombbs);
        }
        //Process the false branch..
        if (fb && InstructionUtils::getSinglePredecessor(fb) == I.getParent()) {
            //Get all dominated BBs, these are BBs belonging only to the current branch.
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(fb, dombbs);
            //Update the constraints.
            expr cons = c->getExpr(rpred,sc,uc);
            c->addConstraint2BBs(&cons,dombbs);
        }
        //Update the dead BBs to the global state, if any.
        this->currState.updateDeadBBs(this->currFuncCallSites, c->deadBBs);
        return;
    }

}// namespace DRCHECKER
