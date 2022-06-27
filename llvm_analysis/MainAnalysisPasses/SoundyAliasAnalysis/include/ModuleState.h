//
// Created by machiry on 10/25/16.
//

#ifndef PROJECT_MODULESTATE_H
#define PROJECT_MODULESTATE_H
#include "AliasObject.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "TaintInfo.h"
#include "bug_detectors/warnings/VulnerabilityWarning.h"
#include "RangeAnalysis.h"
#include <set>
#include <chrono>
#include <ctime>
#include <fstream>
#include <functional>
#include "../../Utils/include/CFGUtils.h"
#include "../../Utils/include/Constraint.h"
#include <bitset>
#include <climits>

//#define DEBUG_HIERARCHY
#define PRINT_HIERARCHY_CHAIN
#define DEBUG_CONSTRUCT_TAINT_CHAIN
#define CONFINE_RECUR_STRUCT
#define CALC_HIERARCHY_HASH

using namespace llvm;

namespace DRCHECKER {
//#define DEBUG_GLOBALS
    /***
     * Class that abstracts the context.
     * Definition 3.5 of the paper.
     */
    class AnalysisContext {
    public:
        std::vector<Instruction *> *callSites;
        void printContext(llvm::raw_ostream& O) {
            O << "------------CONTEXT------------\n";
            if (!callSites) {
                O << "Null this->callSites!!\n";
            }else {
                int no = 0;
                for(Instruction *currCallSite : *(this->callSites)) {
                    O << no << " ";
                    InstructionUtils::printInst(currCallSite,O);
                    ++no;
                }
            }
            O << "-------------------------------\n";
        }

        void printContextJson(llvm::raw_ostream& O) {
            O << "\"context\":[";
            bool putComma = false;
            if (this->callSites) {
                for(Instruction *currCallSite : *(this->callSites)) {
                    if(putComma) {
                        O << ",";
                    }
                    O << "{";
                    InstructionUtils::printInstJson(currCallSite,O);
                    O << "}\n";
                    putComma = true;
                }
            }
            O << "\n]";
        }
    };

    static std::set<std::vector<TypeField*>*> htys;
    static std::set<size_t> chainHash;
    static std::set<std::string> hstrs;
    static std::set<std::set<AliasObject*>*> eqObjs;

    /***
     *  Object which represents GlobalState.
     *  Everything we need in one place.
     *  Refer Fig1 in the paper.
     *  It contains pointsTo, globalVariables and TaintInformation.
     */
    class GlobalState {
    public:

        // map containing analysis context to corresponding vulnerability warnings.
        std::map<AnalysisContext*, std::set<VulnerabilityWarning*>*> allVulnWarnings;

        // map containing vulnerability warnings w.r.t instruction.
        std::map<Instruction*, std::set<VulnerabilityWarning*>*> warningsByInstr;
        // set containing all analysis contexts that were analyzed using this global state
        std::set<AnalysisContext*> availableAnalysisContexts;

        // Range analysis results.
        RangeAnalysis::RangeAnalysis *range_analysis;

        //is the current function being analyzed read/write?
        bool is_read_write_function = false;

        // Map, which contains at each instruction.
        // set of objects to which the pointer points to.
        // Information needed for AliasAnalysis
        std::map<AnalysisContext*, std::map<Value*, std::set<PointerPointsTo*>*>*> pointToInformation;

        static std::map<Value *, std::set<PointerPointsTo*>*> globalVariables;

        static std::map<Function*, std::set<BasicBlock*>*> loopExitBlocks;

        // Data layout for the current module
        DataLayout *targetDataLayout;

        // Information needed for TaintAnalysis
        std::map<AnalysisContext*, std::map<Value*, std::set<TaintFlag*>*>*> taintInformation;

        // Store the value constraints imposed by different paths.
        std::map<AnalysisContext*, std::map<Value*, Constraint*>> constraintInformation;

        // These are the infeasible (due to conflicting path constraints) basic blocks under each calling context.
        std::map<AnalysisContext*, std::set<BasicBlock*>> deadBBs;

        // a map of basic block to number of times it is analyzed.
        std::map<const BasicBlock*, unsigned long> numTimeAnalyzed;

        //Indicates the analysis phase we're currently in, now:
        //1 = preliminary phase, 2 = main analysis phase, 3 = bug detection phase.
        int analysis_phase = 0;

        GlobalState(RangeAnalysis::RangeAnalysis *ra, DataLayout *currDataLayout) {
            this->range_analysis = ra;
            this->targetDataLayout = currDataLayout;
        }

        ~GlobalState() {
            cleanup();

        }

        void cleanup() {
            // clean up
            std::set<AliasObject*> deletedObjects;
            // all global variables.
            for(auto glob_iter = globalVariables.begin(); glob_iter != globalVariables.end(); glob_iter++) {
                auto targetPointsTo = glob_iter->second;
                for(auto currPointsTo: *targetPointsTo) {
                    auto targetAliasObj = currPointsTo->targetObject;
                    if(deletedObjects.find(targetAliasObj) == deletedObjects.end()) {
                        deletedObjects.insert(targetAliasObj);
                        delete(targetAliasObj);
                    }
                    delete(currPointsTo);
                }
                delete(targetPointsTo);
            }
            globalVariables.clear();

            // all pointsToInformation
            for(auto ptInfo = pointToInformation.begin(); ptInfo != pointToInformation.end(); ptInfo++) {
                for(auto pointsTo_iter = ptInfo->second->begin(); pointsTo_iter != ptInfo->second->begin();
                    pointsTo_iter++) {
                    auto targetPointsTo = pointsTo_iter->second;
                    for(auto currPointsTo: *targetPointsTo) {
                        auto targetAliasObj = currPointsTo->targetObject;
                        if(deletedObjects.find(targetAliasObj) == deletedObjects.end()) {
                            deletedObjects.insert(targetAliasObj);
                            delete(targetAliasObj);
                        }
                        delete(currPointsTo);
                    }
                    delete(targetPointsTo);
                }
            }
            pointToInformation.clear();
        }

        /***
         * Get the DataLayout for the current module being analyzed.
         * @return pointer to the DataLayout*
         */
        DataLayout* getDataLayout() {
            return this->targetDataLayout;
        }

        /***
         * Get the type size for the provided type.
         * @param currType Type for which size needs to fetched.
         * @return uint64_t representing size of the type.
         */
        uint64_t getTypeSize(Type *currType) {
            if(currType->isSized()) {
                return this->getDataLayout()->getTypeAllocSize(currType);
            }
            return 0;
        }


        /***
         * Get the AliasObject referenced by the currVal.
         *
         * @param currVal Value whose reference needs to be fetched.
         * @param globalObjectCache Map containing values and corresponding
         *                          AliasObject.
         * @return Corresponding AliasObject.
         */
        static AliasObject* getReferencedGlobal(std::vector<llvm::GlobalVariable *> &visitedCache, Value *currVal,
                                                std::map<Value*, AliasObject*> &globalObjectCache) {
            llvm::GlobalVariable *actualGlobal = dyn_cast<llvm::GlobalVariable>(currVal);
            if (actualGlobal == nullptr) {
                // OK, check with stripped.
                Value *strippedVal = currVal->stripPointerCasts();
                actualGlobal = dyn_cast<llvm::GlobalVariable>(strippedVal);
            }
            // Even stripping din't help. Check if this is an instruction and get the first
            // global variable in operand list
            // TODO: a better handling of the ConstantExpr. 
            if (actualGlobal == nullptr && dyn_cast<ConstantExpr>(currVal)) {
                ConstantExpr *targetExpr = dyn_cast<ConstantExpr>(currVal);
                for (unsigned int i = 0; i < targetExpr->getNumOperands(); i++) {
                    Value *currOperand = targetExpr->getOperand(i);
                    llvm::GlobalVariable *globalCheck = dyn_cast<llvm::GlobalVariable>(currOperand);
                    if (globalCheck == nullptr) {
                        // check with strip
                        globalCheck = dyn_cast<llvm::GlobalVariable>(currOperand->stripPointerCasts());
                    }
                    if (globalCheck != nullptr) {
                        actualGlobal = globalCheck;
                        break;
                    }
                    AliasObject *refObj = getReferencedGlobal(visitedCache, currOperand, globalObjectCache);
                    if(refObj != nullptr) {
                        return refObj;
                    }
                }
            }
            //Is it a function?
            if (actualGlobal == nullptr && dyn_cast<Function>(currVal)) {
                Function *targetFunction = dyn_cast<Function>(currVal);
                //NOTE: we assume that all functions that have definitions in the module have already 
                //been added to globalObjectCache (i.e. in "setupGlobals").
                if (globalObjectCache.find((Value*)targetFunction) != globalObjectCache.end()) {
                    return globalObjectCache[(Value*)targetFunction];
                }else {
                    dbgs() << "!!! getReferencedGlobal(): Cannot find the targetFunction in the cache: "
                    << targetFunction->getName().str() << "\n";
                }
            }
            if(actualGlobal != nullptr) {
                //Not a function, neither expr, it's a normal global object pointer.
                return addGlobalVariable(visitedCache, actualGlobal, globalObjectCache);
            }
            return nullptr;
        }

        /***
         *  Check if the Constant is a constant variable. ie. it uses
         *  some global variables.
         * @param targetConstant Constant to check
         * @return true/false depending on whether the constant
         *         references global variable.
         */
        static bool isConstantVariable(Constant *targetConstant) {
            Function* functionCheck = dyn_cast<Function>(targetConstant);
            if(functionCheck) {
                return true;
            }
            llvm::GlobalVariable *globalCheck = dyn_cast<llvm::GlobalVariable>(targetConstant);
            if(globalCheck) {
                return true;
            }
            ConstantExpr *targetExpr = dyn_cast<ConstantExpr>(targetConstant);
            if(targetExpr) {
                return true;
            }
            return false;
        }

        /***
         *  Get the global object from variable initializers.
         * @param constantType Type of the constant.
         * @param targetConstant Constant for which AliasObject needs to be created.
         * @param globalObjectCache Cache containing value to AliasObject.
         * @return Alias Object corresponding to the initializer.
         */
        static AliasObject* getGlobalObjectFromInitializer(std::vector<llvm::GlobalVariable *> &visitedCache,
                                                           Constant *targetConstant,
                                                           std::map<Value*, AliasObject*> &globalObjectCache) {
            if (!targetConstant || !targetConstant->getType() || !dyn_cast<ConstantAggregate>(targetConstant)) {
                return nullptr;
            }
            ConstantAggregate *constA = dyn_cast<ConstantAggregate>(targetConstant);
            Type* constantType = targetConstant->getType();
            AliasObject *glob = new GlobalObject(targetConstant, constantType);
            //hz: this can handle both the struct and sequential type.
            for (unsigned int i = 0; i < constA->getNumOperands(); ++i) {
                Constant *constCheck = constA->getOperand(i);
                if (!constCheck) {
                    continue;
                }
                AliasObject *currFieldObj = nullptr;
                if (isConstantVariable(constCheck)) {
                    // OK, the field is initialized w/ a global object pointer, now get that pointee global object.
                    currFieldObj = getReferencedGlobal(visitedCache, constCheck, globalObjectCache);
                    //Update the field point-to record.
                    if (currFieldObj != nullptr) {
                        //Since this is the global object initialization, the InstLoc is nullptr.
                        glob->addObjectToFieldPointsTo(i, currFieldObj, nullptr);
                    }
                } else if (dyn_cast<ConstantAggregate>(constCheck)) {
                    // This is an embedded struct...
                    currFieldObj = getGlobalObjectFromInitializer(visitedCache, constCheck, globalObjectCache);
                    // Update the embed object record.
                    if (currFieldObj != nullptr) {
                        glob->setEmbObj(i, currFieldObj, true);
                    }
                } else {
                    // This is possibly an integer field initialization, we can just skip.
                    continue; 
                }
            }
            return glob;
        }

        //Decide whether we need to create a GlobalObject for a certain GlobalVariable.
        static bool toCreateObjForGV(llvm::GlobalVariable *globalVariable) {
            if (!globalVariable) {
                return false;
            }
            Type *ty = globalVariable->getType();
            // global variables are always pointers
            if (!ty || !ty->isPointerTy()) {
                return false;
            }
            ty = ty->getPointerElementType();
            // Don't create GlobalObject for certain types (e.g. str pointer). 
            if (dyn_cast<SequentialType>(ty)) {
                Type *ety = dyn_cast<SequentialType>(ty)->getElementType();
                if (InstructionUtils::isPrimitiveTy(ety) || InstructionUtils::isPrimitivePtr(ety)) {
                    return false;
                }
            }
            //Filter by name.
            std::string bls[] = {".str.",".descriptor"};
            if (globalVariable->hasName()) {
                std::string n = globalVariable->getName().str();
                for (auto &s : bls) {
                    if (s == n) {
                        return false;
                    }
                }
            }
            return true;
        }

        /***
         * Add global variable into the global state and return corresponding AliasObject.
         *
         * Handles global variables in a rather complex way.
         * A smart person should implement this in a better way.
         *
         *
         * @param globalVariable Global variable that needs to be added.
         * @param globalObjectCache Cache of Values to corresponding AliasObject.
         * @return AliasObject corresponding to the global variable.
         */
        static AliasObject* addGlobalVariable(std::vector<llvm::GlobalVariable*> &visitedCache,
                                              llvm::GlobalVariable *globalVariable,
                                      std::map<Value*, AliasObject*> &globalObjectCache) {

            if (!globalVariable) {
                return nullptr;
            }
            if(std::find(visitedCache.begin(), visitedCache.end(), globalVariable) != visitedCache.end()) {
#ifdef DEBUG_GLOBALS
                dbgs() << "Cycle Detected for: " << InstructionUtils::getValueStr(globalVariable) << "\n";
#endif
                return nullptr;
            }
            Value *objectCacheKey = dyn_cast<Value>(globalVariable);
            Type *baseType = globalVariable->getType();
            // global variables are always pointers
            if (!baseType || !baseType->isPointerTy()) {
                return nullptr;
            }
            Type *objType = baseType->getPointerElementType();
            //Don't create the GlobalObject for certain GVs.
            if (!toCreateObjForGV(globalVariable)) {
                return nullptr;
            }
            // if its already processed? Return previously created object.
            if(globalObjectCache.find(objectCacheKey) != globalObjectCache.end()) {
                return globalObjectCache[objectCacheKey];
            }
            AliasObject *toRet = nullptr;
            visitedCache.push_back(globalVariable);
            // This is new global variable.
            // next check if it has any initializers.
            if (globalVariable->hasInitializer()) {
                Constant *targetConstant = globalVariable->getInitializer();
                toRet = getGlobalObjectFromInitializer(visitedCache, targetConstant, globalObjectCache);
            }
            if(toRet == nullptr) {
                // OK, the global variable has no initializer.
                // Just create a default object.
                toRet = new GlobalObject(globalVariable, objType);
            }
            //Update the global pto records.
            if (toRet != nullptr) {
                //TODO: confirm that the global variable is const equals to the pointee object is also const.
                toRet->is_const = globalVariable->isConstant();
                //hz: since this is the pre-set pto for gv, there is no calling context. 
                std::set<PointerPointsTo*> *newPointsTo = new std::set<PointerPointsTo*>();
                PointerPointsTo *pointsToObj = new PointerPointsTo(globalVariable, toRet, 0, new InstLoc(globalVariable,nullptr), false);
                newPointsTo->insert(newPointsTo->end(), pointsToObj);
                assert(GlobalState::globalVariables.find(globalVariable) == GlobalState::globalVariables.end());
                GlobalState::globalVariables[globalVariable] = newPointsTo;
                //dbgs() << "Adding:" << *globalVariable << " into cache\n";
                // make sure that object cache doesn't already contain the object.
                assert(globalObjectCache.find(objectCacheKey) == globalObjectCache.end());
                // insert into object cache.
                globalObjectCache[objectCacheKey] = toRet;
                // Make sure that we have created a pointsTo information for globals.
                assert(GlobalState::globalVariables.find(globalVariable) != GlobalState::globalVariables.end());
                assert(GlobalState::globalVariables[globalVariable] != nullptr);
            }
            visitedCache.pop_back();
            return toRet;
        }

        /***
         * Add global function into GlobalState.
         * @param currFunction Function that needs to be added.
         * @param globalObjectCache Map of values and corresponding AliasObject.
         */
        static void addGlobalFunction(Function *currFunction, std::map<Value*, AliasObject*> &globalObjectCache) {
            // add to the global cache, only if there is a definition.
            if(!currFunction->isDeclaration()) {
                std::set<PointerPointsTo*> *newPointsTo = new std::set<PointerPointsTo*>();
                GlobalObject *glob = new GlobalObject(currFunction);
                PointerPointsTo *pointsToObj = new PointerPointsTo(currFunction, glob, 0, new InstLoc(currFunction,nullptr), false);
                newPointsTo->insert(newPointsTo->end(), pointsToObj);

                GlobalState::globalVariables[currFunction] = newPointsTo;
                globalObjectCache[currFunction] = glob;
            }
        }

        /***
         * Add loop exit blocks for the provided function.
         * @param targetFunction Pointer to the function for which the loop exit block needs to be added.
         * @param allExitBBs List of the basicblocks to be added
         */
        static void addLoopExitBlocks(Function *targetFunction, SmallVector<BasicBlock *, 1000> &allExitBBs) {
            if(loopExitBlocks.find(targetFunction) == loopExitBlocks.end()) {
                loopExitBlocks[targetFunction] = new std::set<BasicBlock*>();
            }
            std::set<BasicBlock*> *toAddList;
            toAddList = loopExitBlocks[targetFunction];
            toAddList->insert(allExitBBs.begin(), allExitBBs.end());
        }

        /***
         * Get all loop exit basic blocks for the provided function.
         * @param targetFunction Target function for which the exit blocks needs to be fetched.
         * @return pointer to set of all loop exit basic blocks for the provided function.
         */
        static std::set<BasicBlock*> * getLoopExitBlocks(Function *targetFunction) {
            if(loopExitBlocks.find(targetFunction) != loopExitBlocks.end()) {
                return loopExitBlocks[targetFunction];
            }
            return nullptr;
        }


        // Get the context for the provided instruction at given call sites.
        AnalysisContext* getContext(std::vector<Instruction*> *callSites) {
            if (!callSites || callSites->empty()) {
                if (this->analysis_phase > 2) {
                    dbgs() << "!!! getContext(): Null callSites received in the bug detection phase!\n";
                }
                return nullptr;
            }
            for (auto curr_a : availableAnalysisContexts) {
                if(*(curr_a->callSites) == *callSites) {
                    return curr_a;
                }
            }
            //////////Below is just for debugging...
            //In theory all contexts have been analyzed in the main analysis phase, it's impossible that
            //in bug detection phase we have an unseen context. If this happens, we really need a thorough inspection...
            if (this->analysis_phase > 2) {
                dbgs() << "!!!!! getContext(): In bug detection phase we have an unseen calling context:\n";
                for (Instruction *inst : *callSites) {
                    InstructionUtils::printInst(inst,dbgs());
                }
                dbgs() << "We now have " << this->availableAnalysisContexts.size() << " ctx available, try to find a nearest one...\n";
                //(1) Longest common prefix, and (2) most matched insts.
                std::vector<Instruction*> *lcp = nullptr, *mmi = nullptr;
                int nlcp = 0, nmmi = 0;
                for (auto curr_a : this->availableAnalysisContexts) {
                    std::vector<Instruction*> *c = curr_a->callSites;
                    if (!c) {
                        continue;
                    }
                    bool pr = true;
                    int nl = 0, nm = 0;
                    for (int i = 0; i < callSites->size() && i < c->size(); ++i) {
                        if ((*c)[i] == (*callSites)[i]) {
                            if (pr) {
                                ++nl;
                            }
                            ++nm;
                        }else {
                            pr = false;
                        }
                    }
                    if (nl > nlcp) {
                        nlcp = nl;
                        lcp = c;
                    }
                    if (nm > nmmi) {
                        nmmi = nm;
                        mmi = c;
                    }
                }
                if (lcp) {
                    dbgs() << "==The candidate w/ longest common prefix:\n";
                    for (Instruction *inst : *lcp) {
                        InstructionUtils::printInst(inst,dbgs());
                    }
                }
                if (mmi) {
                    dbgs() << "==The candidate w/ most matched insts:\n";
                    for (Instruction *inst : *mmi) {
                        InstructionUtils::printInst(inst,dbgs());
                    }
                }
            }
            return nullptr;
        }


        /***
         *  Get or create context at the provided list of callsites,
         *  with corresponding pointsto and taint information.
         *
         * @param callSites list of call sites for the target context.
         * @param targetInfo Points-To info as std::set<PointerPointsTo*>*>*
         * @param targetTaintInfo Taint into as std::map<Value *, std::set<TaintFlag*>*> *
         * @return Target context updated with the provided information.
         *
         */
        AnalysisContext* getOrCreateContext(std::vector<Instruction*> *callSites, std::map<Value*,
                std::set<PointerPointsTo*>*> *targetInfo = nullptr, std::map<Value *, std::set<TaintFlag*>*> *targetTaintInfo = nullptr) {

            AnalysisContext* currContext = getContext(callSites);
            if(currContext == nullptr) {
                // Create a new context for the provided instruction with provided points to info.
                AnalysisContext *newContext = new AnalysisContext();
                newContext->callSites = callSites;
                // insert the new context into available contexts.
                availableAnalysisContexts.insert(availableAnalysisContexts.end(), newContext);

                // create new points to information.
                std::map<Value*, std::set<PointerPointsTo*>*> *newInfo = new std::map<Value*, std::set<PointerPointsTo*>*>();
                if (targetInfo != nullptr) {
                    newInfo->insert(targetInfo->begin(), targetInfo->end());
                } else {
                    //To copy global pto records to every calling context can lead to high
                    //memory consumption especially for large bc files with lots of global
                    //variables. Since top-level global variables are also in SSA form
                    //(e.g., their pto records will only be assigned once in the init phase)
                    //and the memory fields they point to also have their own pto records
                    //with context-sensitive propagating InstLocs, it should be safe to only
                    //keep a central copy of global pto records (i.e., "GlobalState::globalVariables").
                    /*
                    // Add all global variables in to the context.
                    newInfo->insert(GlobalState::globalVariables.begin(), GlobalState::globalVariables.end());
                    */
                }
                pointToInformation[newContext] = newInfo;

                // create taint info for the newly created context.
                std::map<Value *, std::set<TaintFlag*>*> *newTaintInfo = new std::map<Value *, std::set<TaintFlag*>*>();
                if(targetTaintInfo != nullptr) {
                    newTaintInfo->insert(targetTaintInfo->begin(), targetTaintInfo->end());
                }
                taintInformation[newContext] = newTaintInfo;

                return newContext;
            }
            return currContext;
        }

        void copyPointsToInfo(AnalysisContext *targetContext) {
            // Make a shallow copy of points to info for the current context.
            std::map<Value *, std::set<PointerPointsTo*>*> *currInfo = pointToInformation[targetContext];

            // we need to make a shallow copy of currInfo
            std::map<Value *, std::set<PointerPointsTo*>*> *newInfo = new std::map<Value *, std::set<PointerPointsTo*>*>();
            newInfo->insert(currInfo->begin(), currInfo->end());

            pointToInformation[targetContext] = newInfo;
        }

        /***
         * Get all points to information at the provided context i.e., list of call sites.
         * @param callSites target context: List of call-sites
         * @return PointsTo information as std::map<Value *, std::set<PointerPointsTo*>*>*
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* getPointsToInfo(std::vector<Instruction *> *callSites) {
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext != nullptr && pointToInformation.count(currContext));
            return pointToInformation[currContext];
        }

        std::map<Value*, Constraint*> *getCtxConstraints(std::vector<Instruction*> *callSites) {
            if (!callSites) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            return &(this->constraintInformation[currContext]);
        }

        Constraint *getConstraints(std::vector<Instruction*> *callSites, Value *v, bool create = true) {
            if (!callSites || callSites->empty() || !v) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            if (this->constraintInformation.find(currContext) != this->constraintInformation.end() &&
                this->constraintInformation[currContext].find(v) != this->constraintInformation[currContext].end()) {
                Constraint *r = this->constraintInformation[currContext][v];
                if (r) {
                    //Got the existing Constraint.
                    return r;
                }
            }
            //This means there is no existing constraint, create one if specified.
            if (create) {
                Instruction *i = (*callSites)[callSites->size()-1];
                Function *f = nullptr;
                if (i && i->getParent()) {
                    f = i->getParent()->getParent();
                }
                Constraint *r = new Constraint(v,f);
                this->constraintInformation[currContext][v] = r;
                return r;
            }
            return nullptr;
        }

        bool setConstraints(std::vector<Instruction*> *callSites, Value *v, Constraint *c) {
            if (!callSites || !v || !c) {
                return false;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            this->constraintInformation[currContext][v] = c;
            return true;
        }

        //Insert the provided dead BBs to the current records.
        void updateDeadBBs(std::vector<Instruction*> *callSites, std::set<BasicBlock*> &bbs) {
            if (!callSites || callSites->empty() || bbs.empty()) {
                return;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            (this->deadBBs)[currContext].insert(bbs.begin(),bbs.end());
            return;
        }

        std::set<BasicBlock*> *getDeadBBs(std::vector<Instruction*> *callSites) {
            if (!callSites || callSites->empty()) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            if (this->deadBBs.find(currContext) != this->deadBBs.end()) {
                return &((this->deadBBs)[currContext]);
            }
            return nullptr;
        }

        bool isDeadBB(std::vector<Instruction*> *callSites, BasicBlock *bb) {
            std::set<BasicBlock*> *dbbs = this->getDeadBBs(callSites);
            if (!dbbs || !bb) {
                return false;
            }
            return (dbbs->find(bb) != dbbs->end());
        }

        // Taint Handling functions

        /***
         * get all taint information at the provided context i.e., list of call sites
         * @param callSites target context: List of call-sites
         * @return Taint information as: std::map<Value *, std::set<TaintFlag*>*>*
         */
        std::map<Value *, std::set<TaintFlag*>*>* getTaintInfo(std::vector<Instruction *> *callSites) {
            AnalysisContext* currContext = getContext(callSites);
            if(currContext != nullptr && taintInformation.count(currContext)) {
                return taintInformation[currContext];
            }
            return nullptr;
        };

        //The standard is whether the obj/field combination exists in the history, nothing to do w/ TaintFlag.
        bool in_taint_history(TypeField *tf, std::vector<TypeField*> &history, bool insert = false) {
            //To prevent the potential path explosion caused by recursive data structures (e.g., linked list, red-black tree),
            //we exclude the case where multiple recursive structure related nodes (e.g., list_head) appear in the path.
            //TODO: better justify this decision.
            if (!tf) {
                return true;
            }
#ifdef CONFINE_RECUR_STRUCT
            std::string nty;
            if (tf->priv && ((AliasObject*)tf->priv)->targetType) {
                nty = InstructionUtils::isRecurTy(((AliasObject*)tf->priv)->targetType);
            }
#endif
            for (TypeField *htf : history) {
                if (!htf) {
                    continue;
                }
                if (htf->fid == tf->fid && 
                    (htf->priv == tf->priv || isEqvObj((AliasObject*)(htf->priv),(AliasObject*)(tf->priv)) > 0)) 
                {
                    return true;
                }
#ifdef CONFINE_RECUR_STRUCT
                if (htf->priv && !nty.empty()) {
                    std::string hty = InstructionUtils::getTypeName(((AliasObject*)htf->priv)->targetType);
                    InstructionUtils::trim_num_suffix(&hty);
                    if (hty == nty) {
                        return true;
                    }
                }
#endif
            }
            if (insert) {
                history.push_back(tf);
            }
            return false;
        }

        bool insertTaintPath(std::vector<InstLoc*> *tr, std::set<std::vector<InstLoc*>*> &res) {
            if (!tr) {
                return false;
            }
            if (res.size() > 1024) {
                //Already too many taint paths, to avoid explosion, skip.
                return false;
            }
            //If no duplication, insert.
            for (auto t : res) {
                if (DRCHECKER::sameLocTr(t,tr)) {
                    return false;
                }
            }
            res.insert(tr);
            return true;
        }

        bool insertTaintPath(std::vector<TypeField*> &chain, std::set<std::vector<InstLoc*>*> &res) {
            if (chain.empty()) {
                return false;
            }
            if (res.size() > 1024) {
                //Already too many taint paths, to avoid explosion, skip.
                return false;
            }
            std::set<std::vector<InstLoc*>*> ps,tmp;
            ps.insert(new std::vector<InstLoc*>());
            for (int i = chain.size() - 1; i > 0; --i) {
                TypeField *tf = chain[i];
                if (!tf || tf->tfs.empty()) {
                    continue;
                }
                if (tf->tfs.size() > 1) {
                    //More than one taint paths for the current link.
                    //Option 0: Select a shortest path (current choice)
                    TaintFlag *stf = nullptr;
                    for (void *pt : tf->tfs) {
                        if (!pt) {
                            continue;
                        }
                        TaintFlag *tflg = (TaintFlag*)pt;
                        if (!stf || tflg->instructionTrace.size() < stf->instructionTrace.size()) {
                            stf = tflg;
                        }
                    }
                    if (stf) {
                        //Insert taint tags to the trace as "breakpoints", for debugging purpose..
                        stf->addTag2Trace();
                        for (std::vector<InstLoc*> *p : ps) {
                            //TODO: any cross-entry-func taint path validity test?
                            p->insert(p->end(),stf->instructionTrace.begin(),stf->instructionTrace.end());
                        }
                    }
                    //Option 1: Insert all
                    /*
                    tmp.clear();
                    for (std::vector<InstLoc*> *p : ps) {
                        for (void *pt : tf->tfs) {
                            TaintFlag *tflg = (TaintFlag*)pt;
                            std::vector<InstLoc*> *np = new std::vector<InstLoc*>(*p);
                            //TODO: any cross-entry-func taint path validity test?
                            np->insert(np->end(),tflg->instructionTrace.begin(),tflg->instructionTrace.end());
                            tmp.insert(np);
                        }
                    }
                    ps.clear();
                    ps = tmp;
                    */
                }else {
                    TaintFlag *tflg = (TaintFlag*)(*(tf->tfs.begin()));
                    //Insert taint tags to the trace as "breakpoints", for debugging purpose..
                    tflg->addTag2Trace();
                    for (std::vector<InstLoc*> *p : ps) {
                        //TODO: any cross-entry-func taint path validity test?
                        p->insert(p->end(),tflg->instructionTrace.begin(),tflg->instructionTrace.end());
                    }
                }
            }
            //Now insert the paths to the res set.
            for (std::vector<InstLoc*> *p : ps) {
                if (!insertTaintPath(p,res)) {
                    delete(p);
                }
            }
            return true;
        }

        void printTaintChain(raw_ostream &O, std::vector<TypeField*> &chain) {
            O << "[CHAIN]";
            for (TypeField *tf : chain) {
                if (!tf) {
                    continue;
                }
                AliasObject *obj = (AliasObject*)(tf->priv);
                O << " <~ " << (const void*)obj << " " << InstructionUtils::getTypeName(obj->targetType) << "|" << tf->fid;
            }
            O << " ";
        }

        //Decide whether we need to give up searching the taint paths due to the path explosion.
        //Arg: "np": #path already searched; "ntp": #taintPath already found
        //TODO: consider possible FNs due to the heuristics used in this function.
        bool valid_taint_history(std::vector<TypeField*> &history, int np, int ntp) {
            if (np > 10240) {
                //There are really too many searched paths, so restrict the search to a low level.
                if (history.size() > 4) {
                    return false;
                }
            }
            if (history.size() < 8) {
                return true;
            }
            if (ntp > 0) {
                //At least one user taint path has already been identified, so we can give up here.
                return false;
            }
            if (np > 1024) {
                //Though we haven't found any taint paths, there are already too many paths searched,
                //to avoid explosion, we'd better stop the search.
                return false;
            }
            return true;
        }

        //Given current taint exploration history and the #path already searched for the top (newest) element in the history,
        //decide whether we should give up the further exploration.
        bool stopTaintExplore(std::vector<TypeField*> &history, int np) {
            static int limits[] = {10240, 5120, 2560, 1280, 640};
            static int limit_len = sizeof(limits)/sizeof(limits[0]);
            static int g_limit = 128;
            if (history.empty()) {
                return false;
            }
            TypeField *tf = history[history.size() - 1];
            AliasObject *obj = (AliasObject*)(tf->priv);
            if (obj && InstructionUtils::isRecurTy(obj->targetType) != "") {
                if (history.size() <= limit_len) {
                    return (np >= limits[history.size()-1]);
                }else {
                    return (np >= g_limit);
                }
            }else {
                //For now play it conservatively..
                //TODO: consider whether to apply any restrictions here.
                return false;
            }
            return false;
        }

        //Return all taint paths from the user input to the specified field of an object.
        //NOTE: we assume that "res" is empty and there is no TF in "tf" when invoking this function at layer 0.
        int getAllUserTaintPaths(TypeField *tf, std::vector<TypeField*> &history, std::set<std::vector<InstLoc*>*> &res) {
            //obj -> fid -> user taint path to this specific field in the obj.
            static std::map<AliasObject*, std::map<long, std::set<std::vector<InstLoc*>*>>> pathMap;
            //This is the total #paths we have explored so far for the very bottom obj|field (1st entry in "history").
            static int cnt_sp = 0;
            //This represents the #paths we explore in current invocation of "getAllUserTaintPaths".
            int r = 0;
            if (history.empty()) {
                //Root node (i.e. layer 0), reset the counter for #path searched.
                cnt_sp = 0;
            }
            if (!tf || !tf->priv) {
                return 0;
            }
            AliasObject *obj = (AliasObject*)(tf->priv);
            long fid = tf->fid;
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            //dbgs() << "getAllUserTaintPaths(): #history " << history.size() << ": Get taint paths for " 
            //<< (const void*)obj << "|" << fid << "\n"; 
            dbgs() << " <~ " << (const void*)obj << " " << InstructionUtils::getTypeName(obj->targetType) << "|" << fid << " ";
#endif
            //Do we have a taint loop? If not, add the current tf to the history.
            if (this->in_taint_history(tf,history,true)) {
                //A taint loop, stop here.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                //dbgs() << "getAllUserTaintPaths(): loop detected, return!\n";
                dbgs() << " <~ (loop)\n";
#endif
                ++cnt_sp;
                return 1;
            }
            //Should we stop searching to avoid taint path explosion?
            if (!this->valid_taint_history(history,cnt_sp,res.size())) {
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                //dbgs() << "getAllUserTaintPaths(): too many taint paths, stop here...\n";
                dbgs() << " <~ (invalid)\n";
#endif
                history.pop_back();
                ++cnt_sp;
                return 1;
            }
            //Ok, see whether there are cached user taint paths to current tf.
            if (pathMap.find(obj) != pathMap.end() && pathMap[obj].find(fid) != pathMap[obj].end()) {
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << " <~ (cached)\n";
#endif
                //Anyway we will return directly here and stop searching along this path, so increase the counter.
                //If the results are cached, we treat it as *1* path explored.
                ++cnt_sp;
                if (!pathMap[obj][fid].empty()) {
                    //Ok, path connection.
                    std::set<std::vector<InstLoc*>*> hps;
                    insertTaintPath(history,hps);
                    for (std::vector<InstLoc*> *tr : pathMap[obj][fid]) {
                        if (!tr) {
                            continue;
                        }
                        for (std::vector<InstLoc*> *hp : hps) {
                            if (!hp) {
                                continue;
                            }
                            std::vector<InstLoc*> *np = new std::vector<InstLoc*>(*tr);
                            np->insert(np->end(),hp->begin(),hp->end());
                            if (!insertTaintPath(np,res)) {
                                delete(np);
                            }
                        }
                    }
                }
                history.pop_back();
                return 1;
            }
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << " [ enum eqv obj---\n";
#endif
            //Find out who can taint this obj/field...
            //First get all eqv objects to the current one.
            std::set<AliasObject*> eqObjs;
            getAllEquivelantObjs(obj,eqObjs);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "---enum eqv obj #" << eqObjs.size();
            for (AliasObject *o : eqObjs) {
                dbgs() << " " << (const void*)o;
            }
            dbgs() << "]\n";
#endif
            //We need to consider all possible taints to every eqv object...
            //tag_obj --> tag_field --> TFs from that tag to current TypeField.
            std::map<AliasObject*,std::map<long,std::set<TaintFlag*>>> wtfs;
            bool self_inserted = false;
            for (AliasObject *o : eqObjs) {
                if (!o) {
                    continue;
                }
                //Ok, who can taint this obj|field?
                //TODO: if the original arg tf->priv is different than the current eqv obj "o", the bug analyst may be
                //confused about how "tf->priv" can be controlled by the user... Consider what we can do to help.
                //NOTE: now we only consider the taint paths valid in the single-thread execution setting (e.g. one TF may be masked by another
                //during the execution, in which case we only consider the TF that can last to the function return).
                //TODO: try to detect the concurrency bugs (e.g. just before a TF is masked in one entry, we can invoke another entry function 
                //in which the obj|field still bear the effect of that TF...)
                std::set<TaintFlag*> tflgs;
                o->getWinnerTfs(fid,tflgs);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintPaths(): eqv obj " << (const void*)o << " has #winnerTFs: " << tflgs.size() << "\n";
#endif
                for (TaintFlag *flg : tflgs) {
                    if (!flg || !flg->isTainted() || !flg->tag) {
                        continue;
                    }
                    TaintTag *tag = flg->tag;
                    if (flg->is_inherent) {
                        //This means current obj "o" is a taint source itself, and it's possible that it has not been tainted 
                        //by others (i.e. intact),
                        //so if it's a user taint source, we have already found a taint path, otherwise, there is no need to process
                        //this taint flag since its tag simply represents itself. 
                        if (!tag->is_global && !self_inserted) {
                            //TODO: in this case if the taint source obj is not "o" itself but an eqv object, we should include more info
                            //in the taint trace to show how that eqv obj is initiated and how "o" can be identical as the eqv, otherwise
                            //the taint trace will be confusing and hard to inspect.
                            //Construct the user taint path.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                            dbgs() << " <~ (user taint path ty-0, eqv: " << (obj == o) << ")\n";
                            //Re-print the history chain for the next path..
                            printTaintChain(dbgs(),history);
#endif
                            insertTaintPath(history,res);
                            self_inserted = true;
                            ++cnt_sp;
                            ++r;
                        }
                        continue;
                    }
                    AliasObject *no = (AliasObject*)(tag->priv);
                    //If the TF is originated from a user taint source, we've found a path.
                    if (!tag->is_global) {
                        Type *noty = (no ? no->targetType : nullptr);
                        std::set<void*> fs;
                        fs.insert((void*)flg);
                        TypeField ntf(noty,tag->fieldId,no,&fs);
                        history.push_back(&ntf);
                        insertTaintPath(history,res);
                        history.pop_back();
                        ++cnt_sp;
                        ++r;
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                        dbgs() << " <~ " << (const void*)no << " " << InstructionUtils::getTypeName(noty) << "|" << tag->fieldId
                        << " <~ (user taint path ty-1)\n";
                        //Re-print the history chain for the next path..
                        printTaintChain(dbgs(),history);
#endif
                        continue;
                    }
                    //Ok, we now need to recursively explore the taint source of current TF, to avoid duplication,
                    //we group all such TFs by their taint source (e.g. obj|field in the tag).
                    if (no) {
                        wtfs[no][tag->fieldId].insert(flg);
                    }
                }
            }
            //Ok, now take care of the TFs that needs recursive processing.
            bool recur = false;
            for (auto &e0 : wtfs) {
                AliasObject *no = e0.first;
                for (auto &e1 : e0.second) {
                    std::set<void*> tflgs;
                    for (auto t : e1.second) {
                        tflgs.insert(t);
                    }
                    TypeField ntf(no->targetType,e1.first,no,&tflgs);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                    printTaintChain(dbgs(),history);
#endif
                    r += getAllUserTaintPaths(&ntf,history,res);
                    recur = true;
                    //Put an optional aggressive cutting mechanism to help control taint path explosion.
                    if (r > 100 && stopTaintExplore(history,r)) {
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                        printTaintChain(dbgs(),history);
                        dbgs() << " <~ (give up)\n";
#endif
                        goto out;
                    }
                }
            }
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            if (!recur) {
                dbgs() << " <~ (deadend)\n";
            }
#endif
out:
            history.pop_back();
            if (history.empty()) {
                //In the end, don't forget to update the cache...
                //NOTE that we should make a copy of each trace in the cache since the trace in "res" might be modified later. 
                for (std::vector<InstLoc*> *tr : res) {
                    if (tr) {
                        std::vector<InstLoc*> *ntr = new std::vector<InstLoc*>(*tr);
                        pathMap[obj][fid].insert(ntr);
                    }
                }
            }
            return r;
        }

        int getAllObjsForPath(std::vector<TypeField*> *p, std::set<AliasObject*> &res) {
            if (!p || !p->size()) {
                return 0;
            }
            std::set<AliasObject*> stageObjs, nextObjs;
            stageObjs.insert((AliasObject*)((*p)[0]->priv));
            int i = 0;
            for (;i < p->size() - 1; ++i) {
                TypeField *tf = (*p)[i];
                TypeField *ntf = (*p)[i+1];
                if (!tf || !ntf || !tf->priv || !ntf->priv) {
                   break;
                }
                if (stageObjs.empty()) {
                    break;
                }
                nextObjs.clear();
                //First decide the relationship between current typefield and the next one (e.g. point-to or embed)
                if (((AliasObject*)(ntf->priv))->parent == tf->priv) {
                    //Embed, we need to get all embedded objects at the same field of the objs in "stageObjs".
                    for (AliasObject *so : stageObjs) {
                        if (so && so->embObjs.find(tf->fid) != so->embObjs.end()) {
                            AliasObject *no = so->embObjs[tf->fid];
                            if (InstructionUtils::same_types(no->targetType,ntf->ty)) {
                                nextObjs.insert(no);
                            }
                        }
                    }
                }else {
                    //Point-to, need to find all pointee objects of the same field of the objs in "stageObjs".
                    for (AliasObject *so : stageObjs) {
                        if (!so || so->pointsTo.find(tf->fid) == so->pointsTo.end()) {
                            continue;
                        }
                        for (ObjectPointsTo *pto : so->pointsTo[tf->fid]) {
                            if (!pto || !pto->targetObject) {
                                continue;
                            }
                            if (pto->dstfieldId != 0 && pto->dstfieldId != ntf->fid) {
                                continue;
                            }
                            //Type check, note the special case where "pto->targetObject" is the field 0 emb obj in "ntf".
                            AliasObject *no = pto->targetObject;
                            while (no) {
                                if (InstructionUtils::same_types(no->targetType,ntf->ty)) {
                                    nextObjs.insert(no);
                                    break;
                                }
                                if (!no->parent || no->parent_field != 0) {
                                    break;
                                }
                                no = no->parent;
                            }
                        }
                    }
                }
                stageObjs.clear();
                stageObjs.insert(nextObjs.begin(),nextObjs.end());
            }
            //The leaf obj is always in the result set.
            TypeField *lastTf = (*p)[p->size()-1];
            if (lastTf && lastTf->priv) {
                res.insert((AliasObject*)(lastTf->priv));
            }
            //Add the inferred equivelant objects by path.
            if (i >= p->size() - 1) {
                res.insert(stageObjs.begin(),stageObjs.end());
            }
            return 0;
        }

        //Ret: 1 : eqv, 0 : not eqv, -1 : unknown
        int isEqvObj(AliasObject *o0, AliasObject *o1) {
            if (!o0 != !o1) {
                return 0;
            }
            if (!o0) {
                return 1;
            }
            for (std::set<AliasObject*> *cls : DRCHECKER::eqObjs) {
                if (!cls) {
                    continue;
                }
                if (cls->find(o0) != cls->end()) {
                    //Found the equivelant class in the cache...
                    return (cls->find(o1) != cls->end() ? 1 : 0);
                }
                if (cls->find(o1) != cls->end()) {
                    //Found the equivelant class in the cache...
                    return (cls->find(o0) != cls->end() ? 1 : 0);
                }
            }
            return -1;
        }

        //Due to our current multi-entry analysis logic, each entry function will be analyzed independently (e.g. it will not
        //re-use the AliasObject created by other entry functions, instead it will created its own copy), so here we need to
        //identify all potentially identical objects to the provided one, which ensures that our taint chain construction is
        //sound.
        int getAllEquivelantObjs(AliasObject *obj, std::set<AliasObject*> &res) {
            if (!obj) {
                return 0;
            }
            //Always includes itself.
            res.insert(obj);
            //Look up the cache.
            std::set<AliasObject*> *eqcls = nullptr;
            for (std::set<AliasObject*> *cls : DRCHECKER::eqObjs) {
                if (cls && cls->find(obj) != cls->end()) {
                    //Found the equivelant class in the cache...
                    eqcls = cls;
                    break;
                }
            }
            if (eqcls == nullptr) {
                //No equivelant class found in the cache, need to do the dirty work now...
                //By default the obj itself is in its own equivelant class.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllEquivelantObjs(): identify eq objs for: " << (const void*)obj << "\n";
#endif
                eqcls = new std::set<AliasObject*>();
                eqcls->insert(obj);
                DRCHECKER::eqObjs.insert(eqcls);
                //First we need to collect all access paths to current object.
                //TODO: what if there is a pointsFrom obj who points to a non-zero field in "obj"?
                std::set<std::vector<TypeField*>*> *hty = getObjHierarchyTy(obj,0);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllEquivelantObjs(): #accessPaths: " << (hty ? hty->size() : 0) << "\n";
#endif
                //Then based on each access path, we identify all the equivelant objects (i.e. those w/ the same access path).
                if (hty && hty->size()) {
                    for (std::vector<TypeField*> *ap : *hty) {
                        if (!ap || !ap->size()) {
                            continue;
                        }
                        getAllObjsForPath(ap,*eqcls);
                    }
                }
            }
            for (AliasObject *co : *eqcls) {
                //Objects bearing the same path may still have different types (e.g. those ->private pointers),
                //so it's necessary to make another type-based filtering here.
                if (!InstructionUtils::same_types(obj->targetType,co->targetType)) {
                    continue;
                }
                //If the target obj is a dummy one, then it can match any other object (dummy or not), 
                //otherwise, it can only match other dummy objects (i.e. two real objects cannot match).
                if (obj->auto_generated || co->auto_generated) {
                    res.insert(co);
                }
            }
            return 0;
        }

        //Among all paths originating from the same source, only reserve the shortest one.
        int filterTaintPaths(std::set<std::vector<InstLoc*>*> &paths) {
            if (paths.size() <= 1) {
                return 0;
            }
            //The mapping from taint initiator inst to the shortest taint path.
            std::map<Value*,std::vector<InstLoc*>*> sps;
            for (std::vector<InstLoc*> *p : paths) {
                if (!p || p->empty()) {
                    continue;
                }
                if (sps.find((*p)[0]->inst) == sps.end() || p->size() < sps[(*p)[0]->inst]->size()) {
                    sps[(*p)[0]->inst] = p;
                }
            }
            paths.clear();
            for (auto &e : sps) {
                paths.insert(e.second);
            }
            return 0;
        }

        //Given a taint flag (w/ a specific taint src A), we try to figure out whether there exists a taint path from an user input
        //U to A and then to the target instruction in the provided taint flag. Basically we try to return all direct or indirect
        //(e.g. go through multiple entry function invocations) taint paths from the user input to the target instruction affected
        //by the given taint flag.
        int getAllUserTaintChains(TaintFlag *tf, std::set<std::vector<InstLoc*>*> &res) {
            //cache the existing user taint chains to the tag of "tf" (if it's a global one).
            static std::map<TaintTag*,std::set<std::vector<InstLoc*>*>> cache;
            if (!tf || !tf->isTainted() || !tf->tag) {
                return 1;
            }
            TaintTag *tag = tf->tag;
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintChains(): enum user taint chains for TF: " << (const void*)tf << " TAG: ";
            tag->dumpInfo_light(dbgs(),true);
#endif
            //Append the tag info to the 1st inst in the taint trace for debugging purpose..
            tf->addTag2Trace();
            if (!tag->is_global) {
                //Ok this is already a user inited taint flag, return the trace in current TF immediately.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintChains(): this is already a user taint tag, return the TF trace directly!\n";
#endif
                std::vector<InstLoc*> *newPath = new std::vector<InstLoc*>();
                newPath->insert(newPath->end(),tf->instructionTrace.begin(),tf->instructionTrace.end());
                res.insert(newPath);
                return 0;
            }
            //Ok, so now what represented by "tag" is a global memory location, we need to inspect whether and how it can
            //be eventually tainted by the user input, and return the taint paths if any.
            if (cache.find(tag) == cache.end() && tag->priv) {
                //Cache miss, do the dirty work.
                AliasObject *obj = (AliasObject*)tag->priv;
                std::vector<TypeField*> history;
                TypeField t(obj->targetType,tag->fieldId,(void*)obj);
                std::set<std::vector<InstLoc*>*> paths;
                getAllUserTaintPaths(&t,history,paths);
                //Try to filter out some paths since there may be too many.
                this->filterTaintPaths(paths);
                //Update the cache..
                cache[tag].insert(paths.begin(),paths.end());
            }
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintChains(): Got " << cache[tag].size() << " user taint paths to the global tag.\n";
#endif
            //Append the taint trace in "tf" to form the complete chain.
            for (std::vector<InstLoc*> *ep : cache[tag]) {
                //TODO: how to do the compatibility test?
                if (!ep) {
                    continue;
                }
                std::vector<InstLoc*> *newPath = new std::vector<InstLoc*>(*ep);
                newPath->insert(newPath->end(),tf->instructionTrace.begin(),tf->instructionTrace.end());
                res.insert(newPath);
            }
            return 0;
        }

        //We assume "tfs" includes multiple taint flags that share the same target tainted value, this functon tries 
        //to construct all taint paths from the user inout to the target value ending with the taint flags in "tfs".
        int getAllUserTaintChains(std::set<TaintFlag*> *tfs, std::set<std::vector<InstLoc*>*> &res) {
            if (!tfs || tfs->empty()) {
                return 0;
            }
            for (TaintFlag *tf : *tfs) {
                if (!tf || !tf->isTainted()) {
                    continue;
                }
                this->getAllUserTaintChains(tf,res);
            }
            this->filterTaintPaths(res);
            return 0;
        }

        //Return "-1" if no duplication, otherwise the index of the duplicated node.
        static int in_hierarchy_history(AliasObject *obj, long field, std::vector<std::pair<long, AliasObject*>>& history, bool to_add) {
            /*
            auto to_check = std::make_pair(field, obj);
            */
            //To prevent the potential chain explosion caused by recursive data structures (e.g., linked list, red-black tree) and
            //other issues, our duplication detection is based on the following logics:
            //(1) As long as two nodes in the chain have the same obj id, call it a duplication (i.e., ignore the field id).
            //(2) Exclude the case where multiple recursive structure related nodes (e.g., list_head) appear in the chain.
#ifdef CONFINE_RECUR_STRUCT
            std::string nty;
            if (obj && obj->targetType) {
                nty = InstructionUtils::isRecurTy(obj->targetType);
            }
#endif
            for (int i = history.size() - 1; i >= 0; --i) {
                AliasObject *hobj = history[i].second;
                if (hobj == obj) {
                    return i;
                }
#ifdef CONFINE_RECUR_STRUCT
                if (!nty.empty() && hobj) {
                    std::string hty = InstructionUtils::getTypeName(hobj->targetType);
                    InstructionUtils::trim_num_suffix(&hty);
                    if (hty == nty) {
                        return i;
                    }
                }
#endif
            }
            if (to_add) {
                auto to_check = std::make_pair(field, obj);
                history.push_back(to_check);
            }
            return -1;
        }

        //NOTE: in this function we use quite some heuristics.
        static bool valid_history(std::vector<std::pair<long, AliasObject*>>& history) {
            if (history.size() < 4) {
                return true;
            }
            //Ok it's a long history, if it also contains some same typed object types, let's say it's invalid.
            std::set<Type*> tys;
            for (auto &e : history) {
                AliasObject *obj = e.second;
                if (!obj) {
                    return false;
                }
                if (tys.find(obj->targetType) != tys.end()) {
                    return false;
                }
                tys.insert(obj->targetType);
            }
            return true;
        }

        typedef int (*traverseHierarchyCallback)(std::vector<std::pair<long, AliasObject*>>& chain, int recur);

        //Visit every object hierarchy chain ending w/ field "fid" of "obj", for each chain, invoke the passed-in callback
        //to enable some user-defined functionalities.
        static int traverseHierarchy(AliasObject *obj, long field, int layer, std::vector<std::pair<long, AliasObject*>>& history, 
                                     traverseHierarchyCallback cb = nullptr) {
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " traverseHierarchy(): " << (obj ? InstructionUtils::getTypeStr(obj->targetType) : "") 
            << " | " << field << " ID: " << (const void*)obj << "\n";
#endif
            if (!obj) {
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): null obj.\n";
#endif
                return 0;
            }
            //TODO: is it really ok to exclude the local objects?
            if (obj->isFunctionLocal()) {
                //We're not interested in function local variables as they are not persistent.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): function local objs.\n";
#endif
                return 0;
            }
            int dind = in_hierarchy_history(obj,field,history,true);
            if (dind >= 0) {
                //Exists in the history obj chain, should be a loop..
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): Exists in the obj chain..\n";
#endif
                if (cb) {
                    (*cb)(history,dind);
                }
                return 1;
            }
            if (!valid_history(history)) {
                //The history is too long or contains some duplicated elements (maybe due to the FP in static analysis),
                //so we decide to stop here...
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): Too long a history, unlikely to be real, stop..\n";
#endif
                if (cb) {
                    (*cb)(history,-1);
                }
                history.pop_back();
                return 1;
            }
            int r = 0;
            if (obj->parent && obj->parent->embObjs.find(obj->parent_field) != obj->parent->embObjs.end() 
                && obj->parent->embObjs[obj->parent_field] == obj) {
                //Current obj is embedded in another obj.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): find a host obj that embeds this one..\n";
#endif
                r += traverseHierarchy(obj->parent,obj->parent_field,layer+1,history,cb);
            }
            if (!obj->pointsFrom.empty()) {
                //Current obj may be pointed to by a field in another obj.
                for (auto &x : obj->pointsFrom) {
                    AliasObject *srcObj = x.first;
                    if (!srcObj) {
                        continue;
                    }
                    std::set<long> fids;
                    int dcnt = 0;
                    for (ObjectPointsTo *y : x.second) {
                        if (!y || y->targetObject != obj || (y->dstfieldId != 0 && y->dstfieldId != field)) {
                            continue;
                        }
                        if (fids.find(y->fieldId) != fids.end()) {
                            dbgs() << "PointsFrom of " << (const void*)obj << " dup: " << (const void*)(srcObj) << "|" << y->fieldId 
                            << " #" << ++dcnt << "\n";
                            continue;
                        }
                        fids.insert(y->fieldId);
#ifdef DEBUG_HIERARCHY
                        dbgs() << layer << " traverseHierarchy(): find a host object that can point to this one...\n";
#endif
                        r += traverseHierarchy(srcObj,y->fieldId,layer+1,history,cb);
                    }
                }
            }
            //Another case to consider: field 0 of this "obj" is an embedded obj0, which is pointed to by another obj1,
            //in this situation, we should also treat obj1 as a points-from obj of this "obj".
            if (obj->embObjs.find(0) != obj->embObjs.end()) {
                AliasObject *eobj = obj->embObjs[0];
                while (eobj) {
                    if (!eobj->pointsFrom.empty()) {
                        for (auto &x : eobj->pointsFrom) {
                            AliasObject *srcObj = x.first;
                            if (!srcObj) {
                                continue;
                            }
                            std::set<long> fids;
                            int dcnt = 0;
                            for (ObjectPointsTo *y : x.second) {
                                //In this emb-host case, we require that the dst field must be 0.
                                if (!y || y->targetObject != eobj || y->dstfieldId != 0) {
                                    continue;
                                }
                                if (fids.find(y->fieldId) != fids.end()) {
                                    dbgs() << "PointsFrom of " << (const void *)eobj << " dup: " << (const void *)(srcObj) << "|" << y->fieldId
                                           << " #" << ++dcnt << "\n";
                                    continue;
                                }
                                fids.insert(y->fieldId);
#ifdef DEBUG_HIERARCHY
                                dbgs() << layer << " traverseHierarchy(): find a host object that can point to this one's field 0 emb obj...\n";
#endif
                                r += traverseHierarchy(srcObj,y->fieldId,layer+1,history,cb);
                            }
                        }
                    }
                    if (eobj->embObjs.find(0) == eobj->embObjs.end()) {
                        break;
                    }
                    eobj = eobj->embObjs[0];
                }
            }
            if (!r) {
                //This means current object is the root of the hierarchy chain, we should invoke the callback for this chain.
                if (cb) {
                    (*cb)(history,-1);
                }
                r = 1;
            }
            history.pop_back();
            return r; 
        }

        static bool inHty(std::vector<TypeField*> *tys) {
            if (!tys || tys->empty()) {
                return false;
            }
            for (auto &x : DRCHECKER::htys) {
                if (!x || x->size() < tys->size()) {
                    continue;
                }
                int i = x->size(), j = tys->size();
                while(--j >= 0 && --i >= 0) {
                    TypeField *tf0 = (*x)[i];
                    TypeField *tf1 = (*tys)[j];
                    if (!tf0 != !tf1) {
                        break;
                    }
                    if (tf0 && (tf0->priv != tf1->priv || tf0->fid != tf1->fid)) {
                        break;
                    }
                }
                if (j < 0) {
                    return true;
                }
            }
            return false;
        }

        static int hierarchyTyCb(std::vector<std::pair<long, AliasObject*>>& chain, int recur = -1) {
            if (chain.empty()) {
                return 0;
            }
            //If there is self-recursion in the chain, our policy is to delete the recursive part (e.g., the chain between two same nodes)
            int i = (recur >= 0 ? recur : chain.size() - 1);
            //Construct the TypeField chain.
            std::vector<TypeField*> *tys = new std::vector<TypeField*>();
#ifdef CALC_HIERARCHY_HASH
            std::string sig;
#endif
            while (i >= 0) {
                long fid = chain[i].first;
                AliasObject *obj = chain[i].second;
                if (obj) {
                    TypeField *currTf = new TypeField(obj->targetType,fid,(void*)obj);
                    tys->push_back(currTf);
#ifdef CALC_HIERARCHY_HASH
                    sig += std::to_string((long)obj);
                    sig += "_";
                    sig += std::to_string(fid);
                    sig += "_";
#endif
                }else {
                    delete(tys);
                    return 0;
                }
                --i;
            }
            if (tys->size() > 0) {
                //Previously we use "inHty" to to the deduplication but it seems very slow.
#ifdef CALC_HIERARCHY_HASH
                std::hash<std::string> str_hash;
                size_t h = str_hash(sig);
                //Before inserting to htys, one thing to note is we may have a duplicated chain on file already if "recur >= 0", since
                //in that case we only take a part of the original chain. Check it.
                if (recur < 0 || (DRCHECKER::chainHash.find(h) == DRCHECKER::chainHash.end())) {
                    DRCHECKER::htys.insert(tys);
                    DRCHECKER::chainHash.insert(h);
                }
#else
                DRCHECKER::htys.insert(tys);
#endif
            }else {
                delete(tys);
            }
            return 0;
        }

        static void printHtys() {
            dbgs() << "---------[ST] Hierarchy Chain (" << DRCHECKER::htys.size() << ")---------\n";
            for (auto &x : DRCHECKER::htys) {
                if (!x) {
                    continue;
                }
                for (int i = 0; i < x->size(); ++i) {
                    TypeField *tf = (*x)[i];
                    if (tf) {
                        dbgs() << (const void*)(tf->priv) << " " << InstructionUtils::getTypeName(tf->ty) << "|" << tf->fid;
                    }else {
                        dbgs() << "Null TypeField";
                    }
                    if (i < x->size() - 1) {
                        TypeField *ntf = (*x)[i+1];
                        if (ntf && ntf->priv && tf && ((AliasObject*)(ntf->priv))->parent == tf->priv) {
                            dbgs() << " . ";
                        }else {
                            dbgs() << " -> ";
                        }
                    }
                }
                dbgs() << "\n";
            }
            dbgs() << "---------[ED] Hierarchy Chain (" << DRCHECKER::htys.size() << ")---------\n";
        }

        //A wrapper of getHierarchyTy() w/ a cache.
        static std::set<std::vector<TypeField*>*> *getObjHierarchyTy(AliasObject *obj, long fid) {
            static std::map<AliasObject*,std::map<long,std::set<std::vector<TypeField*>*>*>> cache;
            if (!obj) {
                return nullptr;
            }
            if (cache.find(obj) == cache.end() || cache[obj].find(fid) == cache[obj].end()) {
                auto t0 = InstructionUtils::getCurTime(nullptr);
                std::vector<std::pair<long, AliasObject*>> history;
                history.clear();
                for (auto &x : DRCHECKER::htys) {
                    delete(x);
                }
                DRCHECKER::htys.clear();
                DRCHECKER::chainHash.clear();
                traverseHierarchy(obj, fid, 0, history, hierarchyTyCb);
                cache[obj][fid] = new std::set<std::vector<TypeField*>*>();
                for (auto &x : DRCHECKER::htys) {
                    std::vector<TypeField*> *vtf = new std::vector<TypeField*>(*x);
                    cache[obj][fid]->insert(vtf);
                }
                dbgs() << "getObjHierarchyTy(): enumeration done in: ";
                InstructionUtils::getTimeDuration(t0,&dbgs());
#ifdef PRINT_HIERARCHY_CHAIN
                printHtys();
#endif
            }
            return cache[obj][fid];
        }

        void printCurTime() {
            auto t_now = std::chrono::system_clock::now();
            std::time_t now_time = std::chrono::system_clock::to_time_t(t_now);
            dbgs() << std::ctime(&now_time) << "\n";
        }

        // Range analysis helpers

        /***
         * Get range for the provided value
         * @param targetValue Value for which range needs to be fetched.
         * @return Pointer to range object, if exists, else Null.
         */
        RangeAnalysis::Range getRange(Value *targetValue) {
            return this->range_analysis->getRange(targetValue);
        }

        //Try best to filter out false alarms, according to some (conservative) heuristics..
        int isFalseWarning(VulnerabilityWarning *w) {
            if (!w) {
                return 1;
            }
            if (w->traces.empty()) {
                //This might not be a taint style vulnerbility.
                return 0;
            }
            //(1) Exclude the taint flows that go through a mod inst with a small constant modulus.
            //Since it will greatly limit the user's freedom.
            for (auto it = w->traces.begin(); it != w->traces.end();) {
                std::vector<InstLoc*> *tr = *it;
                bool kill = false;
                if (tr) {
                    for (InstLoc *il : *tr) {
                        if (!il || !il->inst || !dyn_cast<BinaryOperator>(il->inst)) {
                            continue;
                        }
                        BinaryOperator *bi = dyn_cast<BinaryOperator>(il->inst);
                        Instruction::BinaryOps bop = bi->getOpcode();
                        if (bop != Instruction::BinaryOps::URem && bop != Instruction::BinaryOps::SRem) {
                            continue;
                        }
                        //Get the modulus...
                        Value *cop = bi->getOperand(1);
                        if (cop) {
                            if (dyn_cast<ConstantInt>(cop)) {
                                int r = dyn_cast<ConstantInt>(cop)->getSExtValue();
                                if (r > 64 || r < -64) {
                                    continue;
                                }
                            }
                            kill = true;
                            break;
                        }
                    }
                }
                if (kill) {
                    it = w->traces.erase(it);
                }else {
                    ++it;
                }
            }
            if (w->traces.empty()) {
                return 2;
            }
            //(2) Exclude the taint flows involving an "and" IR that clear a large fraction of bits.
            for (auto it = w->traces.begin(); it != w->traces.end();) {
                std::vector<InstLoc*> *tr = *it;
                bool kill = false;
                if (tr) {
                    for (InstLoc *il : *tr) {
                        if (!il || !il->inst || !dyn_cast<BinaryOperator>(il->inst)) {
                            continue;
                        }
                        BinaryOperator *bi = dyn_cast<BinaryOperator>(il->inst);
                        Instruction::BinaryOps bop = bi->getOpcode();
                        if (bop != Instruction::BinaryOps::And) {
                            continue;
                        }
                        //Get the mask.
                        //TODO: is it possible that the constant mask is the 1st operand instead of 2nd? 
                        Value *cop = bi->getOperand(1);
                        if (cop && dyn_cast<ConstantInt>(cop)) {
                            uint64_t r = dyn_cast<ConstantInt>(cop)->getZExtValue();
                            //We need to see how many bits are reserved by the mask...
                            std::bitset<64> b(r);
                            if (b.count() <= 6) {
                                kill = true;
                                break;
                            }
                        }
                    }
                }
                if (kill) {
                    it = w->traces.erase(it);
                }else {
                    ++it;
                }
            }
            if (w->traces.empty()) {
                return 3;
            }
            //(3) Exclude the taint flows involving shift IRs (e.g., lshr) that clear most bits.
            /*
            for (auto it = w->traces.begin(); it != w->traces.end();) {
                std::vector<InstLoc*> *tr = *it;
                bool kill = false;
                if (tr) {
                    for (InstLoc *il : *tr) {
                        if (!il || !il->inst || !dyn_cast<BinaryOperator>(il->inst)) {
                            continue;
                        }
                        BinaryOperator *bi = dyn_cast<BinaryOperator>(il->inst);
                        Instruction::BinaryOps bop = bi->getOpcode();
                        if (bop != Instruction::BinaryOps::LShr && bop != Instruction::BinaryOps::AShr) {
                            continue;
                        }
                        //Get the #bits to shift.
                        Value *vop = bi->getOperand(0);
                        Value *cop = bi->getOperand(1);
                        if (cop && dyn_cast<ConstantInt>(cop)) {
                            uint64_t r = dyn_cast<ConstantInt>(cop)->getZExtValue();
                            //How many bits are there in the user-provided integer?
                            unsigned width = InstructionUtils::getBitWidth(vop,true);
                            if (width && (float)r/(float)width >= 0.62) {
                                kill = true;
                                break;
                            }
                        }
                    }
                }
                if (kill) {
                    it = w->traces.erase(it);
                }else {
                    ++it;
                }
            }
            if (w->traces.empty()) {
                return 4;
            }
            */
            //TODO: other filtering logics.
            return 0;
        }

        // Adding vulnerability warning
        /***
         * Add the provided vulnerability warning to the current state indexed by instruction.
         * @param currWarning Vulnerability warning that needs to be added.
         */
        void addVulnerabilityWarningByInstr(VulnerabilityWarning *currWarning) {
            Instruction *targetInstr = currWarning->target_instr;
            std::set<VulnerabilityWarning*> *warningList = nullptr;
            if(warningsByInstr.find(targetInstr) == warningsByInstr.end()) {
                warningsByInstr[targetInstr] = new std::set<VulnerabilityWarning*>();
            }
            warningList = warningsByInstr[targetInstr];

            for(auto a:*warningList) {
                if(a->isSameVulWarning(currWarning)) {
                    return;
                }
            }
            warningList->insert(currWarning);
        }

        /***
         * Add the provided vulnerability warning to the current state.
         * @param currWarning Vulnerability warning that needs to be added.
         */
        void addVulnerabilityWarning(VulnerabilityWarning *currWarning) {
            assert(currWarning != nullptr);
            //Filter out false alarms..
            if (isFalseWarning(currWarning)) {
                return;
            }
            AnalysisContext* currContext = getContext(currWarning->getCallSiteTrace());
            assert(currContext != nullptr);
            if(allVulnWarnings.find(currContext) == allVulnWarnings.end()) {
                // first vulnerability warning.
                allVulnWarnings[currContext] = new std::set<VulnerabilityWarning*>();
            }
            allVulnWarnings[currContext]->insert(currWarning);
            
            //Dump the warning.
            ////////////////
            dbgs() << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
            currWarning->printWarning(dbgs());
            dbgs() << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
            ////////////////

            this->addVulnerabilityWarningByInstr(currWarning);
        }

    };
}

#endif //PROJECT_MODULESTATE_H
