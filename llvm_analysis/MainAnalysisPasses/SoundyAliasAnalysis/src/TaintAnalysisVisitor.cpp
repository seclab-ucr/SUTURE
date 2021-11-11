//
// Created by machiry on 12/5/16.
//

#include "TaintAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"

using namespace llvm;
namespace DRCHECKER {

//#define DEBUG_CALL_INSTR
//#define DEBUG_RET_INSTR
//#define DEBUG_LOAD_INSTR
//#define DEBUG_CAST_INSTR
//#define DEBUG
//#define DEBUG_BIN_INSTR
#define ENFORCE_TAINT_PATH
//#define DEBUG_ENFORCE_TAINT_PATH
#define DEBUG_STORE_INSTR_MAPPING

    InstLoc *TaintAnalysisVisitor::makeInstLoc(Value *v) {
        return new InstLoc(v,this->currFuncCallSites);
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::getTaintInfo(Value *targetVal) {
        return TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, targetVal);
    }

    //"I" is the inst site where need the ptr taint info. 
    void TaintAnalysisVisitor::getPtrTaintInfo(Value *targetVal, std::set<TaintFlag*> &retTaintFlag, Instruction *I) {
        std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, targetVal);
        if(currPtsTo == nullptr) {
            return;
        }
        InstLoc *loc = this->makeInstLoc(I);
        for (PointerPointsTo *currPtTo : *currPtsTo) {
            std::set<TaintFlag*> currTaintSet;
            currPtTo->targetObject->getFieldTaintInfo(currPtTo->dstfieldId,currTaintSet,loc);
            if (currTaintSet.size()) {
                for(auto a : currTaintSet) {
                    if(std::find_if(retTaintFlag.begin(), retTaintFlag.end(), [a](const TaintFlag *n) {
                        return  n->isTaintEquals(a);
                    }) == retTaintFlag.end()) {
                        // if not insert the new taint flag into the newTaintInfo.
                        retTaintFlag.insert(a);
                    }
                }
            }
        }
    }

    void TaintAnalysisVisitor::updateTaintInfo(Value *targetVal, std::set<TaintFlag*> *targetTaintInfo) {
        TaintUtils::updateTaintInfo(this->currState, this->currFuncCallSites, targetVal, targetTaintInfo);
    }

    std::set<TaintFlag*> *TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, std::set<TaintFlag*> *srcTaintInfo, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if (srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();
            InstLoc *loc = this->makeInstLoc(targetInstruction);
            bool add_taint = false;
            for (auto currTaint : *srcTaintInfo) {
                if (!currTaint) {
                    continue;
                }
                add_taint = true;
                //hz: we're doing the taint analysis for global states, which can survive function invocations,
                //stmt0 in the 1st function call may affect stmt1 in the 2nd invocation of the same function,
                //although stmt0 cannot reach stmt1 in the CFG of this function, so it seems we should disable the below reachability check.
                //However, we can rely on the post-processing to do the multi-entry fixed-point analysis, and here we still
                //enforce the reachability test to avoid the taint explosion and have a better and cleaner summary of a single entry function.
#ifdef ENFORCE_TAINT_PATH
                if (currTaint->targetInstr != nullptr && !currTaint->is_inherent) {
                    if (targetInstruction) {
                        add_taint = loc->reachable(currTaint->targetInstr);
                    }
                }
#endif
                if (add_taint) {
                    TaintFlag *newTaintFlag = new TaintFlag(currTaint, loc);
                    TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,newTaintFlag);
                }else {
#ifdef DEBUG_ENFORCE_TAINT_PATH
                    dbgs() << "TaintAnalysisVisitor::makeTaintInfoCopy(): Failed to pass the taint path test, the TaintFlag:\n";
                    currTaint->dumpInfo(dbgs());
                    dbgs() << "Src Inst: ";
                    if (currTaint->targetInstr) {
                        currTaint->targetInstr->print(dbgs());
                    }else {
                        dbgs() << "\n";
                    }
                    dbgs() << "Dst Inst: ";
                    loc->print(dbgs());
#endif
                }
            }
            // if no taint info is propagated.
            if (newTaintInfo->empty()) {
                delete(newTaintInfo);
                delete(loc);
                newTaintInfo = nullptr;
            }
            // if dstTaintInfo is not null.
            if (dstTaintInfo != nullptr && newTaintInfo != nullptr) {
                // copy all the taint info into dstTaintInfo.
                if (dstTaintInfo->empty()) {
                    //No need to check for duplication of existing elements in "dstTaintInfo".
                    dstTaintInfo->insert(newTaintInfo->begin(), newTaintInfo->end());
                }else {
                    for (TaintFlag *tf : *newTaintInfo) {
                        TaintAnalysisVisitor::addNewTaintFlag(dstTaintInfo,tf);
                    }
                }
                // delete new taint info
                delete(newTaintInfo);
                // set return value of dstTaintInfo
                newTaintInfo = dstTaintInfo;
            }
            return newTaintInfo;
        }
        return nullptr;
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, TaintFlag *srcTaintFlag, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if (!srcTaintFlag) {
            return nullptr;
        }
        std::set<TaintFlag*> srcTaintInfo;
        srcTaintInfo.insert(srcTaintFlag);
        return TaintAnalysisVisitor::makeTaintInfoCopy(targetInstruction,&srcTaintInfo,dstTaintInfo);
    }

    //Get the taint flags of the specified value, strip the cast when necessary.
    std::set<TaintFlag*> *TaintAnalysisVisitor::getTFs(Value *v) {
        if (!v) {
            return nullptr;
        }
        std::set<TaintFlag*> *tfs = this->getTaintInfo(v);
        if (tfs && !tfs->empty()) {
            return tfs;
        }
        //E.g. "v" might be: (1) GEP (cast..) ... (2) cast (GEP ...) ..., in such cases we need to retrieve the taint
        //from the innermost base pointer.
        //Try stripping the simple cast if any.
        Value *v0 = v->stripPointerCasts();
        //Further strip the GEP transformation.
        //TODO: not sure whether this is the best choice to strip the GEP transformation, at least one obvious weakness
        //is it can only strip the GEP w/ all constant indicies.
        Value *v1 = v->stripInBoundsConstantOffsets();
        //First try the more closer "v0".
        if (v0 && v0 != v) {
            tfs = this->getTaintInfo(v0);
            if (tfs && !tfs->empty()) {
                return tfs;
            }
        }
        //Then "v1".
        if (v1 && v1 != v && v1 != v0) {
            tfs = this->getTaintInfo(v1);
            if (tfs && !tfs->empty()) {
                return tfs;
            }
        }
        //GG
        return tfs;
    }

    //This function will try best to get the pto info of a pointer value, if the raw pointer doesn't have pto, 
    //it will do the necessary cast strip.
    //NOTE: this is a helper function designed for the taint analysis, which also needs to obtain the pto info in some cases,
    //but different from the same named function in alias analysis, we don't need to parse the embedded GEP since its pto
    //info has already been set up by the alias analysis, neither the dummy object creation.
    std::set<PointerPointsTo*> *TaintAnalysisVisitor::getPtos(Value *srcPointer) { 
        if (!srcPointer) {
            return nullptr;
        }
        if (PointsToUtils::hasPointsToObjects(this->currState, this->currFuncCallSites, srcPointer)) {
            return PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, srcPointer); 
        }
        //Try to strip the pointer cast.
        Value *v = srcPointer->stripPointerCasts();
        if (v && v != srcPointer) {
            return PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, v); 
        }
        return nullptr;
    }

    std::set<TaintFlag*> *TaintAnalysisVisitor::mergeTaintInfo(std::set<Value*> &srcVals, Instruction *targetInstr) {

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();
        for(auto currVal : srcVals) {
            std::set<TaintFlag*> *currValTaintInfo = this->getTFs(currVal);
            if(currValTaintInfo && !currValTaintInfo->empty()) {
                this->makeTaintInfoCopy(targetInstr, currValTaintInfo, newTaintInfo);
            }
        }
        // if there is no taint info?
        if(newTaintInfo->empty()) {
            // delete the object.
            delete(newTaintInfo);
            newTaintInfo = nullptr;
        }
        return newTaintInfo;
    }

    int TaintAnalysisVisitor::addNewTaintFlag(std::set<TaintFlag*> *newTaintInfo, TaintFlag *newTaintFlag) {
        return TaintUtils::addNewTaintFlag(newTaintInfo, newTaintFlag);
    }

    void TaintAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
        // Nothing to do for TaintAnalysis
    }

    void TaintAnalysisVisitor::visitCastInst(CastInst &I) {
        // handles cast instruction.

        // if the src operand is tainted then the instruction is tainted.

        Value *srcOperand = I.getOperand(0);
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcOperand);

        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo && !newTaintInfo->empty()) {
                this->updateTaintInfo(&I, newTaintInfo);
            }else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from"
                << "  tainted source at " << InstructionUtils::getValueStr(&I) << "\n";
#endif
                if (newTaintInfo) {
                    delete(newTaintInfo);
                }
            }
        }
    }

    void TaintAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getOperand(0));
        allVals.insert(allVals.end(), I.getOperand(1));
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_BIN_INSTR
            dbgs() << "Propagating taint in binary instruction\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitPHINode(PHINode &I) {
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumIncomingValues(); i++) {
            allVals.insert(allVals.end(), I.getIncomingValue(i));
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitSelectInst(SelectInst &I) {
        /***
         *  Merge taintinfo of all the objects
         *  reaching this select instruction.
         */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getTrueValue());
        allVals.insert(allVals.end(), I.getFalseValue());

        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        // the GEP instruction always computes pointer, which is used to
        // check if one of the operand is tainted?
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0; i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            RangeAnalysis::Range currRange = this->currState.getRange(currOp);
            if(currRange.isBounded()) {
                // if the range of the index we use is bounded?
                // it may not be bad.
                continue;
            }
            allVals.insert(allVals.end(), currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitLoadInst(LoadInst &I) {
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "TaintAnalysisVisitor::visitLoadInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcPointer);
        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        //Copy the taint from tainted pointer.
        if (srcTaintInfo && !srcTaintInfo->empty()) {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "The src pointer itself is tainted.\n";
#endif
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,newTaintInfo);
        }
        //Now get the pto info of the src pointer.
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(srcPointer);
        if (srcPointsTo && !srcPointsTo->empty()) {
            // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
            std::set<std::pair<long, AliasObject *>> targetObjects;
            for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
                long target_field = currPointsToObj->dstfieldId;
                AliasObject *dstObj = currPointsToObj->targetObject;
                auto to_check = std::make_pair(target_field, dstObj);
                if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                    //Ok, now fetch the taint flags from the object field..
                    std::set<TaintFlag*> fieldTaintInfo, nTaintInfo;
                    dstObj->getFieldTaintInfo(target_field,fieldTaintInfo,this->makeInstLoc(&I),true,false,true);
                    if (fieldTaintInfo.empty()) {
#ifdef DEBUG_LOAD_INSTR
                        dbgs() << "No taint information available for: " << (const void*)dstObj << "|" << target_field << "\n";
#endif
                        continue;
                    }
                    this->makeTaintInfoCopy(&I, &fieldTaintInfo, &nTaintInfo);
                    //Now set up the load tag for the new TFs and insert them into the final "newTaintInfo".
                    for (TaintFlag *tf : nTaintInfo) {
                        if (TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,tf)) {
                            //TF inserted, set up the load tag.
                            tf->loadTag = currPointsToObj->loadTag;
                        }
                    }
                }
            }
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "Got pointee objs of srcPointer, #: " << targetObjects.size() << "\n";
#endif
        } else {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Src Pointer does not point to any object.\n";
#endif
        }
        if(newTaintInfo->size()) {
            // okay. Now add the newTaintInfo
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Updating Taint in LoadInstruction..\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        } else {
            delete(newTaintInfo);
        }
#ifdef TIMING
        dbgs() << "[TIMING] TaintAnalysisVisitor::visitLoadInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    void inferTaintMap(StoreInst &I, std::set<TaintFlag*> *srcTFs, std::set<PointerPointsTo*> *dstPtos, 
                       std::map<PointerPointsTo*,std::set<TaintFlag*>> &taintMap) {
        if (!srcTFs || !dstPtos) {
            return;
        }
#ifdef DEBUG_STORE_INSTR_MAPPING
        dbgs() << "inferTaintMap(): #srcTFs: " << srcTFs->size() << " #dstPtos: " << dstPtos->size() << "\n";
#endif
        if (srcTFs->empty() || dstPtos->size() <= 1) {
            return;
        }
        //Verify that the dst pointees share a unified loadTag.
        std::vector<TypeField*> *dtag = &((*(dstPtos->begin()))->loadTag);
        int dl = dtag->size(); 
        for (PointerPointsTo *pto : *dstPtos) {
            dl = std::min(dl,InstructionUtils::isSimilarLoadTag(dtag,&(pto->loadTag)));
            if (dl <= 0) {
#ifdef DEBUG_STORE_INSTR_MAPPING
                dbgs() << "inferTaintMap(): The load tags are not uniformed between dsts.\n";
#endif
                return;
            }
        }
        //Set up the mapping, note that here we skip the unification verification step for the src as in point-to analysis,
        //since unlike the pto records, the taint flags have multiple different sources (e.g. in a load IR they can be from both
        //the src pointer itself and the pointee mem locations..). So what we do here is more aggressive: to try best to match 
        //those TFs that can be addressed to a certain dst mem location, and only for the remaining, propagate them to all dsts.
        std::set<TaintFlag*> addedTFs;
        for (PointerPointsTo *pto : *dstPtos) {
            std::vector<TypeField*> *dt = &(pto->loadTag);
            taintMap[pto].clear();
            for (TaintFlag *tf : *srcTFs) {
                std::vector<TypeField*> *st = &(tf->loadTag);
                if (InstructionUtils::matchLoadTags(dt,st,dl,0) >= 0) {
                    taintMap[pto].insert(tf);
                    addedTFs.insert(tf);
                }else {
#ifdef DEBUG_STORE_INSTR_MAPPING
                    dbgs() << "inferTaintMap(): Unmapped TF: ";
                    tf->dumpInfo_light(dbgs(),false);
                    dbgs() << " for " << pto->targetObject << "|" << pto->dstfieldId << "\n";
#endif
                }
            }
        }
        //TODO: What to do w/ the unmapped TFs..
        /*
        if (addedTFs.size() < srcTFs->size()) {
            for (TaintFlag *tf : *srcTFs) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                }
            }
        }
        */
    }

    bool isSelfTaint(StoreInst &I, std::vector<InstLoc*> &tr) {
        //Get the mem location target of the "store".
        Value *p = I.getPointerOperand();
        if (!p || tr.empty()) {
            return false;
        }
        for (int i = tr.size() - 1; i >= 0; --i) {
            InstLoc *loc = tr[i];
            if (!loc) {
                continue;
            }
            Instruction *inst = dyn_cast<Instruction>(loc->inst);
            if (!inst || !inst->getParent()) {
                continue;
            }
            if (inst->getFunction() != I.getFunction()) {
                //Our analysis here is intra-procedure.
                break;
            }
            LoadInst *ld = dyn_cast<LoadInst>(inst);
            if (ld && ld->getPointerOperand() == p) {
                return true;
            }
        }
        return false;
    }

    void TaintAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
        dbgs() << "TaintAnalysisVisitor::visitStoreInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
        Value *srcPointer = I.getValueOperand();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcPointer);
        //Check for the self taint propagation here (e.g. load and store-back), if any, exclude them.
        //Basically, the idea is to see whether there is a "load" inst in the taint trace that loads from the same mem location
        //as current "store".
        //NOTE that our check here is intra-procedure, and we decide the identity of mem loc in load and store by simply comparing the
        //top-level pointer value.
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            for (auto it = srcTaintInfo->begin(); it != srcTaintInfo->end();) {
                TaintFlag *tf = *it;
                if (tf == nullptr || isSelfTaint(I,tf->instructionTrace)) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                    dbgs() << "TaintAnalysisVisitor::visitStoreInst(): null TF or self-store detected, skip the TF: ";
                    if (tf) {
                        tf->dumpInfo_light(dbgs());
                    }else {
                        dbgs() << "null.\n";
                    }
#endif
                    it = srcTaintInfo->erase(it);
                }else {
                    ++it;
                }
            }
        }
        //Get the mem locations to store.
        Value *dstPointer = I.getPointerOperand();
        std::set<PointerPointsTo*> *dstPointsTo = this->getPtos(dstPointer);
        //De-dup
        std::set<PointerPointsTo*> uniqueDstPto;
        if(dstPointsTo && !dstPointsTo->empty()) {
            for (PointerPointsTo *currPointsToObj : *dstPointsTo) {
                if (std::find_if(uniqueDstPto.begin(),uniqueDstPto.end(),[currPointsToObj](const PointerPointsTo *pto){
                    return currPointsToObj->pointsToSameObject(pto);
                }) == uniqueDstPto.end())
                {
                    uniqueDstPto.insert(currPointsToObj);
                }
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #targetMemLoc: " << uniqueDstPto.size() << "\n";
#endif
        if (uniqueDstPto.empty()) {
            //Nowhere to taint..
            return;
        }
        bool multi_pto = (uniqueDstPto.size() > 1); 
        //Prepare either the taint flags or the taint kill, and their mapping to the taint dst.
        std::set<TaintFlag*> newTaintInfo;
        //The mapping between the taint dst and the TFs to propagate.
        std::map<PointerPointsTo*,std::set<TaintFlag*>> taintMap;
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            //The src value is tainted, then we need to propagate the taint flags;
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,&newTaintInfo);
            //Try to set up the mapping between the taint flags and the taint dst if there are more than one dst.
            if (multi_pto) {
                inferTaintMap(I,&newTaintInfo,&uniqueDstPto,taintMap);
            }
        }else {
            //It's not tainted, then this is actually a taint kill if (1) there is only one target 
            //mem location (otherwise this is a weak taint kill that we will not honor to be conservative). 
            //and (2) the target mem location is tainted now (otherwise no need to kill). 
            //If so then we also need to propagate the taint kill flag.
            if (!multi_pto) {
                //Create a taint kill flag.
                TaintFlag *tf = new TaintFlag(this->makeInstLoc(&I),false,nullptr,false);
                newTaintInfo.insert(tf);
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #newTaintInfo: " << newTaintInfo.size() << "\n";
#endif
        if (newTaintInfo.empty()) {
            return;
        }
        //Ok now propagate the taint flags to the target mem locs, according to the mapping set up previously.
        std::set<TaintFlag*> addedTFs;
        int num_tf = 0;
        for (PointerPointsTo *pto : uniqueDstPto) {
            std::set<TaintFlag*> *toAdd = (taintMap.find(pto) == taintMap.end() ? &newTaintInfo : &(taintMap[pto]));
            num_tf += toAdd->size();
            for (TaintFlag *tf : *toAdd) {
                //Don't forget the "is_weak" flag in the TF indicating whether it's a strong or weak taint.
                //If the "tf" is already a weak taint, then even there is only one pointee, it's still weak;
                //If the "tf" is strong but there are multiple pointees, then again weak;
                tf->is_weak |= multi_pto;
                if (pto->targetObject->addFieldTaintFlag(pto->dstfieldId,tf,true)) {
                    addedTFs.insert(tf);
                }
            }
        }
        //Free the memory occupied by the unuseful TFs (e.g. duplicated in the dst mem loc).
        if (addedTFs.size() < newTaintInfo.size()) {
            for (TaintFlag *tf : newTaintInfo) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                    delete(tf);
                }
            }
        }
#ifdef TIMING
        dbgs() << "[TIMING] TaintAnalysisVisitor::visitStoreInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void TaintAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        // NO idea how to handle this
        assert(false);
    }

    void TaintAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        // No idea how to handle this
        assert(false);
    }

    void TaintAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction,
                                                std::vector<Instruction*> *newCallContext) {

        std::map<Value*, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(newCallContext);

        unsigned int arg_no = 0;
        for (User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++, arg_no++) {
            Value *currArgVal =(*arg_begin).get();
            std::set<TaintFlag*> *currArgTaintInfo = this->getTFs(currArgVal);
            if (!currArgTaintInfo || currArgTaintInfo->empty()) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "TaintAnalysisVisitor::setupCallContext(): arg " << arg_no << " does not have taint info.\n";
#endif
                continue;
            }
#ifdef DEBUG_CALL_INSTR
            dbgs() << "TaintAnalysisVisitor::setupCallContext(): arg " << arg_no << " #TF: " << currArgTaintInfo->size() << "\n";
#endif
            Argument *farg = InstructionUtils::getArg(currFunction,arg_no);
            if (!farg) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "!!! TaintAnalysisVisitor::setupCallContext(): cannot get formal arg " << (arg_no + 1) << "!\n";
#endif
                continue;
            }
            std::set<TaintFlag*> *tfs = this->makeTaintInfoCopy(&I, currArgTaintInfo);
            if (tfs && !tfs->empty()) {
#ifdef DEBUG_CALL_INSTR
                // OK, we need to add taint info.
                dbgs() << "TaintAnalysisVisitor::setupCallContext(): farg " << arg_no << " has #TF: " << tfs->size() << "\n";
#endif
                (*contextTaintInfo)[farg] = tfs;
            }
        }
    }

    void TaintAnalysisVisitor::propagateTaintToMemcpyArguments(std::vector<long> &memcpyArgs, CallInst &I) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Processing memcpy function\n";
#endif
        //TODO: does it really make sense to propagate taint from the src pointer value (not the pointee) to the dst?
        // we do not need any special taint handling..because alias takes care of propagating
        // the pointee memory content, here we just need to update taint of the arguments.
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);

        std::set<Value*> mergeVals;
        mergeVals.insert(srcOperand);

        std::set<TaintFlag*>* newTaintInfo = this->mergeTaintInfo(mergeVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Trying to memcpy from tainted argument\n";
#endif
            this->updateTaintInfo(dstOperand, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::handleKernelInternalFunction(CallInst &I, Function *currFunc) {
        //NOTE: taint initiator function like copy_from_user has been handled in AliasAnalysis, including the taint propagation.
        if (TaintAnalysisVisitor::functionChecker->is_memcpy_function(currFunc)) {
            // Handle memcpy function..
            // get memcpy argument numbers
            std::vector<long> memcpyArgs = TaintAnalysisVisitor::functionChecker->get_memcpy_arguments(currFunc);
            //propagate taint from src to dst.
            this->propagateTaintToMemcpyArguments(memcpyArgs, I);
        }else if (TaintAnalysisVisitor::functionChecker->is_atoi_function(currFunc)) {
            // This is an atoi like function?
            // if yes? get the taint of the object pointed by the first argument.
            // propagate that to the return value.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if (!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);
                this->updateTaintInfo(&I, newTaintSet);
            }
        }else if (TaintAnalysisVisitor::functionChecker->is_sscanf_function(currFunc)) {
            // This is a sscanf function?
            // if yes? get the taint of the object pointed by the first argument.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if (!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);
                std::set<TaintFlag*> addedTaints;
                // now add taint to all objects pointed by the arguments.
                unsigned int arg_idx;
                for (arg_idx = 2; arg_idx < I.getNumArgOperands(); arg_idx++) {
                    Value *argVal = I.getArgOperand(arg_idx);
                    std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, argVal);
                    if (currPtsTo != nullptr) {
                        //Set "is_weak"
                        bool multi_pto = (currPtsTo->size() > 1);
                        for(auto currT : *newTaintSet) {
                            if (currT) {
                                currT->is_weak |= multi_pto;
                            }
                        }
                        for(auto currP : *currPtsTo) {
                            for(auto currT : *newTaintSet) {
                                if(currP->targetObject->addFieldTaintFlag(currP->dstfieldId, currT)) {
                                    addedTaints.insert(currT);
                                }
                            }
                        }
                    }
                }
                //Free memory.
                for (auto currT : *newTaintSet) {
                    if (addedTaints.find(currT) == addedTaints.end()) {
                        delete(currT);
                    }
                }
                delete(newTaintSet);
            }
        }else {
            // TODO (below):
            // untaint all the arguments, depending on whether we are indeed calling kernel internal functions.
            // memset()?
        }
    }

    VisitorCallback* TaintAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "TaintAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        // if this is a kernel internal function.
        if(currFunc->isDeclaration()) {
            this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }

        // else, we need to setup taint context and create a new visitor.
        setupCallContext(I, currFunc, callSiteContext);

        // create a new TaintAnalysisVisitor
        TaintAnalysisVisitor *vis = new TaintAnalysisVisitor(currState, currFunc, callSiteContext);

        return vis;
    }

    void TaintAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        // just connect the taint of the return values.
        TaintAnalysisVisitor *vis = (TaintAnalysisVisitor *)childCallback;
        if(vis->retValTaints.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction:";
            I.print(dbgs());
            dbgs() << "\n";
#endif
            // create new taint info.
            std::set<TaintFlag*>* newTaintInfo = new std::set<TaintFlag*>();
            for(auto currRetTaint:vis->retValTaints) {
                //NOTE: ret taint must be able to reach this call site, so no need for the taint path check.
                TaintFlag *newTaintFlag = new TaintFlag(currRetTaint, this->makeInstLoc(&I));
                newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
            }

            //update taint info
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        // add taint of the return value to the retTaintInfo set.
        Value *targetRetVal = I.getReturnValue();
        if (!targetRetVal) {
            return;
        }
        std::set<TaintFlag*> *currRetTaintInfo = this->getTFs(targetRetVal);
        if (!currRetTaintInfo || currRetTaintInfo->empty()) {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Return value: " << InstructionUtils::getValueStr(&I) << ", does not have TaintFlag.\n";
#endif
            return;
        }
        for(auto a : *currRetTaintInfo) {
            if(std::find_if(this->retValTaints.begin(), this->retValTaints.end(), [a](const TaintFlag *n) {
                return  n->isTaintEquals(a);
            }) == this->retValTaints.end()) {
                // if not insert the new taint flag into the newTaintInfo.
                this->retValTaints.insert(this->retValTaints.end(), a);
            }
        }
    }

    void TaintAnalysisVisitor::visitICmpInst(ICmpInst &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            allVals.insert(currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

#ifdef CONTROL_TAINT
    //hz: add support for branch and switch instructions into taint analysis. 
    //TODO: In the future if we want to do control taint, we need to extend these below methods.

    //hz: the overall propagation logic of this is borrowed (w/o a plan to return) from visitCastInst.
    void TaintAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //No need to handle a unconditional branch since it has no condition variable.
        if (I.isUnconditional()) {
            return;
        }
        //Get the branch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(condition);
        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            }
        }
    }

    /*
    void TaintAnalysisVisitor::visitIndirectBrInst(IndirectBrInst &I) {
        //
    }
    */

    //hz: basically the same as visitBranchInst()
    void TaintAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
        //Get the switch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(condition);
        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo && !newTaintInfo->empty()) {
                this->updateTaintInfo(&I, newTaintInfo);
            }
        }
    }
#endif

}
