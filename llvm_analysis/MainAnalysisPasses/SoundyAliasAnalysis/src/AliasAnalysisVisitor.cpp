//
// Created by machiry on 12/4/16.
//
#include "AliasAnalysisVisitor.h"

namespace DRCHECKER {

#define DEBUG_GET_ELEMENT_PTR
//#define DEBUG_ALLOCA_INSTR
#define DEBUG_CAST_INSTR
//#define DEBUG_BINARY_INSTR
//#define DEBUG_PHI_INSTR
#define DEBUG_LOAD_INSTR
#define DEBUG_STORE_INSTR
#define DEBUG_CALL_INSTR
//#define STRICT_CAST
//#define DEBUG_RET_INSTR
//#define FAST_HEURISTIC
//#define MAX_ALIAS_OBJ 50
//hz: Enable creating new outside objects on the fly when the pointer points to nothing.
#define CREATE_DUMMY_OBJ_IF_NULL
#define DEBUG_CREATE_DUMMY_OBJ
#define DEBUG_UPDATE_POINTSTO
//#define AGGRESSIVE_PTO_DUP_FILTER
//#define DEBUG_TMP
#define DEBUG_HANDLE_INLINE_POINTER

    //hz: A helper method to create and (taint) a new OutsideObject.
    //"p" is the pointer for which we need to create the object, "I" is the instruction as a creation site.
    OutsideObject* AliasAnalysisVisitor::createOutsideObj(Value *p, Instruction *I, bool taint) {
        if (!p) {
            return nullptr;
        }
        if (dyn_cast<GlobalVariable>(p)) {
            //We have already set up all the global pto relationship before all analysis begin, so if now we cannot
            //find the pointee of a certain global variable, that must be we have decided that there is no need to
            //create a pointee object for it (e.g. the gv is a constant string pointer). So we will not create
            //an OutsideObject for it either.
#ifdef DEBUG_CREATE_DUMMY_OBJ
            dbgs() << "AliasAnalysisVisitor::createOutsideObj(): we will not create dummy object for the global variable: "
            << InstructionUtils::getValueStr(p) << "\n";
#endif
            return nullptr;
        }
        InstLoc *loc = nullptr;
        if (I) {
            loc = new InstLoc(I,this->currFuncCallSites);
        }else {
            loc = new InstLoc(p,this->currFuncCallSites);
        }
        std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
        if (DRCHECKER::enableXentryImpObjShare) {
            //Can we get a same-typed object from the global cache (generated when analyzing another entry function)?
            //NOTE: there are multiple places in the code that create a new OutsideObject, but we only do this multi-entry cache mechanism here,
            //because other places create the object that is related to another object (emb/host/field point-to), while we only need to cache the
            //top-level outside obj here (so that other sub obj can be naturally obtained by the field records inside it).
            if (p->getType() && p->getType()->isPointerTy() && dyn_cast<CompositeType>(p->getType()->getPointerElementType())) {
                OutsideObject *obj = DRCHECKER::getSharedObjFromCache(p);
                if (obj) {
                    //We need to bind the shared object w/ current inst.
                    obj->addPointerPointsTo(p,loc);
                    this->updatePointsToObjects(p,obj,loc);
                    return obj;
                }
            }
        }
        //Ok, now we need to create a dummy object for the pointer "p"..
        OutsideObject *robj = DRCHECKER::createOutsideObj(p,loc);
        if (robj) {
            //Add it to the global pto record.
            this->updatePointsToObjects(p,robj,loc);
            //Then we should consider whether and how to taint it...
            if (taint) {
                //First set this new obj as a taint source, since it's very likely that this is a shared obj inited in other entry functions.
                //TODO: consider whether it's possible that this obj is a user inited taint source, if so, how to recognize this?
                //TODO: it's strange to consider the taint stuff in the AliasAnalysis.
                robj->setAsTaintSrc(loc,true);
                //Then propagate the taint flags from the pointer "p" to the obj.
                std::set<TaintFlag*> *existingTaints = TaintUtils::getTaintInfo(this->currState,this->currFuncCallSites,p);
                if (existingTaints) {
                    for (TaintFlag *tf : *existingTaints) {
                        if (!tf) {
                            continue;
                        }
                        //TODO: in theory we need to test whether the new taint trace is valid (i.e. reachability), we omit it now since
                        //it's less likely that the taint on the pointer cannot reach its pointee..
                        //NOTE: "is_weak" is inherited.
                        TaintFlag *ntf = new TaintFlag(tf,loc);
                        robj->taintAllFields(ntf);
                    }
                }
            }
            if (DRCHECKER::enableXentryImpObjShare) {
                DRCHECKER::addToSharedObjCache(robj);
            }
        }else {
#ifdef DEBUG_CREATE_DUMMY_OBJ
            dbgs() << "AliasAnalysisVisitor::createOutsideObj(): failed to create the dummy obj!\n";
#endif
        }
        return robj;
    }

    std::set<PointerPointsTo*>* AliasAnalysisVisitor::getPointsToObjects(Value *srcPointer) {
        // Get points to objects set of the srcPointer at the entry of the instruction
        // currInstruction.
        // Note that this is at the entry of the instruction. i.e INFLOW.
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        // Here srcPointer should be present in points to map.
        if(targetPointsToMap->find(srcPointer) != targetPointsToMap->end()) {
            return (*targetPointsToMap)[srcPointer];
        }
        return nullptr;
    }

    bool AliasAnalysisVisitor::isPtoDuplicated(const PointerPointsTo *p0, const PointerPointsTo *p1, bool dbg = false) {
        if (!p0 && !p1) {
            return true;
        }
        if ((!p0) != (!p1)) {
            return false;
        }
        //hz: a simple hack here to avoid duplicated objects.
        if(dbg){
            dbgs() << "----------------------------\n";
        }
        if (p0->dstfieldId != p1->dstfieldId){
            if(dbg){
                dbgs() << "dstField mismatch: " << p0->dstfieldId << "|" << p1->dstfieldId << "\n";
            }
            return false;
        }
        AliasObject *o0 = p0->targetObject;
        AliasObject *o1 = p1->targetObject;
        if(dbg){
            dbgs() << (o0?"t":"f") << (o1?"t":"f") << (o0?(o0->isOutsideObject()?"t":"f"):"n") 
            << (o1?(o1->isOutsideObject()?"t":"f"):"n") << "\n";
        }
        if ((!o0) != (!o1)) {
            return false;
        }
        if (o0 == o1)
            return true;
        //In theory we should return false, except we use a more strict filtering (in order to reduce more points-to records.)
        //By default, the comparison logic is just to see whether the pointee obj and fieldId are the same.
#ifdef AGGRESSIVE_PTO_DUP_FILTER
        //o0 and o1 must be not null now.
        if(dbg){
            dbgs() << "Ty0: " << InstructionUtils::getTypeStr(o0->targetType) << " Ty1: " << InstructionUtils::getTypeStr(o1->targetType) << "\n";
        }
        if(o0->targetType != o1->targetType){
            if(dbg){
                dbgs() << "Target obj type mismatch!\n";
            }
            return false;
        }
        //Ok, now these two points-to have the same target obj type and dst field, what then?
        //We will further look at the object ptr of the target AliasObject, if they are also the same, we regard these 2 objs the same.
        Value *v0 = o0->getObjectPtr();
        Value *v1 = o1->getObjectPtr();
        if(dbg){
            dbgs() << "Ptr0: " << InstructionUtils::getValueStr(v0) << " Ptr1: " 
            << InstructionUtils::getValueStr(v1) << " RES: " << (v0==v1?"T":"F") << "\n";
        }
        return (v0 == v1);
#else
        return false;
#endif
    }

    //Basically we try to see whether the pointee object type matches that of srcPointer, if not, we try adjust the PointerPointsTo, e.g.,
    //by walking through the embed/parent hierarchy of the pointee object.
    //"loc" is the instruction site where we need to match the pto.
    //"create_host" indicates whether to automatically create a host object if that's necessary for 
    //a match (i.e. current pto points to a struct that can be embedded in a host object).
    //Return: whether the type is matched in the end.
    int AliasAnalysisVisitor::matchPtoTy(Value *srcPointer, PointerPointsTo *pto, Instruction *I, bool create_host) {
        if (!srcPointer || !pto || !pto->targetObject) {
            return 0;
        }
        Type *srcTy = srcPointer->getType();
        if (!srcTy || !srcTy->isPointerTy()) {
            return 0;
        }
        srcTy = srcTy->getPointerElementType();
        return this->matchPtoTy(srcTy,pto,I,create_host);
    }

    //srcTy is the type we should point to.
    int AliasAnalysisVisitor::matchPtoTy(Type *srcTy, PointerPointsTo *pto, Instruction *I, bool create_host) {
        if (!pto || !pto->targetObject) {
            return 0;
        }
        AliasObject *obj = pto->targetObject;
        Type *pTy = obj->targetType;
        if (!srcTy || !pTy) {
            return 0;
        }
        long dstfieldId = pto->dstfieldId;
        if (dstfieldId == 0 && InstructionUtils::same_types(srcTy,pTy)) {
            //Quick path: direct host match.
            return 2;
        }
        //Handle a special case here: <{[i8 * 30], [i8 * 34]}> should be convertiable to [i8 * 64]...
        //If this happens, we choose to directly reset the original object to the flat sequential type.
        if (dyn_cast<SequentialType>(srcTy) && dyn_cast<StructType>(pTy)) {
            Type *bty = nullptr, *bty0 = dyn_cast<SequentialType>(srcTy)->getElementType();
            int sz = -1, sz0 = dyn_cast<SequentialType>(srcTy)->getNumElements();
            InstructionUtils::seq_compatiable(dyn_cast<StructType>(pTy),&bty,&sz);
            if (bty && InstructionUtils::same_types(bty0,bty,false) && (sz0 == 0 || sz0 == sz)) {
                //Perform a type reset.
                //TODO: how to make a new sequential type with a different size from the existing "srcTy"?
                //TODO: how to transfer existing pto records and taint flags to the new flat array?
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): Reset a struct to a sequential!\n";
#endif
                InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
                obj->reset(obj->getValue(),srcTy,loc);
                return 2;
            }
        }
        if (InstructionUtils::same_types(obj->getFieldTy(dstfieldId),srcTy)) {
            //Quick path: field match.
            return 1;
        }
        //DataLayout *dl = this->currState.targetDataLayout;
        //Ok, first let's see whether srcTy can match the type of any embedded fields in the pto.
        std::set<Type*> etys;
        obj->getNestedFieldTy(dstfieldId, etys);
        for (Type *ety : etys) {
            if (InstructionUtils::same_types(ety,srcTy)) {
                //Ok, we just need to get/create the proper embedded object and return its pto.
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to an embedded field to match the srcPointer!\n";
#endif
                InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
                AliasObject *eobj = obj->getNestedObj(dstfieldId,ety,loc);
                if (eobj && eobj != obj && InstructionUtils::same_types(eobj->getFieldTy(0),srcTy)) {
                    pto->targetObject = eobj;
                    pto->dstfieldId = 0;
                    //Matched: emb obj.
                    return 3;
                }
                //Here, (1) "srcTy" cannot directly match the given field type in "pto", 
                //(2) we're sure that it can match one emb obj of the given field,
                //but the thing is we failed to get/create that specific emb obj at the given field w/ "getNestedObj", i
                //though strange, we can do nothing now..
                dbgs() << "!!! AliasAnalysisVisitor::matchPtoTy(): Failed to get/create the emb obj that should be there!\n";
                return 0;
            }
        }
        if (InstructionUtils::isPrimitiveTy(srcTy,8)) {
            //i8 wildcard of the src type.
            return 6;
        }
        //Ok, we cannot match the "srcTy" in any layer of embedded objects at the given field, now consider whether
        //we can match any parent object of current "obj".
        if (dstfieldId || !dyn_cast<CompositeType>(srcTy)) {
            return 0;
        }
        //First, is there existing parent object on record that can match "srcTy"?
        while (obj && obj->parent && obj->parent_field == 0) {
            obj = obj->parent;
            pto->targetObject = obj;
            pto->dstfieldId = 0;
            if (InstructionUtils::same_types(srcTy,obj->targetType)) {
                //Got the match!
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to\
                an existing parent object to match the srcPointer!\n";
#endif
                //Matched: host obj.
                return 4;
            }
        }
        //No matching parent objects on file, now consider whether we can create one, according to the given "srcTy".
        if (!create_host) {
            return 0;
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "AliasAnalysisVisitor::matchPtoTy(): try to create a host object to match the srcTy!\n";
#endif
        FieldDesc *fd = InstructionUtils::getHeadFieldDesc(srcTy);
        if (!fd || fd->fid.size() != fd->host_tys.size()) {
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << "!!! AliasAnalysisVisitor::matchPtoTy(): failed to get the header FieldDesc of srcTy, or the FieldDesc is invalid!\n";
#endif
            return 0;
        }
        if (fd->findTy(obj->targetType) >= 0) {
            //Ok, the "srcTy" can be a parent type for the "obj", there are two possibilities now:
            //(1) current obj is composite, then we will treat it as an emb obj and recursively create its host objs.
            //(2) it's not composite, then we need to first expand (reset) it to the innermost 
            //emb obj, whose host objs will then be created recursively. 
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << "AliasAnalysisVisitor::matchPtoTy(): srcTy is a valid host type of current pointee object, creating the host obj...\n";
#endif
            InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
            if (!dyn_cast<CompositeType>(obj->targetType)) {
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): expand the non-composite src obj to the innermost emb obj.\n";
#endif
                //TODO: should we still use the old "value" of the obj?
                obj->reset(obj->getValue(),fd->host_tys[0],loc);
            }
            DRCHECKER::createHostObjChain(fd,pto,fd->fid.size(),loc);
            //Sanity check.
            if (pto->targetObject && pto->dstfieldId == 0 && InstructionUtils::same_types(srcTy,pto->targetObject->targetType)) {
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): successfully created the required host obj!\n";
#endif
                //Matched: host obj.
                return 4;
            }
        } else if (obj->targetType && InstructionUtils::isPrimitiveTy(obj->targetType,8)) {
            //NOTE: if the current obj is of type "i8", we consider it as a wildcard that can match the heading field of any struct.
            //In this case, we will directly reset current obj to an obj of "srcTy". 
            InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
            obj->reset(obj->getValue(),srcTy,loc);
            //Matched: i8 wildcard.
            return 5;
        }
        return 0;
    }

    void AliasAnalysisVisitor::updatePointsToObjects(Value *p, AliasObject *obj, InstLoc *propInst, long dfid, bool is_weak) {
        if (!p || !obj) {
            return;
        }
        std::set<PointerPointsTo*> ptos;
        PointerPointsTo *pto = new PointerPointsTo(p,obj,dfid,propInst,is_weak);
        ptos.insert(pto);
        return this->updatePointsToObjects(p,&ptos,false);
    }

    void AliasAnalysisVisitor::updatePointsToObjects(Value *srcPointer, std::set<PointerPointsTo*> *newPointsToInfo, bool free = true) {
        /***
         *  Update the pointsto objects of the srcPointer to newPointstoInfo
         *  At the current instruction.
         *
         *  This also takes care of freeing the elements if they are already present.
         */
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "updatePointsToObjects for : " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
        if (!newPointsToInfo || newPointsToInfo->empty() || !srcPointer) {
            //nothing to update.
            return;
        }
        std::map<Value*, std::set<PointerPointsTo*>*> *targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        if (targetPointsToMap->find(srcPointer) == targetPointsToMap->end()) {
            (*targetPointsToMap)[srcPointer] = new std::set<PointerPointsTo*>();
        }
        std::set<PointerPointsTo*>* existingPointsTo = (*targetPointsToMap)[srcPointer];
        Type *srcPointeeTy = nullptr;
        if (InstructionUtils::isPrimitivePtr(srcPointer->getType()) ||
            InstructionUtils::isPrimitiveTy(srcPointer->getType()))
        {
            srcPointeeTy = InstructionUtils::inferPointeeTy(srcPointer);
        }else if (srcPointer->getType() && srcPointer->getType()->isPointerTy()) {
            srcPointeeTy = srcPointer->getType()->getPointerElementType();
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "#newPointsToInfo: " << newPointsToInfo->size() << " #existingPointsTo: " << existingPointsTo->size()
        << " expected pointee type: " << InstructionUtils::getTypeStr(srcPointeeTy) << "\n";
#endif
        std::set<PointerPointsTo*> matchedPtos, unmatchedPtos;
        for(PointerPointsTo *currPointsTo : *newPointsToInfo) {
            // Some basic sanity check.
            if (!currPointsTo || !currPointsTo->targetObject) {
                continue;
            }
            // for each points to, see if we already have that information, if yes, ignore it.
            if(std::find_if(existingPointsTo->begin(), existingPointsTo->end(), [currPointsTo,this](const PointerPointsTo *n) {
                return this->isPtoDuplicated(currPointsTo,n,false);
            }) == existingPointsTo->end()) {
                //Ok this pto doesn't appear in the existing records, now let's see whether it can match the type of srcPointer.
                Instruction *propInst = nullptr;
                if (currPointsTo->propagatingInst) {
                    propInst = dyn_cast<Instruction>(currPointsTo->propagatingInst->inst);
                }
                if (srcPointeeTy == nullptr || matchPtoTy(srcPointeeTy,currPointsTo,propInst) > 0) {
                    matchedPtos.insert(currPointsTo);
                }else {
                    unmatchedPtos.insert(currPointsTo);
                }
            } else {
                //delete the points to object, as we already have a similar pointsTo object.
                delete(currPointsTo);
            }
        }
        //The logic to update the pto records:
        //(1) if there exists type-matched ptos (i.e. "matchPtoTy" is not null), then only insert them - the type unmatched ones
        //are likely due to the polymorphism (e.g. file->private is an i8* which may point to different structs in different ioctls
        //even within a same driver).
        //(2) if all ptos are not type matched, to be conservative, just insert them all.
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "#matchedPtos: " << matchedPtos.size() << " #unmatchedPtos: " << unmatchedPtos.size() << "\n";
#endif
        std::set<PointerPointsTo*> *toAdd = &matchedPtos;
        if (matchedPtos.empty()) {
            toAdd = &unmatchedPtos;
        }else {
            //free the memory of useless ptos.
            for (PointerPointsTo *currPointsTo : unmatchedPtos) {
                delete(currPointsTo);
            }
        }
        for (PointerPointsTo *currPointsTo : *toAdd) {
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << "++ PTO: ";
            currPointsTo->print(dbgs());
#endif
            existingPointsTo->insert(existingPointsTo->end(), currPointsTo);
        }
        //Free the memory if required.
        if (free) {
            delete(newPointsToInfo);
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "updatePointsToObjects: #After update: " << existingPointsTo->size() << "\n";
#endif
    }

    bool AliasAnalysisVisitor::hasPointsToObjects(Value *srcPointer) {
        /***
         * Check if the srcPointer has any pointto objects at currInstruction
         */
        std::map<Value*, std::set<PointerPointsTo*>*> *targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        return targetPointsToMap != nullptr &&
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end() &&
               (*targetPointsToMap)[srcPointer] &&
               (*targetPointsToMap)[srcPointer]->size();
    }

    //In this version, we assume that "srcPointsTo" points to an embedded struct in a host struct.
    //NOTE: "srcPointer" in this function is related to "srcPointsTo".
    std::set<PointerPointsTo*> *AliasAnalysisVisitor::makePointsToCopy_emb(Instruction *propInstruction, Value *srcPointer, Value *resPointer,
                                                             std::set<PointerPointsTo*>* srcPointsTo, long fieldId) {
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            AliasObject *hostObj = currPointsToObj->targetObject;
            if (!hostObj) {
                continue;
            }
            long dstField = currPointsToObj->dstfieldId;
            Type *host_type = hostObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type: " 
            << InstructionUtils::getTypeStr(host_type) << " | " << dstField << "\n";
#endif
            //We must ensure that it points to an embedded composite type in another composite.
            if (!host_type || !dyn_cast<CompositeType>(host_type)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type is not composite!\n";
#endif
                continue;
            }
            //Boundary check for src pto.
            if (!InstructionUtils::isIndexValid(host_type,dstField)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): invalid dstField for the host_type!\n";
#endif
                continue;
            }
            //Get the dst field type (must be composite) in the host obj.
            Type *ety = InstructionUtils::getTypeAtIndex(host_type,dstField);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety: " << InstructionUtils::getTypeStr(ety) <<  " | " << fieldId << "\n";
#endif
            if (!ety || !dyn_cast<CompositeType>(ety)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety is not a composite field!\n";
#endif
                continue;
            }
            //Boundary check for dst pto.
            if (!InstructionUtils::isIndexValid(ety,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): boundary check fails for the ety!\n";
#endif
                continue;
            }
            //Ok, it's an emb struct/array, create new emb object if necessary.
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): trying to get/create an object for the embedded struct/array..\n";
#endif
            AliasObject *newObj = this->createEmbObj(hostObj,dstField,srcPointer,propInstruction);
            if (newObj) {
                PointerPointsTo *newPointsToObj = currPointsToObj->makeCopyP(resPointer,newObj,fieldId,
                                                                      new InstLoc(propInstruction,this->currFuncCallSites),false);
                newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
            } else{
#ifdef DEBUG_GET_ELEMENT_PTR
                errs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): cannot get or create embedded object.\n";
#endif
            }
        }
        return newPointsToInfo;
    }

    AliasObject *AliasAnalysisVisitor::createEmbObj(AliasObject *hostObj, long fid, Value *v, Instruction *I) {
        if (!hostObj) {
            return nullptr;
        }
        InstLoc *loc = nullptr;
        if (I) {
            loc = new InstLoc(I,this->currFuncCallSites);
        }else if (v) {
            loc = new InstLoc(v,this->currFuncCallSites);
        }
        AliasObject *eobj = hostObj->createEmbObj(fid,v,loc);
        if (eobj) {
            //We need to add it to the global pto records..
            if (v) {
                this->updatePointsToObjects(v,eobj,loc);
            }
        }else {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasAnalysisVisitor::createEmbObj(): failed to create the emb object!\n";
#endif
        }
        return eobj;
    }

    //NOTE: fieldId == -1 indicates it's a variable index.
    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy(Instruction *propInstruction, Value *srcPointer,
            std::set<PointerPointsTo*> *srcPointsTo, long fieldId) {
        /***
         * Makes copy of points to information from srcPointer to propInstruction
         */
        if (!srcPointsTo || srcPointsTo->empty()) {
            return nullptr;
        }
        std::set<PointerPointsTo*> *newPointsToInfo = new std::set<PointerPointsTo*>();
        // set of all visited objects to avoid added duplicate pointsto objects.
        std::set<std::pair<long,AliasObject*>> visitedObjects;
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): #elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        //The arg "srcPointer" actually is not related to arg "srcPointsTo", it's indeed "dstPointer" that we need to copy point-to inf for.
        GEPOperator *gep = (srcPointer ? dyn_cast<GEPOperator>(srcPointer) : nullptr);
        //"basePointerType" refers to the type of the pointer operand in the original GEP instruction/opearator, during whose visit we
        //call this makePointsToCopy().
        Type *basePointerType = (gep ? gep->getPointerOperand()->getType() : nullptr);
        Type *basePointToType = (basePointerType ? basePointerType->getPointerElementType() : nullptr);
        InstLoc *loc = new InstLoc(propInstruction,this->currFuncCallSites);
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            if (!currPointsToObj || !currPointsToObj->targetObject) {
                continue;
            }
            PointerPointsTo *pto = currPointsToObj->makeCopyP();
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): basePointerType: " << InstructionUtils::getTypeStr(basePointerType)
            << " cur pto: " << InstructionUtils::getTypeStr(pto->targetObject->targetType) << " | " << pto->dstfieldId
            << ", obj: " << (const void*)(pto->targetObject) <<  " dst fid: " << fieldId << "\n";
#endif
            //Try to match the pto w/ the GEP base pointee type.
            int r = this->matchPtoTy(basePointToType,pto,propInstruction);
            AliasObject *hostObj = pto->targetObject;
            long hostfid = pto->dstfieldId;
            auto to_check = std::make_pair(hostfid, hostObj);
            if(std::find(visitedObjects.begin(), visitedObjects.end(), to_check) != visitedObjects.end()) {
                //Already visited the obj|field.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): this pto was processed before.\n";
#endif
                goto fail_next;
            }
            visitedObjects.insert(to_check);
            //Some common assignments.
            pto->fieldId = 0;
            pto->targetPointer = srcPointer;
            pto->propagatingInst = loc;
            if (r > 0) {
                //The pointee can be matched w/ the gep base pointer
                //First perform a boundary check for the new fieldId.
                if (!InstructionUtils::isIndexValid(basePointToType,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): base pointer matched but new field id is OOB!\n";
#endif
                    goto fail_next;
                }
                if (r == 1 || r == 3) {
                    //Need to get/create the field embed object..
                    assert(InstructionUtils::same_types(hostObj->getFieldTy(hostfid),basePointToType));
                    //We will not specify the "v" arg of "createEmbObj", because it will trigger the pto update of "v",
                    //but "v" actually already has its pto - we just want to adjust the pointee across the nesting layer,
                    //and the adjusted pto is for the resulting pointer of the GEP, but not for the original base GEP pointer (i.e. "v").
                    //AliasObject *newObj = this->createEmbObj(hostObj,hostfid,gep->getPointerOperand(),propInstruction);
                    AliasObject *newObj = this->createEmbObj(hostObj,hostfid,nullptr,propInstruction);
                    if (newObj) {
                        pto->targetObject = newObj;
                        pto->dstfieldId = fieldId;
                    }else {
                        //This seems strange...
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "!!! AliasAnalysisVisitor::makePointsToCopy(): cannot get or create embedded object: " 
                        << InstructionUtils::getValueStr(gep) << "\n";
#endif
                        goto fail_next;
                    }
                }else if (r != 6) {
                    //We can directly change the field in this case, since the host object already matches the base pointer now.
                    assert(InstructionUtils::same_types(hostObj->targetType,basePointToType));
                    pto->dstfieldId = fieldId;
                }else {
                    //Should be impossible...
                    dbgs() << "!!! AliasAnalysisVisitor::makePointsToCopy(): base pointee is a primitive type\
                    but we have more than one index...\n";
                    goto fail_next;
                }
                newPointsToInfo->insert(pto);
            }else {
                //Fail to match the base pointer type...
                //TODO: what should we do? Discard this pto? Try to invoke bit2field()? Keep the pto anyway?
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::makePointsToCopy(): fail to match the base gep pointer!\n";
#endif
                goto fail_next;
            }
            continue;
fail_next:
            delete(pto);
        }
        if (newPointsToInfo->empty()) {
            delete(newPointsToInfo);
            newPointsToInfo = nullptr;
        }
#ifdef DEBUG_GET_ELEMENT_PTR
        if (newPointsToInfo) {
            for (PointerPointsTo *p : *newPointsToInfo) {
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): ++ ret pto: " 
                << InstructionUtils::getTypeStr(p->targetObject->targetType) << " | " << p->dstfieldId
                << ", obj: " << (const void*)(p->targetObject) << "\n";
            }
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): #ret: " << newPointsToInfo->size() << "\n";
        }
#endif
        return newPointsToInfo;
    }

std::set<PointerPointsTo*>* AliasAnalysisVisitor::mergePointsTo(std::set<Value*> &valuesToMerge, 
                                                                Instruction *targetInstruction, Value *targetPtr) {
    /***
     * Merge pointsToInformation of all the objects pointed by pointers in
     * valuesToMerge
     *
     * targetPtr(if not null) is the pointer that points to all objects in the merge set.
     */
    // Set of pairs of field and corresponding object.
    std::set<std::pair<long, AliasObject*>> targetObjects;
    targetObjects.clear();
    std::set<PointerPointsTo*> *toRetPointsTo = new std::set<PointerPointsTo*>();
    for (Value *currVal : valuesToMerge) {
        std::set<PointerPointsTo*> *tmpPointsTo = this->getPtos(targetInstruction,currVal);
        if (tmpPointsTo && !tmpPointsTo->empty()) {
            for (PointerPointsTo *currPointsTo : *tmpPointsTo) {
                auto to_check = std::make_pair(currPointsTo->dstfieldId, currPointsTo->targetObject);
                //de-duplication based on the pointee.
                if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                    PointerPointsTo *pto = currPointsTo->makeCopyP(targetPtr ? targetPtr : targetInstruction, currPointsTo->targetObject,
                    currPointsTo->dstfieldId, new InstLoc(targetInstruction,this->currFuncCallSites), false);
                    toRetPointsTo->insert(toRetPointsTo->begin(), pto);
                }
            }
        }
    }
    if (toRetPointsTo->empty()) {
        delete(toRetPointsTo);
        return nullptr;
    }
    return toRetPointsTo;
}

std::set<PointerPointsTo*>* AliasAnalysisVisitor::copyPointsToInfo(Instruction *srcInstruction, std::set<PointerPointsTo*>* srcPointsTo) {
    /***
     *  Copy pointsto information from the provided set (srcPointsTo)
     *  to be pointed by srcInstruction.
     */
    std::set<std::pair<long, AliasObject*>> targetObjects;
    targetObjects.clear();
    std::set<PointerPointsTo*>* toRetPointsTo = new std::set<PointerPointsTo*>();
    for(auto currPointsToObj : *srcPointsTo) {
        auto to_check = std::make_pair(currPointsToObj->dstfieldId, currPointsToObj->targetObject);
        //de-duplication based on the pointee.
        if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
            targetObjects.insert(targetObjects.end(), to_check);
            PointerPointsTo* pto = currPointsToObj->makeCopyP(srcInstruction, currPointsToObj->targetObject, currPointsToObj->dstfieldId, 
                                                              new InstLoc(srcInstruction,this->currFuncCallSites), false);
            toRetPointsTo->insert(toRetPointsTo->begin(), pto);
        }
    }
    if (toRetPointsTo->empty()) {
        delete(toRetPointsTo);
        return nullptr;
    }
    return toRetPointsTo;
}

void AliasAnalysisVisitor::setLoopIndicator(bool inside_loop) {
    this->inside_loop = inside_loop;
}

void AliasAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
    /***
     *  Visit alloca instruction.
     *  This is the origin of an object
     */
    if(hasPointsToObjects(&I)){
        /*
         * We have already visited this instruction before.
         */
#ifdef DEBUG_ALLOCA_INSTR
        dbgs() << "The Alloca instruction, already processed: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        return;
    }
    AliasObject *targetObj = new FunctionLocalVariable(I, this->currFuncCallSites);
#ifdef DEBUG_ALLOCA_INSTR
    dbgs() << "Processed Alloca Instruction, Created new points to information:" << (*newPointsTo) << "\n";
#endif
    this->updatePointsToObjects(&I, targetObj, new InstLoc(&I,this->currFuncCallSites));
}

void AliasAnalysisVisitor::visitCastInst(CastInst &I) {
    /***
     * This method handles Cast Instruction.
     * First check if we are converting to pointer, if yes, then we need to compute points to
     * If not, check if src value has points to information, if yes, then we need to compute points to
     */
    Type *dstType = I.getDestTy();
    Type *srcType = I.getSrcTy();
    Type *srcPointeeTy = nullptr;
    Type *dstPointeeTy = nullptr;
    if (srcType && srcType->isPointerTy()) {
        srcPointeeTy = srcType->getPointerElementType();
    }
    if (dstType && dstType->isPointerTy()) {
        dstPointeeTy = dstType->getPointerElementType();
    }
    Value *srcOperand = I.getOperand(0);
#ifdef DEBUG_CAST_INSTR
    dbgs() << "AliasAnalysisVisitor::visitCastInst: " << InstructionUtils::getValueStr(&I) << "\n";
    dbgs() << "Convert: " << InstructionUtils::getTypeStr(srcType) << " --> " << InstructionUtils::getTypeStr(dstType) << "\n";
    dbgs() << "srcOperand: " << InstructionUtils::getValueStr(srcOperand) << "\n";
#endif
    std::set<PointerPointsTo*> *srcPointsToInfo = this->getPtos(&I,srcOperand);
    if (srcPointsToInfo && !srcPointsToInfo->empty()) {
        //In this situation, our overall logic is to propagate all point-to information from the src operand to the dst operand,
        //however, we may have some special processing about the point-to information (e.g. change the type of the point-to obj).
        //Create new pointsTo info for the current instruction.
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for(PointerPointsTo *currPointsToObj : *srcPointsToInfo) {
            if (!currPointsToObj->targetObject || !currPointsToObj->targetObject->targetType) {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCastInst(): null targetObject or null type info!\n";
#endif
                //Discard this point-to.
                continue;
            }
            //NOTE: the "targetObject" will not be copied (only the pointer to it will be copied).
            PointerPointsTo *newPointsToObj = (PointerPointsTo*)currPointsToObj->makeCopy();
            //TODO: do we need to keep the original InstLoc (i.e. that of the pointer to cast)?
            newPointsToObj->propagatingInst = new InstLoc(&I,this->currFuncCallSites);
            newPointsToObj->targetPointer = &I;
            Type *currTgtObjType = newPointsToObj->targetObject->targetType;
#ifdef DEBUG_CAST_INSTR
            dbgs() << "AliasAnalysisVisitor::visitCastInst(): current target object: " 
            << InstructionUtils::getTypeStr(currTgtObjType) << " | " << currPointsToObj->dstfieldId << "\n";
#endif
            if (dstPointeeTy) {
                this->matchPtoTy(dstPointeeTy,newPointsToObj,&I);
            }else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCastInst(): the cast destination is not a pointer\
                , simply propagate the point-to record from src to dst...\n";
#endif
            }
            newPointsToInfo->insert(newPointsToObj);
        }
        // Update the points to Info of the current instruction.
        if (newPointsToInfo->size() > 0) {
            this->updatePointsToObjects(&I, newPointsToInfo);
        }
    }else if (dstType->isPointerTy()) {
        //hz: TODO: do we need to create new OutsideObject here of the dstType?
#ifdef DEBUG_CAST_INSTR
        dbgs() << "WARNING: Trying to cast a value (that points to nothing) to pointer, Ignoring\n";
#endif
        //assert(false);
    }else {
        //This can be a value conversion (e.g. i32 -> i64) that can be ignored.
        //Below is the original Dr.Checker's logic.
        if(!this->inside_loop) {
#ifdef STRICT_CAST
            assert(!srcType->isPointerTy());
#endif
#ifdef DEBUG_CAST_INSTR
            dbgs() << "Ignoring casting as pointer does not point to anything\n";
#endif
        }else {
#ifdef DEBUG_CAST_INSTR
            dbgs() << "Is inside the loop..Ignoring\n";
#endif
        }
    }
}

    //TODO: we need to handle the potential pointer arithmetic here...
    void AliasAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
        /***
        *  Handle binary instruction.
        *
        *  get the points to information of both the operands and merge them.
        */

        // merge points to of all objects.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getOperand(0));
        allVals.insert(allVals.end(), I.getOperand(1));
        std::set<PointerPointsTo*> *finalPointsToInfo = mergePointsTo(allVals, &I);
        if(finalPointsToInfo && !finalPointsToInfo->empty()) {
            // Update the points to object of the current instruction.
#ifdef DEBUG_BINARY_INSTR
            dbgs() << "Updating points to information in the binary instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            this->updatePointsToObjects(&I, finalPointsToInfo);
        } else {
#ifdef DEBUG_BINARY_INSTR
            dbgs() << "No value is a pointer in the binary instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        }
        // Sanity,
        // it is really weired if we are trying to do a binary operation on 2-pointers
        if(hasPointsToObjects(I.getOperand(0)) && hasPointsToObjects(I.getOperand(1))) {
#ifdef DEBUG_BINARY_INSTR
            dbgs() << "WARNING: Trying to perform binary operation on 2-pointers: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        }
    }

    void AliasAnalysisVisitor::visitPHINode(PHINode &I) {
        /***
        *  Merge points to of all objects reaching this phi node.
        */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for (unsigned i = 0; i < I.getNumIncomingValues(); ++i) {
            allVals.insert(I.getIncomingValue(i));
        }
        std::set<PointerPointsTo*> *finalPointsToInfo = mergePointsTo(allVals, &I);
        if (finalPointsToInfo && !finalPointsToInfo->empty()) {
            // Attach the load tag of this phi merge.
            if (finalPointsToInfo->size() > 1) {
                int id = 0;
                for (PointerPointsTo *pto : *finalPointsToInfo) {
                    pto->loadTag.push_back(new TypeField(&I,id++,nullptr));
                }
            }
            // Update the points to object of the current instruction.
            this->updatePointsToObjects(&I, finalPointsToInfo);
#ifdef DEBUG_PHI_INSTR
            dbgs() << "Merging points to information in the PHI instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        } else {
#ifdef DEBUG_PHI_INSTR
            dbgs() << "None pto records of the PHI instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        }
    }

    void AliasAnalysisVisitor::visitSelectInst(SelectInst &I) {
        /***
        *  Merge points to of all objects reaching this select instruction.
        */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getTrueValue());
        allVals.insert(allVals.end(), I.getFalseValue());
        std::set<PointerPointsTo*> *finalPointsToInfo = mergePointsTo(allVals, &I);
        if (finalPointsToInfo && !finalPointsToInfo->empty()) {
            // Attach the load tag of this phi merge.
            if (finalPointsToInfo->size() > 1) {
                int id = 0;
                for (PointerPointsTo *pto : *finalPointsToInfo) {
                    pto->loadTag.push_back(new TypeField(&I,id++,nullptr));
                }
            }
            // Update the points to object of the current instruction.
            this->updatePointsToObjects(&I, finalPointsToInfo);
        }
    }

    //Handle the inlined pointer operatrions, e.g., GEP (GEP ...) ..., phi (GEP (cast...)..., ...).
    //The goal is to keep processing the inlined instructions (e.g., cast, gep) until we get the
    //corresponding pto records.
    Value *AliasAnalysisVisitor::handleInlinePointerOp(Instruction *I, Value *srcPointer) {
        if (!srcPointer || hasPointsToObjects(srcPointer)) {
            return srcPointer;
        }
        //First try to strip the pointer cast.
        Value *v = srcPointer->stripPointerCasts();
        if (v != srcPointer && hasPointsToObjects(v)) {
#ifdef DEBUG_HANDLE_INLINE_POINTER
            dbgs() << "AliasAnalysisVisitor::handleInlinePointerOp(): Got pto by stripping cast: " 
            << InstructionUtils::getValueStr(srcPointer) << " -> " << InstructionUtils::getValueStr(v) << "\n";
#endif
            return v;
        }
        //Is it an embedded GEP operator? If so, handle it via "visitGetElementPtrOperator()".
        if (dyn_cast<GEPOperator>(v) && !dyn_cast<GetElementPtrInst>(v)) {
#ifdef DEBUG_HANDLE_INLINE_POINTER
            dbgs() << "AliasAnalysisVisitor::handleInlinePointerOp(): Dealing w/ the embedded GEP: "
            << InstructionUtils::getValueStr(v) << "\n";
#endif
            return this->visitGetElementPtrOperator(I,dyn_cast<GEPOperator>(v));
        }
        //Well, we've tried our best.
        return v;
    }

    //Different from "getPointsToObjects()", this function will try best to get the pto info, if the raw
    //pointer doesn't have pto, it will do the necessary cast and gep stripping.
    std::set<PointerPointsTo*> *AliasAnalysisVisitor::getPtos(Instruction *I, Value *srcPointer, bool create_dummy, bool taint) { 
        if (!srcPointer) {
            return nullptr;
        }
        if (hasPointsToObjects(srcPointer)) {
            return this->getPointsToObjects(srcPointer);
        }
        Value *v = this->handleInlinePointerOp(I,srcPointer);
        if (create_dummy && !hasPointsToObjects(v)) {
            //Ok, try to create the dummy pointee.
            //TODO: create the dummy w/ the original "srcPointer" or "v" (possibly stripped)?
            this->createOutsideObj(v,I,taint);
        }
        return this->getPointsToObjects(v);
    }

    //hz: this method aims to deal with the embedded GEP operator (in "I") in a recursive way.
    //It will try to analyze and record the point-to information in the global state for each GEP operator.
    Value* AliasAnalysisVisitor::visitGetElementPtrOperator(Instruction *I, GEPOperator *gep) {
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::visitGetElementPtrOperator(): " << InstructionUtils::getValueStr(I) << "\n";
        dbgs() << "GEP: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
        //Null pointer or we have processed it before.
        if (!gep || hasPointsToObjects(gep)) {
            return gep;
        }
        if (gep->getNumOperands() == 0 || !gep->getPointerOperand()) {
            //What happens...
            return gep;
        }
        //Process the 1st index at first...
        std::set<PointerPointsTo*> *initialPointsTo = this->processGEPFirstDimension(I, gep);
        //Then the remaining indices if any and update the point-to for this GEP.
        this->processMultiDimensionGEP(I, gep, initialPointsTo);
        return gep;
    }

    void AliasAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        /***
         *  Handle GetElementPtr instruction.
         *  This is tricky instruction.
         *  this is where accessing structure fields happen.
         */
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::visitGetElementPtrInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        //Process the 1st index at first...
        std::set<PointerPointsTo*> *initialPointsTo = this->processGEPFirstDimension(&I, dyn_cast<GEPOperator>(&I));
        //Then the remaining indices if any and update the point-to for this GEP.
        this->processMultiDimensionGEP(&I, dyn_cast<GEPOperator>(&I), initialPointsTo);
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitGetElementPtrInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    void AliasAnalysisVisitor::processMultiDimensionGEP(Instruction *propInst, GEPOperator *I, std::set<PointerPointsTo*> *srcPointsTo) {
        assert(I);
        if (!I || !srcPointsTo || srcPointsTo->empty()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): !I || !srcPointsTo || srcPointsTo->empty()\n";
#endif
            if (srcPointsTo) delete(srcPointsTo);
            return;
        }
        std::set<PointerPointsTo*> *todo_set = new std::set<PointerPointsTo*>();
        std::set<PointerPointsTo*> *final_set = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *pto : *srcPointsTo) {
            if (pto->flag) {
                final_set->insert(pto);
                //one-time use.
                pto->flag = 0;
            } else {
                todo_set->insert(pto);
            }
        }
        //Free the memory..
        delete(srcPointsTo);
        if (!todo_set->empty()) {
            bool update = true;
            //process all indecies from the 1st one (index 0 has been handled before).
            for (int i = 2; i < I->getNumOperands(); ++i) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "About to process index: " << (i-1) << "\n";
#endif
                ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(i));
                long fid = (CI ? CI->getZExtValue() : -1);
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "Index value: " << fid << "\n";
#endif
                //Loop invariant: "!todo_set->empty()".
                std::set<PointerPointsTo*> *newPointsToInfo = nullptr;
                if (i > 2) {
                    //More than 2 indices in this GEP, according to the GEP specification, this means the last (i-1) index
                    //must index into an embedded struct, instead of a pointer field.
                    //TODO: operator vs. inst
                    Value *subGEP = InstructionUtils::createSubGEP(I,i-1);
                    Value *resGEP = nullptr;
                    if (i >= I->getNumOperands()-1) {
                        resGEP = I;
                    }else {
                        resGEP = InstructionUtils::createSubGEP(I,i);
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "subGEP: " << InstructionUtils::getValueStr(subGEP) << "\n";
                    dbgs() << "resGEP: " << InstructionUtils::getValueStr(resGEP) << "\n";
#endif
                    if (subGEP) {
                        newPointsToInfo = makePointsToCopy_emb(propInst, subGEP, resGEP, todo_set, fid);
                    }
                }else {
                    //Most GEP should only have 2 indices..
                    newPointsToInfo = makePointsToCopy(propInst, I, todo_set, fid);
                }
                if (!newPointsToInfo || newPointsToInfo->empty()) {
                    //Fallback: just update w/ the current "todo_set" except when this is a 2-dimension GEP.
                    if (i == 2) {
                        update = false;
                    }
                    if (newPointsToInfo) delete(newPointsToInfo);
                    break;
                }
                //Free the memory occupied by pto records of last iteration..
                for (PointerPointsTo *p : *todo_set) {
                    if (p) delete(p);
                }
                delete(todo_set);
                todo_set = newPointsToInfo;
            }
            if (update && todo_set && !todo_set->empty()) {
                final_set->insert(todo_set->begin(),todo_set->end());
            }
            //Free the memory..
            if (todo_set) delete(todo_set);
        }
        if (!final_set->empty()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): updating the point-to for current GEP...\n";
#endif
            //make sure the points-to information includes the correct TargetPointer, which is current GEP inst.
            //TODO: is this ok? Since the pointsTo->targetPointer may not be the "I", it may be a GEP with a subset of indices created by us.
            for (PointerPointsTo *pointsTo : *final_set) {
                pointsTo->targetPointer = I;
            }
            this->updatePointsToObjects(I, final_set);
        }else {
            delete(final_set);
        }
    }

    //Analyze the 1st dimension of the GEP (the arg "I") and return a point-to set of the 1st dimension.
    std::set<PointerPointsTo*> *AliasAnalysisVisitor::processGEPFirstDimension(Instruction *propInst, GEPOperator *I) {
        if (!I) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Null GEP instruction..\n";
#endif
            return nullptr;
        }
        //First get the base pointer and its pointees..
        Value* srcPointer = I->getPointerOperand();
#ifdef CREATE_DUMMY_OBJ_IF_NULL
        std::set<PointerPointsTo*> *basePointsTo = this->getPtos(propInst,srcPointer,true,true);
#else
        std::set<PointerPointsTo*> *basePointsTo = this->getPtos(propInst,srcPointer);
#endif
        if (!basePointsTo || basePointsTo->empty()) {
            //No way to sort this out...
#ifdef DEBUG_GET_ELEMENT_PTR
            errs() << "AliasAnalysisVisitor::processGEPFirstDimension(): No points-to for: " 
            << InstructionUtils::getValueStr(srcPointer) << ", return\n";
#endif
            return nullptr;
        }
        //Make a copy of the basePointsTo
        std::set<PointerPointsTo*> *srcPointsTo = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *p : *basePointsTo) {
            if (!p || !p->targetObject) {
                continue;
            }
            PointerPointsTo *np = p->makeCopyP();
            np->propagatingInst = new InstLoc(propInst,this->currFuncCallSites);
            np->targetPointer = I;
            np->fieldId = 0;
            np->flag = 0;
            srcPointsTo->insert(np);
        }
        //Get the original pointer operand used in this GEP and its type info.
        Value *orgPointer = I->getPointerOperand();
        if (!orgPointer) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Null orgPointer..return\n";
#endif
            return nullptr;
        }
        Type *basePointerTy = orgPointer->getType();
        Type *basePointeeTy = nullptr;
        if (basePointerTy && basePointerTy->isPointerTy()) {
            basePointeeTy = basePointerTy->getPointerElementType();
        }
        bool is_base_prim = (basePointeeTy && InstructionUtils::isPrimitiveTy(basePointeeTy));
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension():: basePointerTy: " 
        << InstructionUtils::getTypeStr(basePointerTy) << "\n";
#endif
        //Get the 1st dimension. 
        ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(1));
        if (!CI) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Non-constant 0st index!\n";
#endif
            //The index is a variable, in this case, if we can confirm that the base pto points to an element in an array, then
            //we can simply change the pto fieldId to "-1" (representing the variable index in an array), otherwise:
            //(1) if the base pointer is primitive (e.g. i8*) but it actually points to somewhere within a composite object, 
            //we will know nothing about the resulting pto udner a variable offset, so just return nullptr;
            //(2) if not, we assume the base pointer is in an array, but since we cannot confirm this, we return the original pto
            //intact (i.e. treat the variable index as "0").
            for (auto it = srcPointsTo->begin(); it != srcPointsTo->end();) {
                PointerPointsTo *pto = *it;
                int ty_match = matchPtoTy(basePointeeTy,pto,propInst);
                if (pto->switchArrayElm(basePointeeTy,-1) == 0) {
                    //The pto is not in an array of basePointeeTy...
                    if ((is_base_prim && pto->targetObject && !InstructionUtils::isPrimitiveTy(pto->targetObject->targetType)) || !ty_match) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Discard pto for variable 0st index: ";
                        ((ObjectPointsTo*)pto)->print(dbgs());
#endif
                        delete(pto);
                        it = srcPointsTo->erase(it);
                        continue;
                    }
                }
                ++it;
            }
            if (srcPointsTo->empty()) {
                delete(srcPointsTo);
                srcPointsTo = nullptr;
            }
            return srcPointsTo;
        }
        long index = CI->getSExtValue();
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): 0st index: " << index << "\n";
#endif
        std::set<PointerPointsTo*> *resPointsTo = new std::set<PointerPointsTo*>();
        DataLayout *dl = this->currState.targetDataLayout;
        if (basePointeeTy && dl && index) {
            bool is_primitive = InstructionUtils::isPrimitiveTy(basePointeeTy);
            //NOTE: we use alloc size here since 1st GEP index is intended to index an array 
            //of the basePointeeTy (i.e. the basePointeeTy will be stored consecutively so we need its alloc size).
            unsigned width = dl->getTypeAllocSizeInBits(basePointeeTy);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): basePointeeTy size: " 
            << width << ", is_primitive: " << is_primitive << "\n";
#endif
            for (PointerPointsTo *currPto : *srcPointsTo) {
                //Type match in the object parent/embed hierarchy.
                int ty_match = matchPtoTy(basePointeeTy,currPto,propInst);
                if (currPto->switchArrayElm(basePointeeTy,index) > 0) {
                    //The host object is an array of basePointeeTy and we have successfully swicthed the field id according
                    //to the 0st index in the gep...
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Current pto is in an array, we've changed its fieldId.\n";
#endif
                    resPointsTo->insert(currPto);
                } else {
                    if (!is_primitive) {
                        //The 1st index is not for an array, instead it's for pointer arithmetic, 
                        //this usually only happens when the GEP base pointee is primitive (e.g. i8)
                        //in which case the GEP has just one index, but now we have a non-primitive 
                        //base pointer for pointer arithmetic (and the GEP can have multiple indices)...
                        //What we do here is we convert this GEP to a one-index GEP w/ primitive base 
                        //pointee, by calculating the overall bit offset of this multi-index GEP. 
                        int rc;
                        index = InstructionUtils::calcGEPTotalOffsetInBits(I,dl,&rc);
                        if (rc) {
                            //This means we fail to calculate the total offset of current GEP... No way to handle it then.
#ifdef DEBUG_GET_ELEMENT_PTR
                            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): fail to get the\
                            total offset of current non-primitive GEP to handle the non-zero 1st index...\n";
#endif
                            continue;
                        }
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): calculated offset sum in bits: " << index << "\n";
#endif
                        width = 1; //bit unit.
                        //Tell the visitGEP() that it doesn't need to process the remainig indices 
                        //(if any) since we have converted this GEP to single-index for this pto.
                        currPto->flag = 1;
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): invoke bit2Field()...\n";
#endif
                    if (!this->bit2Field(propInst,I,currPto,width,index)) {
                        resPointsTo->insert(currPto);
                    }else {
                        delete(currPto);
                    }
                }
            } //For loop
        } else {
            delete(resPointsTo);
            return srcPointsTo;
        }
        delete(srcPointsTo);
        return resPointsTo;
    }

    //Starting from "dstfieldId" in the target object (struct) as specified in "pto", 
    //if we step bitWidth*index bits, which field will we point to then?
    //The passed-in "pto" will be updated to point to the resulted object and field. 
    //(e.g. we may end up reaching a field in an embed obj in the host obj).
    //NOTE: we assume the "pto" has been verified to be a struct pointer.
    int AliasAnalysisVisitor::bit2Field(Instruction *propInst, GEPOperator *I, PointerPointsTo *pto, unsigned bitWidth, long index) {
        if (index == 0) {
            return 0;
        }
        DataLayout *dl = this->currState.targetDataLayout;
        if (!dl || !pto) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): !dl || !pto\n";
#endif
            return -1;
        }
        long dstOffset = 0, resOffset = 0, bits = 0, org_bits = (long)bitWidth * index, org_dstOffset = 0;
        std::vector<FieldDesc*> *tydesc = nullptr;
        int i_dstfield = 0;
        AliasObject *targetObj = nullptr;
        Type *targetObjTy = nullptr;
        while (true) {
            targetObj = pto->targetObject;
            long dstfield = pto->dstfieldId;
            targetObjTy = targetObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): host obj: " << InstructionUtils::getTypeStr(targetObjTy) 
            << " | " << dstfield << " obj ID: " << (const void*)targetObj << "\n";
#endif
            if (!targetObjTy || !dyn_cast<CompositeType>(targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): not a composite host type, return...\n";
#endif
                return -1;
            }
            //Boundary check.
            if (!InstructionUtils::isIndexValid(targetObjTy,dstfield)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): dstfield out-of-bound.\n";
#endif
                return -1;
            }
            tydesc = InstructionUtils::getCompTyDesc(dl,dyn_cast<CompositeType>(targetObjTy));
            if (!tydesc) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): we cannot get the detailed type desc for current host obj, return...\n";
#endif
                return -1;
            }
            if (dstfield == -1) {
                //We're now pointing to a variable indexed element in an array (i.e. it can be any element), in this
                //case, if we add some offsets to the current pointer, it may result in the same element, or a different
                //one in the array - anyway, the final location is again uncertain, so here we will contain the final
                //offset in this same variable indexed element, by modding the element size.
                assert(dyn_cast<SequentialType>(targetObjTy));
                Type *ety = dyn_cast<SequentialType>(targetObjTy)->getElementType();
                unsigned esz = dl->getTypeStoreSizeInBits(ety);
                resOffset = index * (long)bitWidth;
                resOffset %= (long)esz;
                if (resOffset < 0) {
                    resOffset += esz;
                }
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): we have a variable index in an array, contain the resOffset"
                << " within the same element: " << resOffset << "\n";
#endif
                break;
            }
            i_dstfield = InstructionUtils::locateFieldInTyDesc(tydesc,dstfield);
            if (i_dstfield < 0) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): we cannot locate the dst field desc in the type desc vector, return...\n";
#endif
                return -1;
            }
            //NOTE: both "dstOffset" and "bits" can be divided by 8, "bits" can be negative.
            dstOffset = (*tydesc)[i_dstfield]->bitoff;
            org_dstOffset += dstOffset;
            bits = index * (long)bitWidth;
            resOffset = dstOffset + bits;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): dstOffset(org_dstOffset): " << dstOffset << "(" << org_dstOffset << ")";
            dbgs() << " bits(org_bits): " << bits << "(" << org_bits << ")" << " resOffset: " << resOffset << "\n";
#endif
        	//NOTE: llvm DataLayout class has three kinds of type size:
        	//(1) basic size, for a composite type, this is the sum of the size of each field type.
        	//(2) store size, a composite type may need some paddings between its fields for the alignment.
        	//(3) alloc size, two successive composite types may need some paddings between each other for alignment.
        	//For our purpose, we need the real size for a single type, so we use "store size", note that 
            //if the type is array, "store size" already takes the padding between each element into account.
            if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(targetObjTy)) {
                //This is possibly the case of "container_of()" where one tries to access the host object from within the embedded object,
                //what we should do here is try to figure out what's the host object and adjust the point-to accordingly.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): resOffset (in bits) out-of-bound,"
                << " possibly the container_of() case, trying to figure out the host object...\n";
#endif
				if (targetObj->parent && targetObj->parent->targetType) {
                    //Ok, parent object on file.
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::bit2Field(): parent object on file, try it..\n";
#endif
                    pto->targetObject = targetObj->parent;
                    pto->dstfieldId = targetObj->parent_field;
                    bitWidth = 1;
                    index = resOffset;
                } else {
                    break;
                }
            } else {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): current container object can satisfy the result offset!\n";
#endif
                break;
            }
        }
        if (!resOffset) {
            if (pto->dstfieldId > 0) {
                pto->dstfieldId = 0;
            }
            return 0;
        }
        //Have we got the parent object that can hold the resOffset?
        if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(pto->targetObject->targetType)) {
            //No.. We need infer the container type...
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): the recorded parent object is not enough,"
            << " we need to infer the unknown container object...\n";
#endif
            //We cannot use "dstOffset" here, we should use the realDstOffset of the original GEP base pointer...
            CandStructInf *floc = DRCHECKER::inferContainerTy(propInst->getModule(),I->getPointerOperand(),
                                                              pto->targetObject->targetType,org_dstOffset);
            if (!floc || !floc->fds || floc->ind[0] < 0 || floc->ind[0] >= floc->fds->size()) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): failed to infer the container type...\n";
#endif
                if (floc) delete(floc);
                return -1;
            }
            //Check whether the container can contain the target offset (in theory this should already been verified by inferContainerTy())
            tydesc = floc->fds;
            i_dstfield = floc->ind[0];
            delete(floc);
            dstOffset = (*tydesc)[i_dstfield]->bitoff;
            resOffset = dstOffset + org_bits;
            targetObjTy = (*tydesc)[0]->host_tys[(*tydesc)[0]->host_tys.size()-1];
            if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): the inferred container object still cannot hold the target bitoff...\n";
#endif
                return -1;
            }
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): successfully identified the container object,"
            << " here is the FieldDesc of the original pointee bitoff:\n";
            (*tydesc)[i_dstfield]->print(dbgs());
            dbgs() << "AliasAnalysisVisitor::bit2Field(): dstOffset: " << dstOffset << " bits: " 
            << org_bits << " resOffset: " << resOffset << "\n";
#endif
            //Ok, we may need to create the host object chain for the location pointed to by the GEP base pointer if necessary.
            int limit = (*tydesc)[i_dstfield]->host_tys.size();
            DRCHECKER::createHostObjChain((*tydesc)[i_dstfield],pto,limit,new InstLoc(propInst,this->currFuncCallSites));
            if (!InstructionUtils::same_types(pto->targetObject->targetType,targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): incomplete creation of the host obj chain.\n";
#endif
                return -1;
            }
            if (!resOffset) {
                //This means the resulting pointer will point to the beginning of the created host object, so update the dstFieldId.
                pto->dstfieldId = 0;
                return 0;
            }
        }
        //Ok, now we are sure that the target "resOffset" will not exceed the current host object
        //since we've created all required container objects.
        //Next, we need to see whether this "resOffset" is inside an embedded composite typed field
        //within the container object, and recursively create the embedded object when necessary.
        int i_resoff = InstructionUtils::locateBitsoffInTyDesc(tydesc,resOffset);
        if (i_resoff < 0) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): Cannot locate the resOffset in the type desc, return...\n";
#endif
            return -1;
        }
        FieldDesc *fd = (*tydesc)[i_resoff];
        if (fd->fid.size() != fd->host_tys.size()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): fd->fid.size() != fd->host_tys.size()\n";
#endif
            return -1;
        }
        int limit = -1;
        //NOTE: at a same bit offset there can be a composite field who recursively contains multiple composite sub-fields at its head:
        // e.g. [[[   ]    ]     ], in this case the type desc will record all these sub composite fields at the head and all #fid is 0,
        //while we don't really want to create the embedded object up to the innermost heading composite field, instead we stop at the outermost
        //head composite field here.
        while (++limit < fd->fid.size() && !fd->fid[limit]);
        bool need_free = false;
        if (pto->dstfieldId == -1) {
            //Need to do a little hack here since the original FieldDesc doesn't support "-1" field.
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): Change the FieldDesc outermost field id to -1...\n";
#endif
            fd = new FieldDesc(fd);
            fd->fid[fd->fid.size()-1] = -1;
            need_free = true;
        }
        int r = DRCHECKER::createEmbObjChain(fd,pto,limit,new InstLoc(propInst,this->currFuncCallSites));
        if (need_free) delete(fd);
        if (r > limit) {
            //There must be something wrong in the createEmbObjChain()...
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): something wrong w/ the createEmbObjChain()\
            , point-to result will be unreliable, discard..\n";
#endif
            return -1;
        }
        return 0;
    }

    void AliasAnalysisVisitor::visitLoadInst(LoadInst &I) {
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "AliasAnalysisVisitor::visitLoadInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        // Get the src points to information.
#ifdef CREATE_DUMMY_OBJ_IF_NULL
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,srcPointer,true,true);
#else
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,srcPointer);
#endif
        if (!srcPointsTo || srcPointsTo->empty()) {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "AliasAnalysisVisitor::visitLoadInst(): srcPointer does not point to any object.\n";
#endif
            return;
        }
        // OK, now what? :)
        // Get all objects pointed by all the objects in the srcPointsTo
        // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
        std::set<std::pair<long, AliasObject*>> targetObjects, finalObjects;
        std::set<PointerPointsTo*> *newPointsToInfo = new std::set<PointerPointsTo*>();
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        long id = 0;
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject* dstObj = currPointsToObj->targetObject;
            auto to_check = std::make_pair(target_field, dstObj);
            //De-duplication for the target memory locations..
            if (std::find(targetObjects.begin(), targetObjects.end(), to_check) != targetObjects.end()) {
                continue;
            }
            targetObjects.insert(targetObjects.end(), to_check);
            //Fetch objects that could be pointed by the pointer in the target mem location.
            std::set<std::pair<long,AliasObject*>> pointees;
            dstObj->fetchPointsToObjects(target_field, pointees, propInst);
            for (auto &e : pointees) {
                //De-duplication for the pointees of the pointers in those memory locations..
                if (std::find(finalObjects.begin(), finalObjects.end(), e) != finalObjects.end()) {
                    continue;
                }
                finalObjects.insert(e);
                //Create the pto for the fetched pointee.
                PointerPointsTo *pto = new PointerPointsTo(&I, dstObj, target_field, e.second, e.first, 
                                                           new InstLoc(&I,this->currFuncCallSites), false);
                //Set up the load tag to handle the potential N*N update problem.
                pto->loadTag = currPointsToObj->loadTag;
                pto->loadTag.push_back(new TypeField(&I,id++,(void*)dstObj));
                newPointsToInfo->insert(newPointsToInfo->end(), pto);
            }
        }
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "AliasAnalysisVisitor::visitLoadInst(): #targetObjects: " << targetObjects.size() << " #finalObjects: " 
        << finalObjects.size() << "\n";
#endif
        if (newPointsToInfo->size() > 0) {
#ifdef FAST_HEURISTIC
            //A hard limit on #pto, we need to try best to avoid this.
            if(newPointsToInfo->size() > MAX_ALIAS_OBJ) {
                auto end = std::next(newPointsToInfo->begin(), (long)MAX_ALIAS_OBJ);
                std::set<PointerPointsTo*> tmpList;
                tmpList.clear();
                tmpList.insert(newPointsToInfo->begin(), end);
                newPointsToInfo->clear();
                newPointsToInfo->insert(tmpList.begin(), tmpList.end());
            }
#endif
            // Just save the newly created set as points to set for this instruction.
            this->updatePointsToObjects(&I, newPointsToInfo);
        } else {
            delete(newPointsToInfo);
            // points to set is empty.
            // Make sure that we are not trying to load a pointer.
            if(!this->inside_loop) {
                //hz: if we reach here, possibly the previously stripped pointer is incorrect,
                //instead of the assert, we'd better ignore this and hope later analysis can create an OutsideObject for current LoadInst.
                //assert(!I.getType()->isPointerTy());
            }
        }
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitLoadInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    void inferSrcDstMap(std::set<PointerPointsTo*> *srcPointsTo, std::set<PointerPointsTo*> *dstPointsTo,
                        std::map<PointerPointsTo*,std::set<PointerPointsTo*>> &sdMap) {
        if (!srcPointsTo || !dstPointsTo) {
            return;
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "inferSrcDstMap(): #srcPointsTo: " << srcPointsTo->size() << " #dstPointsTo: " << dstPointsTo->size() << "\n";
#endif
        if (dstPointsTo->size() <= 1 || srcPointsTo->empty()) {
            //No mapping if we only have one dst mem location.
            return;
        }
        //Locate the most recent load tag in common for the src and dst.
        //First ensure that every dst pto's load tag is similar in hierarchy (i.e. same layer load and same load src).
        std::vector<TypeField*> *dtag = &((*(dstPointsTo->begin()))->loadTag);
        std::vector<TypeField*> *stag = &((*(srcPointsTo->begin()))->loadTag);
        if (dtag->empty() || stag->empty()) {
            return;
        }
        int dl = dtag->size(), sl = stag->size(); 
        for (PointerPointsTo *pto : *dstPointsTo) {
            dl = std::min(dl,InstructionUtils::isSimilarLoadTag(dtag,&(pto->loadTag)));
            if (dl <= 0) {
#ifdef DEBUG_STORE_INSTR
                dbgs() << "inferSrcDstMap(): The load tags are not uniformed between dsts.\n";
#endif
                return;
            }
        }
        //Ok, all dst mem locs have similar load tags, now it's the turn of "srcPointsTo".
        for (PointerPointsTo *pto : *srcPointsTo) {
            sl = std::min(sl,InstructionUtils::isSimilarLoadTag(stag,&(pto->loadTag)));
            if (sl <= 0) {
#ifdef DEBUG_STORE_INSTR
                dbgs() << "inferSrcDstMap(): The load tags are not uniformed between srcs.\n";
#endif
                return;
            }
        }
        //Now decide whether the src and dst load tags have any common links, and if so, find the most recent link.
        int si,di;
        for (si = 1; si <= sl; ++si) {
            for (di = 1; di <= dl; ++di) {
                if (((*stag)[stag->size()-si])->isSimilarLoadTag((*dtag)[dtag->size()-di])) {
                    break;
                }
            }
            if (di <= dl) {
                break;
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "inferSrcDstMap(): sl/si: " << sl << "/" << si << ", dl/di: " << dl << "/" << di << "\n";
#endif
        if (si > sl) {
            //This means there are no common links between the load tags of the src and dst.. So no N*N update issue here.
#ifdef DEBUG_STORE_INSTR
            dbgs() << "inferSrcDstMap(): No common tags between src and dst.\n";
#endif
            return;
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "inferSrcDstMap(): v: " << InstructionUtils::getValueStr(((*stag)[stag->size()-si])->v) << "\n";
#endif
        //Ok, now create the mapping between the src and dst, according to the load tags.
        std::set<PointerPointsTo*> mappedSrc,mappedDst;
        for (PointerPointsTo *dpto : *dstPointsTo) {
            TypeField *dt = (dpto->loadTag)[dpto->loadTag.size()-di];
            for (PointerPointsTo *spto : *srcPointsTo) {
                TypeField *st = (spto->loadTag)[spto->loadTag.size()-si];
                if (dt->isSameLoadTag(st)) {
                    sdMap[dpto].insert(spto);
                    mappedSrc.insert(spto);
                    mappedDst.insert(dpto);
                }
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "inferSrcDstMap(): #mappedSrc: " << mappedSrc.size() << " #mappedDst " << mappedDst.size() << "\n";
#endif
        //TODO: what if not all src or dst are included in the mapping? Should we fall back to the N*N update? 
        //Or just discard the unmapped ones? Currently we do the later.
        //Print out the missing src/dst.
        if (mappedSrc.size() < srcPointsTo->size()) {
            for (PointerPointsTo *pto : *srcPointsTo) {
                if (mappedSrc.find(pto) == mappedSrc.end()) {
#ifdef DEBUG_STORE_INSTR
                    dbgs() << "[MISSING SRC]: ";
                    pto->print(dbgs());
#endif
                }
            }
        }
        if (mappedDst.size() < dstPointsTo->size()) {
            for (PointerPointsTo *pto : *dstPointsTo) {
                if (mappedDst.find(pto) == mappedDst.end()) {
#ifdef DEBUG_STORE_INSTR
                    dbgs() << "[MISSING DST]: ";
                    pto->print(dbgs());
#endif
                    //This forces the pto update process to skip the dst mem loc..
                    sdMap[pto].clear();
                }
            }
        }
        return;
    }

    void AliasAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_STORE_INSTR
        dbgs() << "AliasAnalysisVisitor::visitStoreInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        // Get the src points to information.
        Value *targetValue = I.getValueOperand();
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,targetValue);
        //Get the dst points-to info.
        //NOTE: although "dstPointsTo" might be useless if the "srcPointsTo" is null in this function, we still
        //invoke "getPtos()" for it here to help the subsequent taint analysis to resolve nested operators (e.g., GEP)
        //in the store target. 
        Value *targetPointer = I.getPointerOperand();
        std::set<PointerPointsTo*> *dstPointsTo = this->getPtos(&I,targetPointer);
        if (!srcPointsTo || srcPointsTo->empty()) {
            //The src to store doesn't point to anything, maybe this is because the src is a scalar instead of a pointer,
            //anyway no need to process this store inst any more since what we are doing is a point-to analysis.
#ifdef DEBUG_STORE_INSTR
            dbgs() << "visitStoreInst(): src does not point to anything: " << InstructionUtils::getValueStr(targetValue) << "; Ignoring.\n";
#endif
            //TODO: can we ignore the timing info since this is an early return?
            return;
        }
        if(!dstPointsTo || dstPointsTo->empty()) {
#ifdef DEBUG_STORE_INSTR
            dbgs() << "Trying to store something into pointer, which does not point to anything\n";
#endif
#ifdef STRICT_STORE
            assert("Null dstPointsTo set in visitStoreInst()" && false);
#endif
            //TODO: can we ignore the timing info since this is an early return?
            return;
        }
        //Handle the N*N update case (i.e. there are multiple src pointers and dst mem locations, but instead of letting
        //every location hold every src pointer, we may need to consider the relationship between src and dst and do the
        //precise update). One example is as below:
        //%0 <-- load src.f0 //imagine src now points to N mem locations, so %0 may also have N pointees loaded.
        //store %0 --> src.f1 //since src has N potential mem locations, so does src.f1, but here it's not precise to do the N*N update
        //the correct way is to do the 1*1 update for N different src locations - the underlying truth is "src" can only point to
        //*one* location in the actual run.
        std::map<PointerPointsTo*,std::set<PointerPointsTo*>> sdMap;
        inferSrcDstMap(srcPointsTo,dstPointsTo,sdMap);
        //NOTE: when processing the store inst we do *not* need to update the pto info for the "targetPointer" - it will
        //always point to the same location(s). What we really need to update is the pto info of the memory location(s) pointed
        //to by the "targetPointer" (i.e. "targetPointer" is a 2nd order pointer).
        int is_weak = dstPointsTo->size() > 1 ? 1 : 0;
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        int num_pto = 0;
        for (PointerPointsTo *currPointsTo : *dstPointsTo) {
            // perform update
            std::set<PointerPointsTo*> *ptos = ((sdMap.find(currPointsTo) != sdMap.end()) ? &(sdMap[currPointsTo]) : srcPointsTo);
            if (ptos) {
                num_pto += ptos->size(); 
                currPointsTo->targetObject->updateFieldPointsTo(currPointsTo->dstfieldId, ptos, propInst, is_weak);
            }
        }
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitStoreInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void AliasAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        assert(false);
    }

    void AliasAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        assert(false);
    }

    //Propagate the pto records of the actual args to the formal args. 
    void AliasAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction, std::vector<Instruction *> *newCallContext) {

        std::map<Value*, std::set<PointerPointsTo*>*> *currFuncPointsTo = currState.getPointsToInfo(newCallContext);

        // This ensures that we never analyzed this function with the same context.
        //assert(currFuncPointsTo->size() == 0);

        unsigned int arg_no = 0;

        for (User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++, arg_no++) {
            Value *currArgVal =(*arg_begin).get();
            std::set<Value*> valuesToMerge;
            valuesToMerge.clear();
            valuesToMerge.insert(currArgVal);
            //Locate the corresponding formal arg.
            Argument *farg = InstructionUtils::getArg(currFunction,arg_no);
            if (!farg) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "!!! AliasAnalysisVisitor::setupCallContext(): cannot get formal arg " << (arg_no + 1) << "!\n";
#endif
                continue;
            }
            //first get pto info of the actual arg and copy them for the related formal arg.
            std::set<PointerPointsTo*> *currArgPointsTo = mergePointsTo(valuesToMerge, &I, farg);
            if (currArgPointsTo && !currArgPointsTo->empty()) {
#ifdef DEBUG_CALL_INSTR
                // OK, we need to add pointsto.
                dbgs() << "AliasAnalysisVisitor::setupCallContext(): arg " << (arg_no + 1) << " has points to information\n";
#endif
                (*currFuncPointsTo)[farg] = currArgPointsTo;
            }
        }
    }


    //Precondition: I is a call inst to a memcpy style function.
    Type *AliasAnalysisVisitor::getMemcpySrcTy(CallInst &I) {
        //Get the copy size if any.
        Function *func = I.getCalledFunction();
        unsigned sz = 0;
        if (func && func->hasName()) {
            std::string name = func->getName().str();
            if (name.find("memcpy") != std::string::npos) {
                Value *sa = I.getArgOperand(2);
                if (dyn_cast<ConstantInt>(sa)) {
                    sz = dyn_cast<ConstantInt>(sa)->getZExtValue();
                }
            }
        }
#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::getMemcpySrcTy(): memcpy size: " << sz << "\n";
#endif
        //Get the types inferred from the function argument and the context instructions.
        std::set<Type*> candTys;
        Type *ty = InstructionUtils::inferPointeeTy(I.getArgOperand(0));
        if (ty) {
            candTys.insert(ty);
        }
        ty = InstructionUtils::inferPointeeTy(I.getArgOperand(1));
        if (ty) {
            candTys.insert(ty);
        }
        DataLayout *dl = this->currState.targetDataLayout;
        if (!dl) {
            dbgs() << "!!! AliasAnalysisVisitor::getMemcpySrcTy(): No datalayout...\n";
            if (candTys.size() == 1) {
                return *(candTys.begin());
            }
            return nullptr;
        }
        int min = -1;
        Type *rty = nullptr;
        if (sz == 0) {
            //This means we either have a variable memcpy size, or the function is not memcpy..
            //In this case, to be conservative, return the minimal type we have.
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::getMemcpySrcTy(): we have no memcpy size info, so try to return the min ty between src and dst.\n";
#endif
            for (Type *ty : candTys) {
                int tysz = dl->getTypeStoreSize(ty);
                if (min < 0 || tysz < min) {
                    min = tysz;
                    rty = ty;
                }
            }
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::getMemcpySrcTy(): minTy: " << InstructionUtils::getTypeStr(rty) << "\n";
#endif
            return rty;
        }
#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::getMemcpySrcTy(): try to find the type nearest to the memcpy size.\n";
#endif
        for (Type *ct : candTys) {
            std::set<Type*> htys;
            InstructionUtils::getHeadTys(ct,htys);
            for (Type *ht : htys) {
                int delta = (int)(dl->getTypeStoreSize(ht)) - (int)sz;
                if (delta < 0) {
                    delta = 0 - delta;
                }
                if (min < 0 || delta < min) {
                    min = delta;
                    rty = ht;
                }
            }
        }
        return rty;
    }

    //Given a pto and a *CompositeType*, return the matched sub- or super- obj of the pointee obj.
    AliasObject *AliasAnalysisVisitor::getObj4Copy(PointerPointsTo *pto, CompositeType *ty, Instruction &I) {
        if (!pto || !ty) {
            return nullptr;
        }
        int r = this->matchPtoTy(ty,pto,&I,true);
        if (r == 0) {
            return nullptr;
        }
        AliasObject *obj = pto->targetObject;
        if (r == 1 || r == 3) {
            obj = this->createEmbObj(pto->targetObject,pto->dstfieldId,nullptr,&I);
        }
        return obj;
    }

    PointerPointsTo *AliasAnalysisVisitor::copyObj(Value *dstPointer, PointerPointsTo *srcPto, Type *ty, Instruction &propInst) {
        if (!srcPto || !ty) {
            return nullptr;
        }
        CompositeType *cty = dyn_cast<CompositeType>(ty);
        InstLoc *loc = new InstLoc(&propInst,this->currFuncCallSites);
        PointerPointsTo *np = srcPto->makeCopyP(dstPointer,loc);
        AliasObject *nobj = nullptr;
        if (cty) {
            AliasObject *eobj = this->getObj4Copy(np,cty,propInst);
            if (eobj) {
                nobj = eobj->makeCopy(loc);
            }else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::copyObj(): cannot match the src object to copy.\n";
#endif
            }
        }else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::copyObj(): the expected type is not composite, so only copy one field...\n";
#endif
            //This means the copy type is non-composite, which is less likely (possibly because no
            //type info in the context), so we only copy one non-composite field if possible.
            nobj = new HeapLocation(propInst, ty, this->currFuncCallSites, nullptr, false);
            //Propagate the taint and pto records.
            nobj->mergeField(0, np->targetObject, np->dstfieldId, loc, false);
        }
        if (nobj) {
            np->targetObject = nobj;
            np->dstfieldId = 0;
            return np;
        }else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::copyObj(): null nobj.\n";
#endif
            delete(np);
            delete(loc);
        }
        return nullptr;
    }

    void AliasAnalysisVisitor::handleMemcpyFunction(std::vector<long> &memcpyArgs, CallInst &I) {
        // handle memcpy instruction.
#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): Processing memcpy function.\n";
#endif
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get points to information.
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,srcOperand);
        if (!srcPointsTo || srcPointsTo->empty()) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): no src pto info!\n";
#endif
            return;
        }
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);
        std::set<PointerPointsTo*> *dstPointsTo = this->getPtos(&I,dstOperand);
        //Ok, now decide the src type to copy.
        Type *ty = this->getMemcpySrcTy(I);
        CompositeType *cty = ty ? dyn_cast<CompositeType>(ty) : nullptr;
#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): inferred memcpy ty: " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        InstLoc *loc = new InstLoc(&I,this->currFuncCallSites);
        if (!dstPointsTo || dstPointsTo->empty()) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): no dst pto info!\n";
#endif
            //Simply make a copy of the src AliasObject for the dst pointer.
            std::set<PointerPointsTo*> newPtos;
            for (PointerPointsTo *pto : *srcPointsTo) {
                if (!pto || !pto->targetObject) {
                    continue;
                }
#ifdef DEBUG_CALL_INSTR
                dbgs() << "[SRC_PTO] ";
                pto->print(dbgs());
#endif
                PointerPointsTo *np = this->copyObj(&I, pto, ty, I);
                if (np) {
                    newPtos.insert(np);
                }
            }
            if (!newPtos.empty()) {
                this->updatePointsToObjects(dstOperand,&newPtos,false);
            }
        }else {
            std::map<PointerPointsTo*,std::set<PointerPointsTo*>> sdMap;
            bool multi_pto = false;
            if (dstPointsTo->size() > 1) {
                //Try to infer the src dst mapping since this may be a N*N copy, similar as the case in visitStoreInst().
                inferSrcDstMap(srcPointsTo,dstPointsTo,sdMap);
                multi_pto = true;
            }
            for (PointerPointsTo *dpto : *dstPointsTo) {
                if (!dpto || !dpto->targetObject) {
                    continue;
                }
#ifdef DEBUG_CALL_INSTR
                dbgs() << "[DST PTO] ";
                dpto->print(dbgs());
#endif
                //First make sure the dst pointee object is capable of receving the copy type..
                AliasObject *dobj = nullptr;
                if (cty) {
                    dobj = this->getObj4Copy(dpto,cty,I);
                    if (!dobj) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): cannot get the dst obj to copy to!\n";
#endif
                        continue;
                    }
                }
                std::set<PointerPointsTo*> *srcs = ((sdMap.find(dpto) != sdMap.end()) ? &(sdMap[dpto]) : srcPointsTo);
                for (PointerPointsTo *spto : *srcs) {
                    if (!spto || !spto->targetObject) {
                        continue;
                    }
                    AliasObject *sobj = nullptr;
                    if (cty) {
                        sobj = this->getObj4Copy(spto,cty,I);
                        if (!sobj) {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): cannot get the src obj to copy to: ";
                            spto->print(dbgs());
#endif
                            continue;
                        }
                    }
                    if (sobj && dobj) {
                        //Merge the src object to the dst object..
                        dobj->mergeObj(sobj,loc,multi_pto);
                    }else {
                        //Fallback: try to merge the single field if possible..
                        dpto->targetObject->mergeField(dpto->dstfieldId,spto->targetObject,spto->dstfieldId,loc,multi_pto);
                    }
                }
            }
        }
    }

    void AliasAnalysisVisitor::handleFdCreationFunction(std::map<long,long> &fdFieldMap, Function *currFunc, CallInst &I) {
        if (!currFunc) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Null currFunc!!!\n";
#endif
            return;
        }
        //We need to create a new struct.file object and set its field point-to according to the field-to-arg map.
        std::string fn("file");
        Type *file_ty = InstructionUtils::getStTypeByName(I.getModule(), fn);
        if (!file_ty) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Cannot get the struct.file type!!!\n";
#endif
        }
        //If we have already visited this call site then the file obj should already be created, now let's just skip it.
        //NOTE: count == 1 means that it's the first time we're analyzing current BB, among all call contexts.
        if ( this->currState.numTimeAnalyzed.find(I.getParent()) != this->currState.numTimeAnalyzed.end() &&
             this->currState.numTimeAnalyzed[I.getParent()] > 1 ) {
            //TODO: "anon_inode_getfd" doesn't return the pointer to the created file struct, 
            //so we don't need to update the point-to of this call inst,
            //but we may have other fd creation functions that needs us to do so. If that's the case, 
            //we need to retrieve the previously created obj and update the pointer.
            return;
        }
        //Type based object creation.
        OutsideObject *newObj = DRCHECKER::createOutsideObj(file_ty);
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        if (newObj) {
            //Since this is a fd, we always treat it as a global taint source.
            newObj->setAsTaintSrc(propInst,true);
            //Update the field point-to according to the "fdFieldMap" and the global pto record if necessary.
            for (auto &e : fdFieldMap) {
                long fid = e.first;
                long arg_no = e.second;
                if (arg_no == -1) {
                    //this means the function return value should point to the newly created file struct.
                    this->updatePointsToObjects(&I, newObj, propInst);
                    continue;
                }
                if (arg_no < 0 || arg_no >= (long)I.getNumArgOperands()) {
                    continue;
                }
                Value *arg = I.getArgOperand(arg_no);
                if (arg && hasPointsToObjects(arg)) {
                    std::set<PointerPointsTo*>* srcPointsTo = getPointsToObjects(arg);
                    //We're sure that the "newObj" field pto will be updated, so it's a strong update.
                    newObj->updateFieldPointsTo(fid,srcPointsTo,propInst,0);
                }
            }
            if (DRCHECKER::enableXentryImpObjShare) {
                DRCHECKER::addToSharedObjCache(newObj);
            }
        }else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Cannot create the file struct!!!\n";
#endif
        }
    }

    void AliasAnalysisVisitor::handleMemdupFunction(CallInst &I) {
        //res_ptr = memdup(src_ptr,size), note that memdup is responsible to allocate a buf for res_ptr.
        // get src operand
        Value *srcOperand = I.getArgOperand(0);
        Value *sizeArg = I.getArgOperand(1);
        // the dst operand is the return value (i.e. the callinst itself)
        Value *dstOperand = &I;
        //Decide the obj type to create, from the dst pointer.
        Type *ty = InstructionUtils::inferPointeeTy(dstOperand);
        if (!ty) {
            dbgs() << "!!! AliasAnalysisVisitor::handleMemdupFunction(): failed to infer the dst obj type!\n";
            return;
        }
        CompositeType *cty = dyn_cast<CompositeType>(ty);
#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): inferred memdup obj type: " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        //Is this a memdup from the user space? If so, we need to treat it as a user initiated taint source later.
        bool from_user = false;
        Function *func = I.getCalledFunction();
        if (func && func->hasName()) {
            std::string n = func->getName().str();
            if (n.find("user") != std::string::npos) {
                from_user = true;
            }
        }
        //Get the src pointees.
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,srcOperand);
        //Propagate src pto to the dst, or create new dummy dst objs.
        InstLoc *loc = new InstLoc(&I,this->currFuncCallSites);
        std::set<PointerPointsTo*> newPtos;
        if (srcPointsTo && !srcPointsTo->empty()) {
            for (PointerPointsTo *pto : *srcPointsTo) {
                if (!pto || !pto->targetObject) {
                    continue;
                }
#ifdef DEBUG_CALL_INSTR
                dbgs() << "[SRC PTO]: ";
                pto->print(dbgs());
#endif
                PointerPointsTo *np = this->copyObj(&I, pto, ty, I);
                if (np) {
                    newPtos.insert(np);
                    //if this is a memdup_user, we may need to force a user taint on the dst obj, in case it's not propagated
                    //from the src for some reasons. In this case, it's unlikely that newly added inherent TFs will accidentally
                    //kill the existing TFs since kernel code cannot directly operate on the user space object (so no existing TFs).
                    if (from_user) {
                        AliasObject *obj = np->targetObject;
                        if (np->dstfieldId) {
                            obj = obj->getEmbObj(np->dstfieldId);
                        }
                        if (obj) {
                            obj->setAsTaintSrc(loc,!from_user);
                        }
                    }
                }else {
                    dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): failed to copy the obj from current src!\n";
                }
            }
        }
        if (!newPtos.empty()) {
            this->updatePointsToObjects(&I,&newPtos,false);
        }else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleMemcpyFunction(): no pto info copied from src, create new dummy pointee obj!\n";
#endif
            //No src pointees, in this case we need to create the new dummy obj for the dst pointer..
            AliasObject *obj = new HeapLocation(I, ty, this->currFuncCallSites, sizeArg, false);
            //Anyway we need to set the newly created obj as the taint source, user initiated or not.
            obj->setAsTaintSrc(loc,!from_user);
            //update the pto for dst pointer.
            this->updatePointsToObjects(&I,obj,loc);
        }
    }

    void AliasAnalysisVisitor::handleCfuFunction(std::set<long> &taintedArgs, CallInst &I) {
        //handle copy_from_user(to, src, size)
        //The src object must come from the user space, so we can assume that there are no existing TFs or ptos associated
        //w/ the src object, on the other hand, the dst pointer is mostly likely related to a newly allocated object (e.g. kmalloc),
        //so here we only need to take care of the dst pointee object. (i.e. set it as the user taint source).
        for (auto currArgNo : taintedArgs) {
            Value *currArg = I.getArgOperand(currArgNo);
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Current argument: " << InstructionUtils::getValueStr(currArg) << "\n";
#endif
            Type *ty = InstructionUtils::inferPointeeTy(currArg);
            if (!ty) {
                dbgs() << "!!! AliasAnalysisVisitor::handleCfuFunction(): failed to infer the dst obj type!\n";
                continue;
            }
            CompositeType *cty = dyn_cast<CompositeType>(ty);
            //Get the dst pto info.
            std::set<PointerPointsTo*> *dstPointsTo = this->getPtos(&I,currArg);
            std::set<PointerPointsTo*> newPtos;
            bool user_tainted = false;
            InstLoc *loc = new InstLoc(&I,this->currFuncCallSites);
            if (dstPointsTo != nullptr && !dstPointsTo->empty()) {
                for (PointerPointsTo *pto : *dstPointsTo) {
                    if (!pto || !pto->targetObject) {
                        continue;
                    }
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "[DST PTO] ";
                    pto->print(dbgs());
#endif
                    AliasObject *obj = nullptr;
                    if (cty) {
                        obj = this->getObj4Copy(pto,cty,I);
                        if (!obj) {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << "AliasAnalysisVisitor::handleCfuFunction(): cannot match the inferred obj ty w/ the comp dst pto.\n";
#endif
                            continue;
                        }
                    }else {
                        obj = pto->targetObject->getEmbObj(pto->dstfieldId);
                    }
                    if (obj) {
                        obj->clearAllInhTFs();
                        obj->setAsTaintSrc(loc,false);
                        user_tainted = true;
                    }
                }
            }
            if (!user_tainted) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::handleCfuFunction(): Try to create a new dummy dst obj to init the user taint!\n";
#endif
                //Create a dummy dst object as the user taint source.
                //TODO: the "size" arg.
                AliasObject *obj = new HeapLocation(I, ty, this->currFuncCallSites, nullptr, false);
                //Set the newly created obj as the user space taint source.
                obj->setAsTaintSrc(loc,false);
                //update the pto for dst pointer.
                this->updatePointsToObjects(currArg,obj,loc);
            }
        }
    }

    VisitorCallback* AliasAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
            std::vector<Instruction *> *oldFuncCallSites,
            std::vector<Instruction *> *callSiteContext) {

#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        std::string currFuncName = currFunc->getName().str();
        // if we do not have function definition
        // that means, it is a kernel internal function.
        // call kernel intra-function handler.
        if (currFunc->isDeclaration()) {
            FunctionChecker *targetChecker = (AliasAnalysisVisitor::functionHandler)->targetChecker;
            if (targetChecker->is_memcpy_function(currFunc)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCallInst(): This is a memcpy function w/o definition.\n";
#endif
                // handle memcpy function.
                std::vector<long> memcpyArgs = targetChecker->get_memcpy_arguments(currFunc);
                this->handleMemcpyFunction(memcpyArgs, I);
            }else if (targetChecker->is_memdup_function(currFunc)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCallInst(): This is a memdup function w/o definition.\n";
#endif
                //handle the memdup function.
                this->handleMemdupFunction(I);
            }else if (targetChecker->is_taint_initiator(currFunc)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCallInst(): This is a copy_from_user function.\n";
#endif
                //handling __copy_from_user and its friends.
                std::set<long> taintedArgs = targetChecker->get_tainted_arguments(currFunc);
                this->handleCfuFunction(taintedArgs, I);
            }else if (targetChecker->is_fd_creation_function(currFunc)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCallInst(): This is a fd creation function w/o definition.\n";
#endif
                // handle fd creation function
                std::map<long,long> fdFieldMap = targetChecker->get_fd_field_arg_map(currFunc);
                this->handleFdCreationFunction(fdFieldMap,currFunc,I);
            }else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCallInst(): Handle the Function: " << currFuncName << " in the default way.\n";
#endif
                bool is_handled = false;
                std::set<PointerPointsTo*> *newPointsToInfo = (std::set<PointerPointsTo*>*)
                                                              this->functionHandler->handleFunction(I, currFunc, this->currFuncCallSites,
                                                                                                    this->callback, is_handled);
                if (is_handled) {
                    if (newPointsToInfo && !newPointsToInfo->empty()) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Function handler returned some points to info to add.\n";
#endif
                        this->updatePointsToObjects(&I, newPointsToInfo);
                    }
                } else {
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "AliasAnalysisVisitor::visitCallInst(): not handled!\n";
#endif
                }
            }
            //TODO: upon a "memset" we need to somehow kill the existing pto records (but it's less likely that an object that already
            //has some pto records will be "memset" later..)
            return nullptr;
        }

        // Setup call context.
        setupCallContext(I, currFunc, callSiteContext);

        // Create a AliasAnalysisVisitor
        AliasAnalysisVisitor *vis = new AliasAnalysisVisitor(currState, currFunc, callSiteContext);

        return vis;
    }

    void AliasAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        AliasAnalysisVisitor *vis = (AliasAnalysisVisitor *)childCallback;
        if(vis->retValPointsTo.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            std::set<PointerPointsTo*> *newPointsToInfo = this->copyPointsToInfo(&I, &(vis->retValPointsTo));
            if(newPointsToInfo && !newPointsToInfo->empty()) {
                this->updatePointsToObjects(&I, newPointsToInfo);
            }
        }

    }

    void AliasAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        Value *targetRetVal = I.getReturnValue();
        if (!targetRetVal) {
            return;
        }
#ifdef DEBUG_RET_INSTR
        dbgs() << "AliasAnalysisVisitor::visitReturnInst(): Ret: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(&I,targetRetVal);
        if (srcPointsTo && !srcPointsTo->empty()) {
            // Get all objects pointed by all the objects in the targetRetVal
            for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
                if(std::find_if(this->retValPointsTo.begin(), this->retValPointsTo.end(), [currPointsToObj](const PointerPointsTo *n) {
                            return  n->pointsToSameObject(currPointsToObj);
                   }) == this->retValPointsTo.end()) 
                {
#ifdef DEBUG_RET_INSTR
                    dbgs() << "[RET PTO] ";
                    currPointsToObj->print(dbgs());
#endif
                    this->retValPointsTo.insert(currPointsToObj);
                }
            }
        } else {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Ret does not point to any object. Ignoring.\n";
#endif
        }
    }

    void AliasAnalysisVisitor::printAliasAnalysisResults(llvm::raw_ostream& O) const {
        /***
         * Dump all the alias analysis result information into provided stream.
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        for(auto ai:*targetPointsToMap) {
            O << "\nPointer:";
            ai.first->print(O);
            O << " has following points to information:\n";
            for(auto pp:*(ai.second)) {
                O << (*pp);
                O << "\n";
            }
        }
    }
}
