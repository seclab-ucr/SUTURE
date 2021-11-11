#include "AliasObject.h"

using namespace llvm;

namespace DRCHECKER {

    bool enableXentryImpObjShare = false;

    std::map<Type*,std::map<Function*,std::set<OutsideObject*>>> sharedObjCache;
    
    std::set<std::string> sharedObjTyStrs;

    Function *currEntryFunc = nullptr;

    bool validTyForOutsideObj(Type *ty) {
        if (!ty || !dyn_cast<CompositeType>(ty)) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "validTyForOutsideObj(): it's not a composite type, cannot create the outside obj!\n";
#endif
            return false;
        }
        if (InstructionUtils::isNullCompTy(ty)) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "validTyForOutsideObj(): it's an opaque struct type or null composite type, cannot create the outside obj!\n";
#endif
            return false;
        }
        return true;
    }

    void AliasObject::logFieldAccess(long srcfieldId, Instruction *targetInstr, const std::string &msg) {
        dbgs() << "\n*********FieldAccess(" << msg << ")**********\n";
        dbgs() << "Current Inst: " << InstructionUtils::getValueStr(targetInstr) << "\n";
        dbgs() << InstructionUtils::getTypeStr(this->targetType) << " | " << srcfieldId << " OBJ: " << (const void*)this << "\n";
        dbgs() << "Object Ptr: " << InstructionUtils::getValueStr(this->getValue()) << "\n";
        if (this->getValue()){
            /*
               if(dyn_cast<Instruction>(this->targetVar)){
                    dbgs() << "\n";
                    dyn_cast<Instruction>(this->targetVar)->getFunction()->print(dbgs());
               }
             */
        }
        dbgs() << "*******************\n";
    }

    //Taint the point-to object by field "srcfieldId" according to the field taint info.
    //NOTE: we assume this function is only called when a new field pointee object is created.
    void AliasObject::taintPointeeObj(AliasObject *newObj, long srcfieldId, InstLoc *targetInstr) {
        if (!newObj) {
            return;
        }
        /*
        //TODO: we need to re-consider whether to propagate the host field TF (inherent or not or both?) 
        //to the new dummy pointee obj, consider the case where a "store" assigns the address of a real 
        //obj to the host field - in that situation we actually wouldn't propagate the host field TFs.
        //If we disable the propagation, will we miss any potential bugs (e.g. to modify the host field 
        //is to select the pointee, indirectly controlling the pointee obj content)? But on the other hand, 
        //we can still match this dummy obj w/ other potential real objs that can be selected by changing
        //the host field..
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::taintPointeeObj(): " << (const void*)this << " | " << srcfieldId << " (src) --> " 
        << (const void*)newObj << " (sink)\n";
#endif
        std::set<TaintFlag*> tfs;
        this->getFieldTaintInfo(srcfieldId,tfs,targetInstr);
        for (TaintFlag *tf : tfs) {
            //if (tf->is_inherent) {
            //    continue;
            //}
            //NOTE: no need to check taint path again here since "getFieldTaintInfo" already ensure its validity.
            TaintFlag *ntf = new TaintFlag(tf,targetInstr);
            //NOTE: "is_weak" is inherited.
            newObj->taintAllFields(ntf);
        }
        */
        //If the host object is a global taint source, then we also set the newly created field pointee object as so.
        //TODO: justify this decision.
        if (this->is_taint_src) {
            newObj->setAsTaintSrc(targetInstr,(this->is_taint_src > 0));
        }
    }

    Type *getLoadedPointeeTy(Instruction *targetInstr) {
        if (targetInstr && dyn_cast<LoadInst>(targetInstr)) {
            Type *ptrTy = targetInstr->getType();
            if (ptrTy->isPointerTy()) {
                Type *ty = ptrTy->getPointerElementType();
                if (InstructionUtils::isPrimitiveTy(ty) || !dyn_cast<CompositeType>(ty)) {
                    //If the pointee type is primitive (e.g. i8*) or not composite, we may be able to 
                    //infer the real pointee struct type from the context.
                    Type *ity = InstructionUtils::inferPointeeTy(targetInstr);
                    if (ity) {
                        return ity;
                    }
                }
                return ty;
            }
        }
        return nullptr;
    }

    //We have switched to a different level 0 entry function, need to reset the activation status of the ptos.
    //(1) deactivate those active pto records set up when analyzing the previous entry functions.
    //(2) re-activate those inactive preset pto records (e.g. global struct definition) killed by last entry function.
    void AliasObject::resetPtos(long fid, Instruction *entry) {
        assert(entry && "reset must be invoked w/ a non-null entry inst!!!");
        if (this->lastPtoReset.find(fid) == this->lastPtoReset.end()) {
            this->lastPtoReset[fid] = entry;
        }
        if (this->lastPtoReset[fid] == entry) {
            //We're still within the same top-level entry function, no need to reset.
            return;
        }
        //Ok, we need to do the reactivation..
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "AliasObject::resetPtos(): Reset field pto for: " << (const void*)this << " | " << fid;
        dbgs() << ", switch entry to: ";
        InstructionUtils::printInst(entry,dbgs());
#endif
        this->lastPtoReset[fid] = entry;
        if (this->pointsTo.find(fid) == this->pointsTo.end()) {
            return;
        }
        std::set<ObjectPointsTo*> *srcPto = &(this->pointsTo[fid]);
        for (ObjectPointsTo *pto : *srcPto) {
            if (pto && pto->propagatingInst) {
                InstLoc *pil = pto->propagatingInst;
                if (pto->is_active && pil->hasCtx() && (*pil->ctx)[0] != entry) {
                    //Deactivate it.
                    this->activateFieldPto(pto,false);
#ifdef DEBUG_UPDATE_FIELD_POINT
                    dbgs() << "AliasObject::resetPtos(): de-activate point-to: ";
                    pto->print(dbgs());
#endif
                    continue;
                }
                if (!pto->is_active && !pil->hasCtx()) {
                    //This is a deactivated global preset pto, need to re-activate it since we're on a new entry.
                    this->activateFieldPto(pto,true);
#ifdef DEBUG_UPDATE_FIELD_POINT
                    dbgs() << "AliasObject::resetPtos(): re-activate point-to: ";
                    pto->print(dbgs());
#endif
                }
            }
        }
    }

    //"test_coverage" means whether to test and ensure the returned ptos have covered all paths from the entry to the "loc".
    void AliasObject::getLivePtos(long fid, InstLoc *loc, std::set<ObjectPointsTo*> *retPto, bool test_coverage) {
        if (this->pointsTo.find(fid) == this->pointsTo.end()) {
            return;
        }
        std::set<ObjectPointsTo*> *srcPto = &(this->pointsTo[fid]);
        if (!srcPto || !retPto || !loc) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getLivePtos(): !srcPto || !retPto || !loc\n";
#endif
            return;
        }
        int stCnt = retPto->size();
        //Preliminary processing: filter out the inactive pto records.
        std::set<ObjectPointsTo*> actPtos;
        for (ObjectPointsTo *pto : *srcPto) {
            if (pto && pto->is_active) {
                actPtos.insert(pto);
            }
        }
        if (actPtos.empty()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getLivePtos(): No active/valid pto records after pre-filtering!\n";
#endif
            return;
        }
        //Step 1: reachability test - whether a src pto (updated at a certain InstLoc) can reach current location.
        //NOTE: here we need to consider the case where one pto is killed along its path to the destination by another strong pto update.
        std::set<InstLoc*> blocklist;
        for (ObjectPointsTo *pto : actPtos) {
            if (pto->propagatingInst && !pto->is_weak) {
                blocklist.insert(pto->propagatingInst);
            }
        }
        for (ObjectPointsTo *pto : actPtos) {
            if (loc->reachable(pto->propagatingInst,&blocklist)) {
                retPto->insert(pto);
            }
            //Null pto->propagatingInst will make the "pto" be treated as a preset global pto record, the below is just for logging.
            if (!pto->propagatingInst) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "!!! AliasObject::getLivePtos(): pto w/o update site info: ";
                pto->print(dbgs());
#endif
            }
        }
        //Step 2: post-dom test - some pto records may "kill" others due to post-dom relationship.
        //TODO: do we really need this test here given that we have already done such a test when updating the field pto.
        //Step 3: de-duplication test. 
        //TODO: we may not need to do this as well since it's performed at the update time.
        //
        //The final step: path coverage check.
        //Can these pto records in "retPto" cover every path from the very beginning to current "loc"?
        //If not we need to create dummy objs for the uncovered paths.
        //If no live ptos then the caller will create dummy obj itself, no need for us. 
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::getLivePtos(): There are currently " << retPto->size() 
        << " live ptos in the return set, before path coverage test.\n";
#endif
        if (test_coverage && retPto->size() > 0) {
            bool has_global_pto= false;
            for (ObjectPointsTo *pto : *srcPto) {
                if (!pto->propagatingInst || !pto->propagatingInst->inEntry()) {
                    has_global_pto = true;
                    break;
                }
                InstLoc *pil = pto->propagatingInst;
                if (pil->ctx->size() == 1 && loc->hasCtx() && 
                    (*loc->ctx)[0] == (*pil->ctx)[0] && pil->inst && pil->inst == (*pil->ctx)[0]) {
                    //Has a pto set up at the level 0 function entry.
                    has_global_pto = true;
                    break;
                }
            }
            //Already have global pto (can follow any path) -> It's either activated now, 
            //or deactivated because it's completely blocked -> no need to test the path coverage any more.
            if (!has_global_pto) {
                //Test whether current active ptos can cover all paths from entry to "loc".
                blocklist.clear();
                for (ObjectPointsTo *pto : *retPto) {
                    if (pto && pto->propagatingInst) {
                        blocklist.insert(pto->propagatingInst);
                    }
                }
                if (loc->chainable(0,&blocklist,true)) {
                    //Ok, need to create the "default" dummy obj at the entry...
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                    dbgs() << "AliasObject::getLivePtos(): The current live ptos cannot cover every path"
                    << " to the current use site, needs to create dummy pto at the entry...\n";
#endif
                    if (loc->hasCtx() && (*loc->ctx)[0]) {
                        std::vector<Instruction*> *newCtx = new std::vector<Instruction*>(loc->ctx->begin(),loc->ctx->begin()+1);
                        InstLoc *il = new InstLoc((*loc->ctx)[0],newCtx);
                        std::set<std::pair<long, AliasObject*>> newObjs;
                        this->createFieldPointee(fid, newObjs, loc, il);
                        if (newObjs.empty()) {
                            //This is strange...
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                            dbgs() << "AliasObject::getLivePtos(): Fail to create dummy pto...\n";
#endif
                            return;
                        }
                        //We need to add these newly created pto (which are also live now) to the return set.
                        int cnt = 0;
                        for (ObjectPointsTo *pto : *srcPto) {
                            if (pto && pto->propagatingInst == il && pto->is_active) {
                                retPto->insert(pto);
                                ++cnt;
                            }
                        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "AliasObject::getLivePtos(): " << cnt << " dummy ptos (at the entry) inserted!\n";
#endif
                    }
                }
            }else {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::getLivePtos(): The field already has global pto, so no path coverage test...\n";
#endif
            }
        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::getLivePtos(): ";
        this->logFieldPto(fid,dbgs());
        dbgs() << "AliasObject::getLivePtos(): #final_ret: " << retPto->size() - stCnt << "\n";
#endif
        return;
    }

    //An index-insensitive version of "getEqvArrayElm()", the only reason we have this is for an evaluation of the
    //efficacy of index-sensitivity... 
    int AliasObject::getAllArrayElm(long fid, std::set<TypeField*> &res) {
        //First go to the top-level container.
        std::vector<long> path;
        AliasObject *obj = this;
        bool has_seq = false;
        while (obj->parent) {
            path.push_back(obj->parent_field);
            obj = obj->parent;
            if (dyn_cast<SequentialType>(obj->targetType)) {
                has_seq = true;
            }
        }
        if (!dyn_cast<SequentialType>(this->targetType) && !has_seq) {
            //No array at any layer, so impossible to have eqv elements.
            return 0;
        }
        //Go down the hill and identify all equivalent array elements, if any.
        std::set<AliasObject*> eqs;
        eqs.insert(obj);
        while (!path.empty()) {
            long f = path.back();
            path.pop_back();
            std::set<AliasObject*> to_add;
            if (dyn_cast<SequentialType>(obj->targetType)) {
                for (AliasObject *e : eqs) {
                    std::set<long> eqfs = e->getAllAvailableFields();
                    eqfs.insert(-1);
                    for (long t : eqfs) {
                        if (e->getEmbObj(t)) {
                            to_add.insert(e->getEmbObj(t));
                        }
                    }
                }
            }else {
                for (AliasObject *e : eqs) {
                    if (e->getEmbObj(f)) {
                        to_add.insert(e->getEmbObj(f));
                    }
                }
            }
            eqs.clear();
            eqs.insert(to_add.begin(),to_add.end());
            obj = obj->getEmbObj(f);
        }
        //Construct the final obj|field combinations.
        for (AliasObject *e : eqs) {
            if (dyn_cast<SequentialType>(e->targetType)) {
                std::set<long> eqfs = e->getAllAvailableFields();
                eqfs.insert(-1);
                for (long t : eqfs) {
                    TypeField *tf = new TypeField(e->targetType,t,e);
                    res.insert(tf);
                }
            }else {
                TypeField *tf = new TypeField(e->targetType,fid,e);
                res.insert(tf);
            }
        }
        return 1;
    }

    //Simply count the effective #tf of the field "srcfieldId" at the location of "currInst".
    int AliasObject::countFieldTfs(long srcfieldId, InstLoc *currInst) {
        FieldTaint *ft = this->getFieldTaint(srcfieldId);
        if (!ft || ft->empty()) {
            ft = &(this->all_contents_taint_flags);
        }
        std::set<TaintFlag*> r;
        if (!ft->empty()) {
            ft->doGetTf(currInst, r);
        }
        return r.size();
    }

    //Simply count the effective #pto of the field "srcfieldId" at the location of "currInst".
    int AliasObject::countFieldPtos(long srcfieldId, InstLoc *currInst) {
        if (this->pointsTo.find(srcfieldId) == this->pointsTo.end()) {
            return 0;
        }
        //Decide which pto records are valid at current load site (i.e. the InstLoc "currInst").
        std::set<ObjectPointsTo*> livePtos;
        this->getLivePtos(srcfieldId,currInst,&livePtos,false);
        int cnt = 0;
        for (ObjectPointsTo *obj : livePtos) {
            if (obj->fieldId == srcfieldId && obj->targetObject) {
                ++cnt;
            }
        }
        return cnt;
    }

    //If we are accessing a variable element (index: -1) of an array, that equals to access every normal element;
    //If we are accessing a normal element, then we also need to consider the pto/TF in the variable element.
    //RET: return 0 if it's not in an array, otherwise 1.
    int AliasObject::getEqvArrayElm(long fid, std::set<TypeField*> &res) {
        //First go to the top-level container.
        std::vector<long> path;
        AliasObject *obj = this;
        bool has_seq = false;
        while (obj->parent) {
            path.push_back(obj->parent_field);
            obj = obj->parent;
            if (dyn_cast<SequentialType>(obj->targetType)) {
                has_seq = true;
            }
        }
        if (!dyn_cast<SequentialType>(this->targetType) && !has_seq) {
            //No array at any layer, so impossible to have eqv elements.
            return 0;
        }
        //Go down the hill and identify all equivalent array elements, if any.
        std::set<AliasObject*> eqs;
        eqs.insert(obj);
        while (!path.empty()) {
            long f = path.back();
            path.pop_back();
            std::set<AliasObject*> to_add;
            if (dyn_cast<SequentialType>(obj->targetType)) {
                for (AliasObject *e : eqs) {
                    std::set<long> eqfs;
                    if (f == -1) {
                        eqfs = e->getAllAvailableFields();
                    }else {
                        eqfs.insert(f);
                    }
                    eqfs.insert(-1);
                    for (long t : eqfs) {
                        if (e->getEmbObj(t)) {
                            to_add.insert(e->getEmbObj(t));
                        }
                    }
                }
            }else {
                for (AliasObject *e : eqs) {
                    if (e->getEmbObj(f)) {
                        to_add.insert(e->getEmbObj(f));
                    }
                }
            }
            eqs.clear();
            eqs.insert(to_add.begin(),to_add.end());
            obj = obj->getEmbObj(f);
        }
        //Construct the final obj|field combinations.
        for (AliasObject *e : eqs) {
            if (dyn_cast<SequentialType>(e->targetType)) {
                std::set<long> eqfs;
                if (fid == -1) {
                    eqfs = e->getAllAvailableFields();
                }else {
                    eqfs.insert(fid);
                }
                eqfs.insert(-1);
                for (long t : eqfs) {
                    TypeField *tf = new TypeField(e->targetType,t,e);
                    res.insert(tf);
                }
            }else {
                TypeField *tf = new TypeField(e->targetType,fid,e);
                res.insert(tf);
            }
        }
        return 1;
    }

    //An improved version of "fetchPointsToObjects", we need to consider the type of each field.
    void AliasObject::fetchPointsToObjects(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects, InstLoc *currInst,
                                           bool get_eqv, bool create_obj) {
        /***
         * Get all objects pointed by field identified by srcfieldID
         *
         * i.e if a field does not point to any object.
         * Automatically generate an object and link it with srcFieldId
         */
        Instruction *targetInstr = currInst ? dyn_cast<Instruction>(currInst->inst) : nullptr;
        //What's the expected type of the fetched point-to object?
        //TODO: deal with other types of insts that can invoke "fetchPointsToObjects" in its handler.
        Type *expObjTy = getLoadedPointeeTy(targetInstr);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        logFieldAccess(srcfieldId, targetInstr, "FETCH");
#endif
        AliasObject *host = this->getNestedObj(srcfieldId,nullptr,currInst);
        if (!host) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::fetchPointsToObjects: failed to obtain the innermost nested field!\n";
#endif
            return;
        }
        if (host != this) {
            //This means what we need to fetch is in an embedded field obj at the original 
            //"srcfieldId", so the new field should be 0 in the emb obj.
            srcfieldId = 0;
        }
        //Reactivation check: if there has been a level 0 entry function change (e.g. we have finished analyzing ioctl_0 and started
        //ioctl_1) since last update to the field pto set, we then need a reset.
        if (currInst && currInst->hasCtx() && (*currInst->ctx)[0]) {
            host->resetPtos(srcfieldId,(*currInst->ctx)[0]);
        }
        //Handle the variable index here (i.e. srcfieldId == -1, or current pointee is an variable element in an array).
        if (get_eqv) {
            std::set<TypeField*> eqs;
            int ra = host->getEqvArrayElm(srcfieldId,eqs);
            if (eqs.size() > 1) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::fetchPointsToObjects: equivalent obj|field identified, cnt: " << eqs.size() << "\n";
#endif
                for (TypeField *e : eqs) {
                    if (e->fid != srcfieldId || e->priv != host) {
                        //This is an equivelant (but not identical) obj|field combo to the current pointee,
                        //we simply retrieve their pointee (but not create dummy pointee) and we will not
                        //recursively invoke "getEqvArrayElm" when doing so (which will trap into an
                        //infinite loop).
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "AliasObject::fetchPointsToObjects: ~~>[EQV OBJ] " << (const void*)(e->priv) << "|" << e->fid << "\n";
#endif
                        ((AliasObject*)e->priv)->fetchPointsToObjects(e->fid,dstObjects,currInst,false,false);
                    }
                    delete(e);
                }
            }
        }
        //Fetch the pto from the specified field...
        bool hasObjects = false;
        int dstobj_cnt = 0;
        if (host->pointsTo.find(srcfieldId) != host->pointsTo.end()) {
            //Decide which pto records are valid at current load site (i.e. the InstLoc "currInst").
            std::set<ObjectPointsTo*> livePtos;
            host->getLivePtos(srcfieldId,currInst,&livePtos);
            for (ObjectPointsTo *obj : livePtos) {
                if (obj->fieldId == srcfieldId && obj->targetObject) {
                    //We handle a special case here:
                    //Many malloc'ed HeapLocation object can be of the type i8*, while 
                    //only in the later code the pointer will be converted to a certain struct*,
                    //we choose to do this conversion here, specifically we need to:
                    //(1) change the object type to the "expObjTy",
                    //(2) setup the taint information properly.
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                    //dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " 
                    //<< (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                    //dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
#endif
                    if (obj->dstfieldId == 0 && obj->targetObject->isHeapLocation() && 
                        expObjTy && dyn_cast<CompositeType>(expObjTy) && InstructionUtils::isPrimitiveTy(obj->targetObject->targetType)) 
                    {
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                        dbgs() << "AliasObject::fetchPointsToObjects: Change type of the HeapLocation obj to: " 
                        << InstructionUtils::getTypeStr(expObjTy) << "\n"; 
#endif
                        //Change type.
                        obj->targetObject->reset(targetInstr,expObjTy,currInst);
                        //No need to call the "taintPointeeObj" again since we have already 
                        //done that when creating the old (before type reset) object, and the TaintFlags
                        //at that time will be propagated to new fields by "reset".
                        //host->taintPointeeObj(obj->targetObject,srcfieldId,currInst);
                    }
                    //Anyway here we're sure that we have the point-to record and we don't need to create dummy pointees any more,
                    //although the recorded pointee may have already been included in the "dstObjects" (e.g. load src pointer can have
                    //other target objects whose pointee set has already included this recorded pointee).
                    hasObjects = true;
                    auto p = std::make_pair(obj->dstfieldId, obj->targetObject);
                    if (std::find(dstObjects.begin(), dstObjects.end(), p) == dstObjects.end()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "-> " << InstructionUtils::getTypeStr(obj->targetObject->targetType) 
                        << " | " << obj->dstfieldId << ", obj: " << (const void*)(obj->targetObject);
                        dbgs() << ", is_taint_src: " << obj->targetObject->is_taint_src << ", Val: " 
                        << InstructionUtils::getValueStr(obj->targetObject->getValue()) << "\n";
#endif
                        dstObjects.insert(dstObjects.end(), p);
                        ++dstobj_cnt;
                    }
                }
            }
        }
        //If this is a const object, then no new field pto records are possible besides those set up at
        //the definition site, so just leave it as is.
        if (hasObjects || this->is_const || InstructionUtils::isAsanInst(targetInstr) || !create_obj) {
            return;
        }
        //Try to create a dummy object.
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::fetchPointsToObjects: No existing pto records for the field, try to create a dummy obj.\n";
#endif
        //since we cannot find any existing pto records, we need to create a "default" 
        //pto for current field who should exist at current level 0 function entry,
        //thus, we need to set the "siteInst" to the entry, instead of the "currInst".
        if (currInst && currInst->hasCtx() && (*currInst->ctx)[0]) {
            std::vector<Instruction*> *newCtx = new std::vector<Instruction*>(currInst->ctx->begin(),currInst->ctx->begin()+1);
            InstLoc *il = new InstLoc((*currInst->ctx)[0],newCtx);
            host->createFieldPointee(srcfieldId, dstObjects, currInst, il);
        } else {
            dbgs() << "!!! AliasObject::fetchPointsToObjects: currInst does not have a valid level 0 entry function!\n";
            host->createFieldPointee(srcfieldId, dstObjects, currInst);
        }
    }

    //Create a dummy field pto object.
    //"currInst" is the instruction where we actually need to use the field pto (but find it's not present), while "siteInst" is the location
    //we need to address the newly created field pto to (i.e. its "propagatingInst"). E.g.
    //func_entry: //site 0... if (..) {//site 1} else {//site 2}
    //Imagine "currInst" is in site 1, and site 2 also needs to use the same field pto, if in site 1 we don't have any pto records,
    //that means the pto is absent from the very beginning (e.g. function entry), so we actually need to create the pto in site 0 (i.e. siteInst)
    //so that site 2 later can also use it.
    void AliasObject::createFieldPointee(long fid, std::set<std::pair<long, AliasObject*>> &dstObjects, InstLoc *currInst, InstLoc *siteInst) {
        if (this->is_const) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): cannot create the field pointee since this obj is constant!\n";
#endif
            return;
        }
        if (siteInst == nullptr) {
            siteInst = currInst;
        }
        Instruction *targetInstr = currInst ? dyn_cast<Instruction>(currInst->inst) : nullptr;
        //What's the expected type of the fetched point-to object?
        //TODO: deal with other types of insts that can invoke "fetchPointsToObjects" in its handler.
        Type *expObjTy = getLoadedPointeeTy(targetInstr);
        //Get the type of the field for which we want to get the pointee.
        AliasObject *hostObj = this->getNestedObj(fid,nullptr,currInst);
        if (!hostObj) {
            return;
        }
        //It's possible that the embedded object already has the point-to record for field 0, if so, we just return the existing pto records.
        //If not, the "fetchPointsToObjects" will again invoke "createFieldPointee" to create the dummy object.
        if (hostObj != this) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): fetch the point-to from the embedded composite field.\n"; 
#endif
            return hostObj->fetchPointsToObjects(fid,dstObjects,currInst);
        }
        Type *ety = this->getFieldTy(fid);
        //Decide the type of the dummy object we want to create..
        Type *real_ty = nullptr;
        if (ety && ety->isPointerTy()) {
            real_ty = ety->getPointerElementType();
        }
        //In some cases we need to use the inferred obj type instead of the explicit field type..
        //(1) Either we cannot get the field type (e.g., no type info for the host obj), or the explicit field type is not a pointer.
        //(2) The explicit field pointee is of a primitive type (e.g., i8), while the inferred obj type provides a better guess reagrding
        //the type of the dummy obj to be created (e.g., a structure type).
        if ( (!real_ty) ||
             (InstructionUtils::isPrimitiveTy(real_ty) && expObjTy && !InstructionUtils::isPrimitiveTy(expObjTy))
           )
        {
            real_ty = expObjTy;
            //If the field type cannot match the expected pointee type (e.g. i8* can potentially point to anything), 
            //we will still use the "currInst", as in this case, the field may point to different things in different code paths...
            siteInst = currInst;
        }
        if (!real_ty) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): cannot decide the type of the dummy obj!\n"; 
#endif
            return;
        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::createFieldPointee(): about to create dummy obj of type: " << InstructionUtils::getTypeStr(real_ty) << "\n"; 
#endif
        //Create the dummy obj according to the dst type.
        if (real_ty->isFunctionTy()) {
            //This is a function pointer w/o point-to function, which can cause trobule later in resolving indirect function call.
            //We can try to do some smart resolving here by looking at the same-typed global constant objects.
#ifdef SMART_FUNC_PTR_RESOLVE
            std::set<Function*> candidateFuncs;
            hostObj->getPossibleMemberFunctions(fid, dyn_cast<FunctionType>(real_ty), targetInstr, candidateFuncs);
            for (Function *func : candidateFuncs) {
                GlobalObject *newObj = new GlobalObject(func);
                //Update points-to
                hostObj->addObjectToFieldPointsTo(fid,newObj,siteInst,false);
                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
            }
#endif
        }else if (validTyForOutsideObj(real_ty)) {
            OutsideObject *newObj = nullptr;
            if (DRCHECKER::enableXentryImpObjShare) {
                newObj = DRCHECKER::getSharedObjFromCache(real_ty);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::createFieldPointee(): Got Xentry shared obj: " << (const void*)newObj << "\n";
#endif
            }
            if (!newObj) {
                newObj = new OutsideObject(targetInstr,real_ty);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::createFieldPointee(): New outside obj created. Id: " << (const void*)newObj << "\n";
#endif
                //If enabled, try to add the newly created object to the cache for cross entry sharing.
                if (DRCHECKER::enableXentryImpObjShare) {
                    DRCHECKER::addToSharedObjCache(newObj);
                }
            }
            newObj->auto_generated = true;
            // get the taint for the field and add that taint to the newly created object
            hostObj->taintPointeeObj(newObj,fid,siteInst);
            //Handle some special cases like mutual point-to in linked list node "list_head".
            hostObj->handleSpecialFieldPointTo(newObj,fid,siteInst);
            //Update points-to
            hostObj->addObjectToFieldPointsTo(fid,newObj,siteInst,false);
            dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
        }else if (InstructionUtils::isPrimitiveTy(real_ty)) {
            //This is likely to be a mem buffer allocated by malloc() or similar functions, create a HeapLocation for it.
            AliasObject *newObj = nullptr;
            if (currInst && targetInstr) {
                newObj = new HeapLocation(*targetInstr, real_ty, currInst->ctx, nullptr, false);
            }else {
                newObj = new HeapLocation(real_ty, nullptr, false);
            }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): New heap obj created. Id: " << (const void*)newObj << "\n";
#endif
            newObj->auto_generated = true;
            hostObj->taintPointeeObj(newObj,fid,siteInst);
            //Update points-to
            hostObj->addObjectToFieldPointsTo(fid,newObj,siteInst,false);
            dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
        }else {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "fetchPointsToObjects(): the pointee type is invalid to create a dummy obj!\n";
#endif
        }
    }

    //The "fid" may be a composite field, if this is the case, we recursively get/create the embedded object at that offset,
    //until when we get an emb object whose type is "dty", or when there are no more emb objects (i.e. we have reached the innermost).
    //We will just return "this" if "fid" field is not composite.
    //NOTE: if "dty" is nullptr, we will just try to return the innermost emb object.
    AliasObject *AliasObject::getNestedObj(long fid, Type *dty, InstLoc *loc) {
        //There will be several cases here:
        //(1) The dst field is not composite, then we can return directly;
        //(2) The dst field is an embedded composite, we need to recursively extract 
        //the first field of it until we get a non-composite field or match the "dty";
        //(3) No type information for the dst element is available, return directly.
        AliasObject *hostObj = this;
        while (true) {
            int err = 0;
            Type *ety = hostObj->getFieldTy(fid,&err);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getNestedObj(): " << (const void*)hostObj << " | " << fid 
            << " : " << InstructionUtils::getTypeStr(ety) << "\n";
#endif
            if (!ety) {
                if (err == 2) {
                    //The requested field id is OOB, sth bad has happended.
                    dbgs() << "\n!!! AliasObject::getNestedObj(): field ID OOB!";
                    dbgs() << " Below is the info about current AliasObject...\n";
                    logFieldAccess(fid, nullptr, "ERROR");
                }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "\nAliasObject::getNestedObj(): Cannot decide the type of the dst element!\n";
#endif
                return nullptr;
            }
            if (!dyn_cast<CompositeType>(ety)) {
                return hostObj;
            }
            //If there is a non-null "dty" specified, we need to honor it as another return criteria.
            if (dty && InstructionUtils::same_types(dty,ety)) {
                return hostObj;
            }
            //NOTE: this is actually getOrCreateEmbObj()
            AliasObject *newObj = hostObj->createEmbObj(fid,nullptr,loc);
            if (!newObj) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "\n!!! AliasObject::getNestedObj(): Failed to create the emb obj.\n"; 
#endif
                return nullptr;
            }
            //assert(InstructionUtils::same_types(newObj->targetType,ety));
            hostObj = newObj;
            fid = 0;
        }
        return nullptr;
    }

    void AliasObject::updateFieldPointsTo(long srcfieldId, std::set<ObjectPointsTo*> *dstPointsTo, InstLoc *propagatingInstr, int is_weak) {
        /***
         * Add all objects in the provided pointsTo set to be pointed by the provided srcFieldID
         */
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "updateFieldPointsTo() for: " << InstructionUtils::getTypeStr(this->targetType) << " | " << srcfieldId;
        dbgs() << " Host Obj ID: " << (const void*)this << "\n";
#endif
        if (!dstPointsTo || !dstPointsTo->size()) {
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo(): Null dstPointsTo.\n";
#endif
            return;
        }
        AliasObject *host = this;
        if (host->targetType) {
            //If the "srcfieldId" is an embedded struct/array, we need to recursively update 
            //the fieldPointsTo in the embedded object instead of current host object.
            host = host->getNestedObj(srcfieldId,nullptr,propagatingInstr);
            if (!host) {
                //TODO: return or go ahead w/ "this"?
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "!!! updateFieldPointsTo(): Failed to get the nested field!\n";
#endif
                return;
            }
            if (host != this) {
                //This means what we need to update is an embedded obj at the original "srcfieldId", so the new field should be 0 in the emb obj.
                srcfieldId = 0;
            }
        }else {
            //Is this possible?
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "!!! updateFieldPointsTo(): null type info for this host obj!\n";
#endif
        }
        //Reactivation check: if there has been a level 0 entry function change (e.g. we have finished analyzing ioctl_0 and started
        //ioctl_1) since last update to the field pto set, we then need a reset.
        if (propagatingInstr && propagatingInstr->hasCtx() && (*propagatingInstr->ctx)[0]) {
            host->resetPtos(srcfieldId,(*propagatingInstr->ctx)[0]);
        }
        //Do the dirty work..
        host->updateFieldPointsTo_do(srcfieldId,dstPointsTo,propagatingInstr,is_weak);
    }

    //Do the real job of field pto update.
    void AliasObject::updateFieldPointsTo_do(long srcfieldId, std::set<ObjectPointsTo*> *dstPointsTo, InstLoc *propagatingInstr, int is_weak) {
        if (!dstPointsTo || !dstPointsTo->size()) {
            return;
        }
        //preprocessing: deduplication and unify "fieldId" and "propInst".
        std::set<ObjectPointsTo*> unique_pto;
        for (ObjectPointsTo *pto : *dstPointsTo) {
            if (!pto) {
                continue;
            }
            bool unique = true;
            for (ObjectPointsTo *t : unique_pto) {
                //NOTE: pto in "dstPointsTo" should all share the same "propagatingInstr", 
                //so we only need to care about their dst obj and field here.
                if (!t->pointsToSameObject(pto)) {
                    //Obviously different.
                    continue;
                }
                //if both pointed object and field are same and only "is_weak" is different, then just make "is_weak = false" (i.e. strong update)
                //for the existing pto record. 
                if (t->is_weak != pto->is_weak) {
                    t->is_weak = false;
                }
                //exclude this "pto" since it's duplicated
                unique = false;
                break;
            }
            if (unique) {
                ObjectPointsTo *npto = pto->makeCopy();
                //Before inserting the pto to the unique set, force set its "fieldId" and "propInst" to be correct.
                npto->fieldId = srcfieldId;
                npto->srcObject = this;
                npto->propagatingInst = propagatingInstr;
                //Insert
                unique_pto.insert(npto);
            }
        }
        if (!unique_pto.size()) {
            return;
        }
        //honor the "is_weak" arg here.
        if (is_weak >= 0) {
            for (ObjectPointsTo *pto : unique_pto) {
                pto->is_weak = !!is_weak;
            }
        }
        //Ok, now try to insert records in "unique_pto" to field points-to.
        //to_add: the pto records we should insert in the end (e.g. we may have duplicated records in existing field pto).
        //to_del: The existing pto records we should remove (e.g. overridden by new pto due to CFG relationship like post-dominator).
        //NOTE that instead of actually removing the overridden pto, we will mark it as "inactive" so the later load won't consider
        //it. The reason is that in the bug detection phase, we need to have a record of all ever existed pto relationship.
        std::set<ObjectPointsTo*> to_add, to_del;
        for (ObjectPointsTo *pto : unique_pto) {
            //Kill every existing pto we can, then decide whether we need to add current new pto.
            bool is_dup = false;
            for (ObjectPointsTo *e : this->pointsTo[srcfieldId]) {
                //The kill criteria: current pto is a strong update and it post-dominates an existing pto.
                //NOTE that we only need to kill those active pto records, since inactive ones are already killed.
                if (e->is_active && !pto->is_weak) {
                    //Ok, it's a strong update, decide whether it post-dominates "e", if so, delete "e" from existing pto set.
                    if (pto->propagatingInst && pto->propagatingInst->postDom(e->propagatingInst)) {
                        to_del.insert(e);
                        continue;
                    }
                }
                //Is "e" identical to "pto"?
                //No need to compare if we already decided it's duplicated.
                if (is_dup) {
                    continue;
                }
                //(1) Basic pto inf should be the same.
                if (!e->isIdenticalPointsTo(pto)) {
                    continue;
                }
                //(2) Update site should be the same.
                if (!e->propagatingInst != !pto->propagatingInst) {
                    continue;
                }
                if (e->propagatingInst && !e->propagatingInst->same(pto->propagatingInst)) {
                    continue;
                }
                //Ok, we can already say they are identical pto records and no need to insert "pto".
                is_dup = true;
                //But if their "is_weak" are different, we will set the existing pto to a strong update anyway.
                if (e->is_weak != pto->is_weak) {
                    e->is_weak = false;
                }
                //Re-activate the existing pto to the latest state of the freshly inserted pto (should be "active").
                if (e->is_active != pto->is_active) {
                    this->activateFieldPto(e,pto->is_active);
                }
            }
            if (!is_dup) {
                to_add.insert(pto);
            }else {
                //Note that each pto record in "unique_pto" is our newly created copy in this func, so we need to free the memory.
                delete(pto);
            }
        }
        //Do the actual deletion(de-activation) and insertion(activation).
        for (ObjectPointsTo *x : to_del) {
            this->activateFieldPto(x,false);
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): de-activate point-to: ";
            x->print(dbgs());
#endif
            /*
            this->pointsTo[srcfieldId].erase(x);
            //Don't forget to update the "pointsFrom" records of the affected objects.
            if (x->targetObject) {
                x->targetObject->erasePointsFrom(this,x);
            }
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): del point-to: ";
            x->print(dbgs());
#endif
            delete(x);
            */
        }
        for (ObjectPointsTo *x : to_add) {
            this->pointsTo[srcfieldId].insert(x);
            //Don't forget to update the "pointsFrom" records of the affected objects.
            if (x->targetObject) {
                x->targetObject->addPointsFrom(this,x);
            }
            this->activateFieldPto(x,true);
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): add and activate point-to: host: " << (const void*)this << ", ";
            x->print(dbgs());
#endif
        }
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "updateFieldPointsTo_do(): After updates: "; 
        this->logFieldPto(srcfieldId,dbgs());
#endif
    }

    void ObjectPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            OS << this->fieldId << " -> " << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->dstfieldId;
            OS << " Tgt Obj ID: " << (const void*)(this->targetObject) << "\n";
        }
    }

    OutsideObject* createOutsideObj(Type *ty) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "Type-based createOutsideObj(): " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        if (!validTyForOutsideObj(ty)) {
            return nullptr;
        }
        OutsideObject *newObj = new OutsideObject(nullptr, ty);
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "Type-based createOutsideObj(): New obj created: " << (const void*)newObj << "\n";
#endif
        //All outside objects are generated automatically.
        newObj->auto_generated = true;
        return newObj;
    }

    OutsideObject* createOutsideObj(Value *p, InstLoc *loc) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): ";
        if(p){
            dbgs() << InstructionUtils::getValueStr(p) << "  |  " << p->getName().str() + " : " << InstructionUtils::getTypeStr(p->getType());
        }
        dbgs() << "\n";
#endif
        //First do some sanity checks, we need to make sure that "p" is a pointer of a composite type.
        if (!(p && p->getType()->isPointerTy() && validTyForOutsideObj(p->getType()->getPointerElementType()))) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): It's not a pointer to the composite type! Cannot create an outside object!\n";
#endif
            return nullptr;
        }
        //Don't create OutsideObject for null ptr.
        if (p->getName().str().empty() && !dyn_cast<Instruction>(p)){
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): Null value name! Cannot create an outside object!\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): Try to create new outside object.\n";
#endif
        //Create a new outside object.
        //OutsideObject *newObj = new OutsideObject(p, p->getType()->getContainedType(0));
        OutsideObject *newObj = new OutsideObject(p, p->getType()->getPointerElementType());
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): New obj created: " << (const void*)newObj << "\n";
#endif
        //All outside objects are generated automatically.
        newObj->auto_generated = true;
        //Set up point-to records inside the AliasObject.
        newObj->addPointerPointsTo(p,loc);
        return newObj;
    }

    AliasObject *AliasObject::createEmbObj(long fid, Value *v, InstLoc *loc) {
        AliasObject *newObj = nullptr;
        if (!this->targetType) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasObject::createEmbObj(): !this->targetType\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "AliasObject::createEmbObj(): host type: " << InstructionUtils::getTypeStr(this->targetType) 
        << " | " << fid << " ID: " << (const void*)(this) << "\n";
#endif
        Type *ety = this->getFieldTy(fid);
        if (!ety || !dyn_cast<CompositeType>(ety)) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasObject::createEmbObj(): invalid field type for an embedded object!\n";
#endif
            return nullptr;
        }
        Type *expectedPointeeTy = nullptr;
        if (v && v->getType() && v->getType()->isPointerTy()) {
            expectedPointeeTy = v->getType()->getPointerElementType();
        }
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "AliasObject::createEmbObj(): ety: " << InstructionUtils::getTypeStr(ety) 
        << " expectedPointeeTy: " << InstructionUtils::getTypeStr(expectedPointeeTy) << "\n";
#endif
        if (v && !InstructionUtils::same_types(ety,expectedPointeeTy)) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasObject::createEmbObj(): ety and expectedPointeeTy are different...\n";
#endif
            return nullptr;
        }
        if (this->embObjs.find(fid) != this->embObjs.end()) {
            //We have created that embedded object previously.
            newObj = this->embObjs[fid];
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasObject::createEmbObj(): find the previosuly created embed object: " << (const void*)newObj << "\n";
#endif
        }
        if (!newObj || !InstructionUtils::same_types(newObj->targetType,ety)) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasObject::createEmbObj(): try to create a new embed object because ";
            if (!newObj) {
                dbgs() << "there is no emb obj in cache...\n";
            }else{
                dbgs() << "the emb obj in cache has a different type than expected: " 
                << InstructionUtils::getTypeStr(newObj->targetType) << "\n";
            }
#endif
            if (newObj) {
                //Erase the parent record of the existing emb obj.
                if (newObj->parent == this) {
#ifdef DEBUG_CREATE_EMB_OBJ
                    dbgs() << "AliasObject::createEmbObj(): try to erase the existing emb obj's\
                    parent record since its parent is also this hostObj.\n";
#endif
                    newObj->parent = nullptr;
                    newObj->parent_field = 0;
                }
            }
            //Need to create a new AliasObject for the embedded struct.
            if (v) {
                newObj = DRCHECKER::createOutsideObj(v,loc);
            }else {
                newObj = DRCHECKER::createOutsideObj(ety);
            }
            if (newObj) {
#ifdef DEBUG_CREATE_EMB_OBJ
                dbgs() << "AliasObject::createEmbObj(): the embedded obj created: "  
                << (const void*)this << " | " << fid << " --> " << (const void*)newObj << "\n"; 
#endif
                //NOTE: the "auto_generated" property should be same between host and emb objects, but "createOutsideObj" by default
                //set it to true.
                newObj->auto_generated = this->auto_generated;

                //Properly taint it.
                //First if the host object is a taint source, then the emb obj is so too, 
                //we also need to set up the inherent taint flags for it,
                //however, for the taint instruction trace in the flag we will just inherite 
                //from the host object instead of using the current one,
                //because in theory, this emb object was immediately avaiable when creating the host object.
                if (this->is_taint_src) {
#ifdef DEBUG_CREATE_EMB_OBJ
                    dbgs() << "AliasObject::createEmbObj(): set the emb obj as a taint source since its host obj is so, is_taint_src: " 
                    << this->is_taint_src << "\n"; 
#endif
                    //NOTE: since our goal here is to extract the "loc" of the inherent taint 
                    //flag for the host obj, not to get the current live taint flags,
                    //we do not use the "getTf()" interface.
                    TaintFlag *itf = this->all_contents_taint_flags.getInherentTf();
                    if (itf && itf->targetInstr) {
                        newObj->setAsTaintSrc(itf->targetInstr,(this->is_taint_src>0));
                    }else {
#ifdef DEBUG_CREATE_EMB_OBJ
                        dbgs() << "!!! AliasObject::createEmbObj(): cannot find the InstLoc in host inherent taint flag!\n"; 
#endif
                        newObj->setAsTaintSrc(loc,(this->is_taint_src>0));
                    }
                }
                //If fid is "-1", we're currently working on an emb object representing a variable field, when later we need
                //to get its TFs, we will automatically try to get all TFs from all available fields, so no need to propagate
                //the TFs to it at this point.
                if (fid >= 0) {
                    //Now propagate non-inherent flags in the host object, no need to 
                    //propagate inherent ones since emb obj is a part of the host. 
                    //NOTE: these propagated TFs may override the previously set-up inherent TFs 
                    //("setAsTaintSrc"), which is just the correct and expected bahavior.
                    std::set<TaintFlag*> tfs;
                    this->getFieldTaintInfo(fid,tfs,loc);
#ifdef DEBUG_CREATE_EMB_OBJ
                    dbgs() << "AliasObject::createEmbObj(): try to taint the emb obj (all fields), #TaintFlag: " << tfs.size() << "\n";
#endif
                    for (TaintFlag *tf : tfs) {
                        //NOTE: we don't need to add current "loc" into the taint trace since this emb obj was tainted as early as the field.
                        //And no worry that "newObj" will be tainted by an inherent TF not 
                        //belonging to itself, since we only propagate non-inherent ones here.
                        if (tf && !tf->is_inherent) {
                            //NOTE: "is_weak" is inherited.
                            newObj->taintAllFields(tf);
                        }
                    }
                }
                //Record it in the "embObjs".
                this->setEmbObj(fid,newObj);
            }else {
#ifdef DEBUG_CREATE_EMB_OBJ
                dbgs() << "AliasObject::createEmbObj(): Failed to create the outside object!\n";
#endif
            }
        }
        return newObj;
    }

    AliasObject *AliasObject::createHostObj(Type *hostTy, long field, InstLoc *loc) {
        if (!hostTy || !dyn_cast<CompositeType>(hostTy)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "AliasObject::createHostObj(): !hostTy || !dyn_cast<CompositeType>(hostTy)\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "AliasObject::createHostObj(): curr emb ty: " << InstructionUtils::getTypeStr(this->targetType) << "\n";
        dbgs() << "AliasObject::createHostObj(): hostObj ty: " << InstructionUtils::getTypeStr(hostTy) << " | " << field << "\n";
#endif
        //Have we already created this parent object?
        if (this->parent) {
            if (InstructionUtils::same_types(this->parent->targetType,hostTy) && this->parent_field == field) {
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "AliasObject::createHostObj(): we have created this parent object before: " << (const void*)(this->parent) << "\n";
#endif
                return this->parent;
            }else {
                //NOTE: we should honor the original parent object, since it's static 
                //analysis and we can have multiple pointees for a same pointer
                //and they may have multiple different parent objects, here we're 
                //possibly trying yo create a parent object for a wrong pointee, we should just skip.
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "!!! AliasObject::createHostObj(): found a previously created parent object but w/ different field or type!\n";
                dbgs() << "!!! AliasObject::createHostObj(): previous parent: " 
                << InstructionUtils::getTypeStr(this->parent->targetType) << " | " << this->parent_field 
                << ", id: " << (const void*)this->parent << "\n";
#endif
                return nullptr;
                /*
                if (this->parent->embObjs.find(this->parent_field) != this->parent->embObjs.end()) {
                    this->parent->embObjs[this->parent_field] = nullptr;
                }
                this->parent = nullptr;
                this->parent_field = 0;
                */
            }
        }
        if (!InstructionUtils::isIndexValid(hostTy,field)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "AliasObject::createHostObj(): field OOB!\n";
#endif
            return nullptr;
        }
        if (!InstructionUtils::same_types(InstructionUtils::getTypeAtIndex(hostTy,field),this->targetType)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "AliasObject::createHostObj(): field type doesn't match the host!\n";
#endif
            return nullptr;
        }
        AliasObject *hobj = DRCHECKER::createOutsideObj(hostTy);
        if (hobj) {
            //NOTE: the "auto_generated" property should be same between host and emb objects, but "createOutsideObj" by default
            //set it to true.
            hobj->auto_generated = this->auto_generated;
            //The taint logic here is: if the emb object has inherent taint flags, 
            //then it's likely that its host object should also be treated as
            //a taint source, otherwise we just keep the newly available fields in the host untainted.
            //NOTE: the logic here is similar to that in "createEmbObject". 
            InstLoc *eloc = nullptr;
            if (this->is_taint_src) {
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "AliasObject::createHostObj(): set the host obj as a taint source since its one emb is, is_taint_src: " 
                << this->is_taint_src << "\n"; 
#endif
                TaintFlag *itf = this->all_contents_taint_flags.getInherentTf();
                if (itf && itf->targetInstr) {
                    //TODO: whether to avoid setting the inherent TF again for "this"...
                    hobj->setAsTaintSrc(itf->targetInstr,(this->is_taint_src>0));
                }else {
#ifdef DEBUG_CREATE_HOST_OBJ
                    dbgs() << "!!! AliasObject::createHostObj(): cannot find the InstLoc in emb inherent taint flag!\n"; 
#endif
                    hobj->setAsTaintSrc(loc,(this->is_taint_src>0));
                }
            }
        }else {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "AliasObject::createHostObj(): fail to create the host obj!\n";
#endif
            return nullptr;
        }
        //Setup embed relationship.
        hobj->setEmbObj(field,this);
        return hobj;
    }

    bool matchFieldName(Module *mod, Type *ty, std::string& n, FieldDesc *fd) {
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): try to match the field name: " << n << " of type: " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        if (!ty || !fd || n.size() == 0) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): (False) !ty || !fd || n.size() == 0\n";
#endif
            return false;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): FieldDesc: ";
        fd->print_path(dbgs());
#endif
        //Be sure that "ty" exists in the "fd".
        if (fd->findTy(ty) < 0) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): (False) no target ty resides at this fd...\n";
#endif
            return false;
        }
        if (fd->host_tys.size() != fd->fid.size()) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "!!! matchFieldName(): (False) #host_tys and #fid mismatch in the fd...\n";
#endif
            return false;
        }
        int i = fd->findHostTy(ty);
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): fd->findHostTy(ty): " << i << " #host_tys: " << fd->host_tys.size() << "\n";
#endif
        if (i < ((int)fd->host_tys.size()) - 1) {
            //NOTE that this can also handle the case wherer "i = -1", which means 
            //"ty" is the innermost field and its direct host object is host_tys[0].
            std::string fn = InstructionUtils::getStFieldName(mod,dyn_cast<StructType>(fd->host_tys[i+1]),fd->fid[i+1]);
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): got the field name: " << fn << "\n";
#endif
            return (fn.size() > 0 && n.find(fn) != std::string::npos);
        }else {
            //It's not a field in a host struct, it's the host struct itself and we don't know its name..
            return false;
        }
        return false;
    }

    int matchFieldsInDesc(Module *mod, Type *ty0, std::string& n0, Type *ty1, std::string& n1, 
                          int bitoff, std::vector<FieldDesc*> *fds, std::vector<unsigned> *res) {
        if (!ty0 || !ty1 || !fds || !res) {
            return 0;
        }
        std::vector<unsigned> type_res;
        std::vector<unsigned> prio_res;
        for (int i = 0; i < fds->size(); ++i) {
            FieldDesc *fd = (*fds)[i];
            if (!fd || fd->findTy(ty0) < 0) 
                continue;
            int dstoff = fd->bitoff + bitoff;
            int step = (bitoff > 0 ? 1 : -1);
            for (int j = i; j >= 0 && j < fds->size(); j+=step) {
                if ((*fds)[j]->bitoff == dstoff && (*fds)[j]->findTy(ty1) >= 0) {
                    //Ok, now we're sure that we get a type match for the two fields in the struct, 
                    //we'll see whether the field names are also matched.
                    //If so, put the matching field id in a special priority queue.
#ifdef DEBUG_CREATE_HOST_OBJ
                    /*
                    dbgs() << "matchFieldsInDesc(): Got a match in current tydesc, n0: " << n0 << ", n1: " << n1 << " ======\n";
                    dbgs() << "Ty0: ";
                    fd->print_path(dbgs());
                    dbgs() << "Ty1: ";
                    (*fds)[j]->print_path(dbgs());
                    */
#endif
                    bool nm_match = false;
                    if (n0.size() > 0 && n1.size() > 0) {
                        nm_match = (matchFieldName(mod,ty0,n0,fd) && matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }else if (n0.size() > 0 || n1.size() > 0) {
                        nm_match = (n0.size() > 0 ? matchFieldName(mod,ty0,n0,fd) : matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }
#ifdef DEBUG_CREATE_HOST_OBJ
                    dbgs() << "matchFieldsInDesc(): nm_match: " << nm_match << "\n";
#endif
                    if (nm_match) {
                        prio_res.push_back(i);
                        prio_res.push_back(j);
                    }
                    type_res.push_back(i);
                    type_res.push_back(j);
                    break;
                }
                if ((step > 0) != ((*fds)[j]->bitoff < dstoff)) {
                    break;
                }
            }
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        if (type_res.size() > 0) {
            dbgs() << "matchFieldsInDesc(): #prio_res: " << prio_res.size() << ", #type_res: " << type_res.size() << "\n";
        }
#endif
        if (prio_res.size() > 0) {
            *res = prio_res;
            return 2;
        }else if (type_res.size() > 0) {
            *res = type_res;
            return 1;
        }
        return 0;
    }

    void sortCandStruct(std::vector<CandStructInf*> *cands, std::set<Instruction*> *insts) {
        if (!cands || !cands->size()) {
            return;
        }
        std::set<Function*> funcs;
        if (insts) {
            for (Instruction *i : *insts) {
                //in case some insts are not inserted into any functions...
                if (i->getParent()) {
                    funcs.insert(i->getFunction());
                }
            }
        }
        for (CandStructInf *c : *cands) {
            std::vector<FieldDesc*> *fds = c->fds;
            FieldDesc *fd0 = (*fds)[c->ind[0]];
            FieldDesc *fd1 = (*fds)[c->ind[1]];
            if (!fd0->host_tys.size()) {
                dbgs() << "!!! sortCandStruct(): No host type inf!\n";
                continue;
            }
            Type *hty = fd0->host_tys[fd0->host_tys.size()-1];
            //If the host type is referred in the target function, then we will have a high confidence.
            for (Function *func : funcs) {
                if (InstructionUtils::isTyUsedByFunc(hty,func)) {
                    c->score += 1000.;
                }
            }
            //TODO: is this reasonable? Is the field name match more important than "used by the function"?
            if (c->field_name_matched) {
                c->score += 1000;
            }
            //TODO: if the type name is similar to the function name, then we will give it a high score.
            //
            /*
            //Observation: it's likely that the #field of ty1 is 0 when "bitoff" is negative. 
            if (c->ind[1] == 0) {
                c->score += 500.;
            }
            */
            //Give a preference to the smaller container..
            c->score -= ((float)(*fds)[fds->size()-1]->bitoff)/100.;
        }
        std::sort(cands->begin(),cands->end(),[](CandStructInf *c0, CandStructInf *c1){
            return (c0->score - c1->score > 0);
        });
        return;
    }

    std::vector<CandStructInf*> *getStructFrom2Fields(DataLayout *dl, Type *ty0, std::string& n0, 
                                                      Type *ty1, std::string& n1, long bitoff, Module *mod) {
        if (!dl || !mod || !ty0 || !ty1) {
            return nullptr;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "getStructFrom2Fields(): Trying to identify a struct that can match the distanced fields.\n";
#endif
        std::vector<StructType*> tys = mod->getIdentifiedStructTypes();
        std::vector<CandStructInf*> *cands = new std::vector<CandStructInf*>();
        //"prio_cands" records the candidate structs whose field names also match the provided two fields.
        std::vector<CandStructInf*> *prio_cands = new std::vector<CandStructInf*>();
        for (StructType *t : tys) {
            std::vector<FieldDesc*> *tydesc = InstructionUtils::getCompTyDesc(dl,t);
            if (!tydesc) {
                continue;
            }
            //Ok, try to match to given fields w/ a specified distance.
            std::vector<unsigned> res;
            int rc = matchFieldsInDesc(mod,ty0,n0,ty1,n1,bitoff,tydesc,&res);
            if (rc == 0) {
                continue;
            }
#ifdef DEBUG_CREATE_HOST_OBJ
            /*
            dbgs() << "getStructTysFromFieldDistance(): got a match: " << InstructionUtils::getTypeStr(t) << "\n"; 
            for (FieldDesc *fd : *tydesc) {
                fd->print(dbgs());
            }
            */
#endif
            //Ok get a match, record it.
            for (int i = 0; i < res.size(); i += 2) {
                CandStructInf *inf = new CandStructInf();
                inf->fds = tydesc;
                inf->ind.push_back(res[i]);
                inf->ind.push_back(res[i+1]);
                cands->push_back(inf);
                if (rc == 2) {
                    inf->field_name_matched = true;
                    prio_cands->push_back(inf);
                }
            }
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "getStructFrom2Fields(): #cands: " << cands->size() << " #prio_cands: " << prio_cands->size() << "\n";
#endif
        if (prio_cands->size() > 0) {
            //Free non-prio candidates..
            for (CandStructInf *c : *cands) {
                if (std::find(prio_cands->begin(),prio_cands->end(),c) == prio_cands->end()) {
                    delete(c);
                }
            }
            delete(cands);
            return prio_cands;
        }
        delete(prio_cands);
        return cands;
    }

    //A typical and common scenario in which we need to call this is that in a "GEP i8 *ptr, index" IR the "ptr" points to
    //a certain object but is converted to i8*. then the "index" calculates a pointer pointing outside this object...
    //To find the host obj, what we want to do is to iterate over all struct types in the current module, then find the correct type(s)
    //that has properly distanced field types that matches both the base "ptr" and the pointer type produced by the "GEP" (we need to
    //figure out the true pointer type from the subsequent cast IRs).
    //ARG: "v" points to the location w/ bit offset "bitoff" in the host type "ty".
    //NOTE: this function is time-consuming!
    CandStructInf *inferContainerTy(Module *m, Value *v, Type *ty, long bitoff) {
#ifdef DEBUG_INFER_CONTAINER
        dbgs() << "inferContainerTy(): v: " << InstructionUtils::getValueStr(v) << " ty: " 
        << InstructionUtils::getTypeStr(ty) << " bitoff: " << bitoff << "\n";
#endif
        //We record all failure cases (i.e. cannot find any container objects) in this cache to accelerate future processing,
        //note that we don't set up a 'success' cache because as soon as we find a container, the parent object will be created, thus later
        //bit2Field() has no need to invoke this function again, but failed cases may be queryed again and again.
        static std::map<Value*,std::map<Type*,std::set<long>>> fail_cache;
        if (!m || !v || !ty) {
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): !m || !v || !ty\n";
#endif
            return nullptr;
        }
        if (fail_cache.find(v) != fail_cache.end() && fail_cache[v].find(ty) != fail_cache[v].end() &&
            fail_cache[v][ty].find(bitoff) != fail_cache[v][ty].end()) {
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "This is a failed case!\n";
#endif
            return nullptr;
        }
        DataLayout dl = m->getDataLayout();
        //NOTE: use store size here since the host object is on its own (not stored consecutively w/ other same objects).
        long tysz = dl.getTypeStoreSizeInBits(ty);
        //Analyze every OOB GEP w/ the same base pointer "v".
        std::vector<CandStructInf*> cands;
        bool init = true;
        std::set<Instruction*> insts;
        for (User *u : v->users()) {
            if (dyn_cast<Instruction>(u)) {
                if (dyn_cast<Instruction>(u)->getParent()) {
                    insts.insert(dyn_cast<Instruction>(u));
                }else {
                    //In case this is an instruction artificially created by us.
                    continue;
                }
            }
            GEPOperator *gep = dyn_cast<GEPOperator>(u);
            //Make sure it's a GEP w/ "v" as the base pointer.
            if (!gep || gep->getPointerOperand() != v) {
                continue;
            }
            int rc;
            long delta = InstructionUtils::calcGEPTotalOffsetInBits(gep,&dl,&rc);
            if (rc) {
                //Cannot calculate the overall offset of this gep.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): cannot calculate the overall offset for GEP: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
                continue;
            }
            long resOff = bitoff + delta;
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): found one GEP using the same srcPointer: " << InstructionUtils::getValueStr(gep) << "\n";
            dbgs() << "inferContainerTy(): delta: " << delta << " resOff: " << resOff << " current host type size: " << tysz << "\n";
#endif
            if (resOff >= 0 && resOff < tysz) {
                //This means current GEP will not index outside the original object, so useless for container inference.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): skip since this GEP doesn't access the fields outside current host (i.e. in the container).\n";
#endif
                continue;
            }
            //Try to obtain the real type of this GEP inst by looking at its users, specifically the "cast" and "load" inst.
            Type *ty1 = nullptr;
            std::set<Type*> candTy1;
            for (User *u1 : gep->users()) {
                if (dyn_cast<Instruction>(u1)) {
                    insts.insert(dyn_cast<Instruction>(u1));
                    if (InstructionUtils::isAsanInst(dyn_cast<Instruction>(u1))) {
                        continue;
                    }
                }
                Type *dty = nullptr;
                if (dyn_cast<CastInst>(u1)) {
                    dty = dyn_cast<CastInst>(u1)->getDestTy();
                }else if (dyn_cast<LoadInst>(u1)) {
                    dty = dyn_cast<LoadInst>(u1)->getPointerOperandType();
                }
                if (dty && dty->isPointerTy()) {
                    candTy1.insert(dty->getPointerElementType());
                }
            }
            //Do a simple filtering if there are multiple candidate ty1 types.
            for (Type *t : candTy1) {
                ty1 = t;
                if (dyn_cast<CompositeType>(ty1) || (ty1->isPointerTy() && !ty1->getPointerElementType()->isIntegerTy())) {
                    break;
                }
            }
            if (!ty1) {
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): cannot find the ty1.\n";
#endif
                continue;
            }
            std::string n0 = "";
            std::string n1 = (gep->hasName() ? gep->getName().str() : "");
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): ty1: " << InstructionUtils::getTypeStr(ty1) << " n1: " << n1 << "\n";
#endif
            //Ok, now we can get some candidate container types that contain both "ty" and "ty1" with a distance of "resOff".
            std::vector<CandStructInf*> *c = DRCHECKER::getStructFrom2Fields(&dl,ty,n0,ty1,n1,resOff,m);
            //We only reserve those container types that are valid for all GEPs (i.e. intersection).
            if (!c || c->size() == 0) {
                //TODO: directly return nullptr or continue? In theory we should return since it's an intersection but that will
                //immediately cause us to have no container types identified... which is also less likely.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): warning: we identified no container types for this ty-ty1-resOff combination...\n";
#endif
                if (c) delete(c);
                continue;
            }
            if (init) {
                cands = *c;
                init = false;
            }else {
                std::vector<CandStructInf*> tmp_copy = cands;
                cands.clear();
                for (CandStructInf *e : *c) {
                    if (!e) {
                        continue;
                    }
                    if (std::find_if(tmp_copy.begin(),tmp_copy.end(),[e](const CandStructInf *cand) {
                        //NOTE: ind[1] may be different since we consider multiple different GEPs (using the same base ty0) as ty1.
                        return (e->fds == cand->fds && e->ind[0] == cand->ind[0]);
                    }) != tmp_copy.end()) {
                        cands.push_back(e);
                    }else {
                        delete(e);
                    }
                }
                //New batch of "cands" loaded, free the old batch..
                for (CandStructInf *e : tmp_copy) {
                    if (e) delete(e);
                }
            }
            delete(c);
            //We're sure that there must be a correct container type existing in the module, 
            //so as long as we have the only available candidate, we should stop and just use it.
            if (cands.size() <= 1) {
                break;
            }
        }
#ifdef DEBUG_INFER_CONTAINER
        dbgs() << "inferContainerTy(): all GEPs analyzed, #cand containers: " << cands.size() << "\n";
#endif
        if (cands.size() == 0) {
            //Add to the fail cache.
            fail_cache[v][ty].insert(bitoff);
            return nullptr;
        }
        //Ok now we have got a candidate container list.
        //We need to select a best candidate to return...
        sortCandStruct(&cands,&insts);
#ifdef DEBUG_INFER_CONTAINER
        /*
        for (int i = 0; i < cands.size(); ++i) {
            Type *t = (*cands[i]->fds)[0]->getOutermostTy();
            dbgs() << "inferContainerTy(): CAND " << i << " SCORE " << cands[i]->score << " : " << InstructionUtils::getTypeStr(t) << "\n"; 
            for (FieldDesc *fd : *cands[i]->fds) {
                fd->print(dbgs());
            }
        }
        */
        for (int i = 0; i < cands.size(); ++i) {
            Type *t = (*cands[i]->fds)[0]->getOutermostTy();
            dbgs() << "inferContainerTy(): ==============CAND " << i << " SCORE " << cands[i]->score 
            << " : " << InstructionUtils::getTypeStr(t) << "\n"; 
            dbgs() << "Ty0: ";
            (*cands[i]->fds)[cands[i]->ind[0]]->print_path(dbgs());
        }
#endif
        //Return the hisghest ranked candidate.
        for (int i = 1; i < cands.size(); ++i) {
            delete(cands[i]);
        }
        //We need to modify the CandStructInf.ind[0] to make it point to exactly the location of "bitoff" inside "ty",
        //note that currently ind[0] is the location of "ty" in the container.
        int idst = InstructionUtils::locateBitsoffInTyDesc(cands[0]->fds,(*cands[0]->fds)[cands[0]->ind[0]]->bitoff + bitoff);
        if (idst < 0 || idst >= cands[0]->fds->size()) {
            //Add to the fail cache.
            fail_cache[v][ty].insert(bitoff);
            return nullptr;
        }
        cands[0]->ind[0] = idst;
        return cands[0];
    }

    bool isSharedTy(Type *ty) {
        if (!ty) {
            return false;
        }
        if (DRCHECKER::sharedObjTyStrs.empty()) {
            //No limitations specified.
            return true;
        }
        //Only a limited set of obj types will be shared.
        StructType *stTy = dyn_cast<StructType>(ty);
        if (!stTy || !stTy->hasName()) {
            return false;
        }
        std::string n = stTy->getName().str();
        n = InstructionUtils::trim_struct_name(n);
        return (DRCHECKER::sharedObjTyStrs.find(n) != DRCHECKER::sharedObjTyStrs.end());
    }

    int addToSharedObjCache(OutsideObject *obj) {
        if (!obj || !DRCHECKER::currEntryFunc ||!obj->targetType) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "addToSharedObjCache(): for the obj: (!obj || !DRCHECKER::currEntryFunc ||!obj->targetType)\n";
#endif
            return 0;
        }
        //Check whether there is a whitelist for the shared obj types.
        if (!isSharedTy(obj->targetType)) {
            return 0;
        }
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "addToSharedObjCache(): for the obj: " << (const void*)obj << " currEntryFunc: " 
        << DRCHECKER::currEntryFunc->getName().str() << "\n";
#endif
        DRCHECKER::sharedObjCache[obj->targetType][DRCHECKER::currEntryFunc].insert(obj);
        return 1;
    }

    //Ok, now get the "->private" pointee type of the file struct as pointed to by "p".
    //(1) get all GEPs that use the "p" as the base pointer and make the indices (0,16).
    //(2) decide the type of the resulting GEP pointer, by looking at the GEP's users (e.g. a cast inst).
    void probeFilePrivTy(Value *p, std::set<Type*> &retSet) {
        if (!p) {
            return;
        }
        for (User *u : p->users()) {
            GEPOperator *gep = dyn_cast<GEPOperator>(u);
            //Make sure it has a single index.
            if (!gep || gep->getNumOperands() != 3 || gep->getPointerOperand() != p) {
                continue;
            }
            //Get the 2nd constant index value.
            ConstantInt *CI = dyn_cast<ConstantInt>(gep->getOperand(2));
            if (!CI) {
                continue;
            }
            long index = CI->getSExtValue();
            //"16" is a hardcoded index of the ".private" in the file struct.
            if (index != 16) {
                continue;
            }
            //Infer the type from the cast inst of this gep.
            for (User *e : gep->users()) {
                CastInst *cinst = dyn_cast<CastInst>(e);
                if (!cinst || cinst->getOperand(0) != dyn_cast<Value>(gep)) {
                    continue;
                }
                Type *t = cinst->getDestTy();
                //NOTE: the gep itself is a pointer to the file->private, where ->private is 
                //also a pointer, so the cast result should be a pointer of a pointer.
                if (t && t->isPointerTy()) {
                    t = t->getPointerElementType();
                    if (t->isPointerTy()) {
                        retSet.insert(t->getPointerElementType());
                    }
                }
            }
        }
        return;
    }

    //Whether this object can be potentially pointed to by "p".
    int AliasObject::maybeAPointee(Value *p) {
        if (!p || !p->getType()) {
            return -1;
        }
        Type *vt = p->getType();
        if (!vt->isPointerTy()) {
            //Since it's not a pointer, we cannot get the type info of the pointee, so conservatively let's return 0.
            return 0;
        }
        Type *pointeeTy = vt->getPointerElementType();
        //i8* or void* can in theory point to anything.
        if (InstructionUtils::isPrimitiveTy(pointeeTy)) {
            return 0;
        }
        //TODO: For the composite type in theory we need to inspect its type desc, 
        //but for now we assume that "p" can point to any composite type,
        //except for some special cases that we will deal with as below.
        //***Special processing for "struct.file" type: match its "->private" pointee object type.
        std::set<Type*> fty0;
        if (pointeeTy && InstructionUtils::same_types(pointeeTy,this->targetType) && dyn_cast<StructType>(pointeeTy)) {
            StructType *stTy = dyn_cast<StructType>(pointeeTy);
            if (stTy->hasName() && stTy->getName().str() == "struct.file") {
                //Ok, it's a file struct, now get the pointee type of "->private" of this AliasObject.
                this->getFieldPointeeTy(16, fty0);
                if (fty0.empty()) {
                    return 0;
                }
            }
        }
        std::set<Type*> fty1;
        probeFilePrivTy(p,fty1);
        for (Type *t0 : fty0) {
            for (Type *t1 : fty1) {
                if (InstructionUtils::same_types(t0,t1)) {
                    return 1;
                }
            }
        }
        return 0;
    }

    OutsideObject *getSharedObjFromCache(Type *ty) {
        if (!ty || !DRCHECKER::currEntryFunc || !isSharedTy(ty)) {
            return nullptr;
        }
        for (auto &c : DRCHECKER::sharedObjCache) {
            if (!InstructionUtils::same_types(ty,c.first)) {
                continue;
            }
            for (auto &e : c.second) {
                if (e.first != DRCHECKER::currEntryFunc) {
                    for (OutsideObject *o : e.second) {
                        if (o) {
                            return o;
                        }
                    }
                }else {
                    //This means there is already a same-typed object created previously when analyzing current entry function.
                    //TODO: should we re-use this previous obj or create a new one?
#ifdef DEBUG_SHARED_OBJ_CACHE
                    dbgs() << "getSharedObjFromCache(): Found a previously created obj by the current entry func.\n";
#endif
                }
            }
        }
        return nullptr;
    }

    OutsideObject *getSharedObjFromCache(Value *v) {
        if (!v || !v->getType() || !v->getType()->isPointerTy()) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): the passed-in value is not a pointer!\n";
#endif
            return nullptr;
        }
        //TODO: consider to obtain the type by inference, instead of the direct "getType()".
        Type *ty = v->getType()->getPointerElementType();
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "getSharedObjFromCache(): At the entrance. Type: " << InstructionUtils::getTypeStr(ty) 
        << " currEntryFunc: " << DRCHECKER::currEntryFunc->getName().str() << "\n";
#endif
        if (!ty || !DRCHECKER::currEntryFunc) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): (!ty || !DRCHECKER::currEntryFunc)\n";
#endif
            return nullptr;
        }
        if (!isSharedTy(ty)) {
            //This type is not intended to be shared.
            return nullptr;
        }
        OutsideObject *ro = nullptr;
        int max_s = -99;
        for (auto &c : DRCHECKER::sharedObjCache) {
            if (!InstructionUtils::same_types(ty,c.first)) {
                continue;
            }
            for (auto &e : c.second) {
                if (e.first != DRCHECKER::currEntryFunc) {
                    for (OutsideObject *o : e.second) {
#ifdef DEBUG_SHARED_OBJ_CACHE
                        dbgs() << "getSharedObjFromCache(): Cand Obj: " << (const void*)o << " srcEntryFunc: " 
                        << e.first->getName().str() << "\n";
#endif
                        int t = o->maybeAPointee(v);
#ifdef DEBUG_SHARED_OBJ_CACHE
                        dbgs() << "Possibility Score: " << t << "\n";
#endif
                        if (t > max_s) {
                            max_s = t;
                            ro = o;
                        }
                    }
                }else {
                    //This means there is already a same-typed object created previously when analyzing current entry function.
                    //TODO: should we re-use this previous obj or create a new one?
#ifdef DEBUG_SHARED_OBJ_CACHE
                    dbgs() << "getSharedObjFromCache(): Found a previously created obj by the current entry func.\n";
#endif
                }
            }
        }
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "getSharedObjFromCache(): Return Obj: " << (const void*)ro << "\n";
#endif
        return ro;
    }

    int createEmbObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit, InstLoc *loc) {
        if (!fd || !pto || !pto->targetObject) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): (!fd || !pto || !pto->targetObject)\n";
#endif
            return -1;
        }
        if (fd->fid.size() != fd->host_tys.size() || fd->fid.size() == 0) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): #fid(" << fd->fid.size() << ") and #host_tys(" << fd->host_tys.size() << ") don't match!\n";
#endif
            return -1;
        }
        int i;
        AliasObject *currHostObj = pto->targetObject;
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
        dbgs() << "createEmbObjChain(): limit: " << limit << "\n";
#endif
        for (i = fd->fid.size() - 1; i > std::max(0,limit); --i) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): current host obj type: " << InstructionUtils::getTypeStr(currHostObj->targetType) << "\n";
            dbgs() << "createEmbObjChain(): Index " << i << ", about to create an embedded obj for: " 
            << InstructionUtils::getTypeStr(fd->host_tys[i]) << " | " << fd->fid[i] << "\n";
#endif
            if (!InstructionUtils::same_types(fd->host_tys[i],currHostObj->targetType)) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
                dbgs() << "!!! createEmbObjChain(): current host obj type doesn't match the record in the type desc vector, i: " << i << "\n";
#endif
                return i+1;
            }
            pto->targetObject = currHostObj;
            pto->dstfieldId = fd->fid[i];
            AliasObject *newObj = currHostObj->createEmbObj(fd->fid[i],nullptr,loc);
            if (!newObj) {
                //TODO: what to do now...
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
                dbgs() << "createEmbObjChain(): fail to get/create the embedded obj!\n";
#endif
                return i;
            }
            currHostObj = newObj;
        }
        if (InstructionUtils::same_types(currHostObj->targetType,fd->host_tys[i])) {
            pto->targetObject = currHostObj;
            pto->dstfieldId = fd->fid[i];
            return i;
        }else {
            return i+1;
        }
        return -1;
    }

    int createHostObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit, InstLoc *loc) {
        if (!fd || !pto || !pto->targetObject) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): (!fd || !pto || !pto->targetObject)\n";
#endif
            return -1;
        }
        if (fd->fid.size() != fd->host_tys.size() || fd->fid.size() == 0) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): #fid(" << fd->fid.size() << ") and #host_tys(" << fd->host_tys.size() << ") don't match!\n";
#endif
            return -1;
        }
        int i = fd->findHostTy(pto->targetObject->targetType);
        for (++i; i < std::min(limit,(int)fd->fid.size()); ++i) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): current sub obj type: " << InstructionUtils::getTypeStr(pto->targetObject->targetType) << "\n";
            dbgs() << "createHostObjChain(): Index " << i << ", about to create its host obj: " 
            << InstructionUtils::getTypeStr(fd->host_tys[i]) << " | " << fd->fid[i] << "\n";
#endif
            AliasObject *hObj = pto->targetObject->createHostObj(fd->host_tys[i], fd->fid[i], loc);
            if (hObj) {
                //Successfully created.
                pto->targetObject = hObj;
                pto->dstfieldId = fd->fid[i];
            }else {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
                dbgs() << "createHostObjChain(): fail to get/create the host obj!\n";
#endif
                return i;
            }
        }
        return i;
    }

    void PointerPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            Value *tv = this->targetObject->getValue();
            OS << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->dstfieldId 
            << " ,is_taint_src: " << this->targetObject->is_taint_src << ", Obj ID: " << (const void*)(this->targetObject) << ", Inst/Val: ";
            if (tv && dyn_cast<Function>(tv)) {
                OS << "FUNC " << dyn_cast<Function>(tv)->getName().str();
            }else {
                OS << InstructionUtils::getValueStr(tv);
            }
            //print the load tags.
            OS << ", loadTag: ";
            for (TypeField *tf : this->loadTag) {
                OS << InstructionUtils::getValueStr(tf->v) << " [" << tf->fid << "] -> ";
            }
            OS << "\n";
        }else {
            OS << "Null targetObject!\n";
        }
    }

    int ObjectPointsTo::inArray(Type *ty) {
        if (!ty || !this->targetObject) {
            return 0;
        }
        Type *curHostTy = this->targetObject->targetType;
        if (!curHostTy) {
            return 0;
        }
        long fid = this->dstfieldId;
        Type *ety = this->targetObject->getFieldTy(fid);
        if (!ety) {
            return 0;
        }
        if (dyn_cast<SequentialType>(curHostTy) && InstructionUtils::same_types(ty,ety)) {
            return 1;
        }
        if (fid == 0 && InstructionUtils::same_types(ty,curHostTy) && this->targetObject->parent) {
            Type *pty = this->targetObject->parent->targetType;
            if (pty && dyn_cast<SequentialType>(pty)) {
                return 2;
            }
        }
        return 0;
    }

    int ObjectPointsTo::switchArrayElm(Type *ty, long fid) {
        int r = this->inArray(ty);
        if (r == 0) {
            return 0;
        }
        if (r == 1) {
            if (InstructionUtils::isIndexValid(this->targetObject->targetType,fid)) {
                this->dstfieldId = fid;
                return r;
            }
            return 0;
        }
        if (r == 2) {
            AliasObject *newObj = this->targetObject->parent;
            if (InstructionUtils::isIndexValid(newObj->targetType,fid)) {
                //TODO: maybe try to get/create the embedded element.
                this->targetObject = newObj;
                this->dstfieldId = fid;
                return r;
            }
        }
        return 0;
    }

}
