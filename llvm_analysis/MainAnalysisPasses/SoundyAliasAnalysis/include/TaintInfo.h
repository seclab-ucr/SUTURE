//
// Created by machiry on 8/23/16.
//

#ifndef PROJECT_TAINTFLAG_H
#define PROJECT_TAINTFLAG_H

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "../../Utils/include/CFGUtils.h"
#include <vector>

#define DEBUG_UPDATE_FIELD_TAINT
#define DEBUG_FETCH_FIELD_TAINT

using namespace llvm;
namespace DRCHECKER {

//#define DEBUG_INSERT_MOD_INST

    class FieldTaint;
    //hz: Class that intends to identify a unique taint source.
    class TaintTag {
    public:
        long fieldId;
        Value *v = nullptr;
        Type *type = nullptr;
        bool is_global;
        //The AliasObject that is related to this tag.
        void *priv = nullptr;

        TaintTag(long fieldId, Value *v, Type *ty, bool is_global = true, void *p = nullptr) {
            this -> fieldId = fieldId;
            this -> v = v;
            this -> type = ty;
            this -> is_global = is_global;
            this -> priv = p;
        }

        //A wrapper for tag w/ a value pointer.
        TaintTag(long fieldId, Value *v, bool is_global = true, void *p = nullptr):
        TaintTag(fieldId,v,nullptr,is_global,p) {
            this -> type = this->getTy();
        }

        //A wrapper for the type based tag.
        //In case we don't have an actual llvm "Value" pointing to the object, we can just provide the obj type.
        TaintTag(long fieldId, Type *ty, bool is_global = true, void *p = nullptr):
        TaintTag(fieldId,nullptr,ty,is_global,p) {
        }

        TaintTag(TaintTag *srcTag):
        TaintTag(srcTag->fieldId,srcTag->v,srcTag->type,srcTag->is_global,srcTag->priv) {
        }

        std::string getTypeStr() {
            if (!this->type) {
                this->type = this->getTy();
            }
            return InstructionUtils::getTypeStr(this->type);
            /*
            std::string str;
            llvm::raw_string_ostream ss(str);
            this->type->print(ss);
            return ss.str();
            */
        }

        Type *getTy() {
            if (this->type) {
                return this->type;
            }
            if (!(this->v)){
                return nullptr;
            }
            Type *ty = this->v->getType();
            if (ty->isPointerTy()){
                ty = ty->getPointerElementType();
            }
            /*
            if (dyn_cast<CompositeType>(ty) && InstructionUtils::isIndexValid(ty,fieldId)) {
                return InstructionUtils::getTypeAtIndex(ty,fieldId);
            }
            */
            return ty;
        }

        Type *getFieldTy() {
            Type *hostTy = this->getTy();
            return InstructionUtils::getTypeAtIndex(hostTy,this->fieldId);
        }

        bool isTagEquals(TaintTag *dstTag) {
            if (!dstTag){
                return false;
            }
            if (this == dstTag){
                return true;
            }
            return this->fieldId == dstTag->fieldId &&
                   this->v == dstTag->v &&
                   this->type == dstTag->type &&
                   this->is_global == dstTag->is_global &&
                   this->priv == dstTag->priv;
            /*
            if ( (this->priv == dstTag->priv && this->fieldId == dstTag->fieldId) ||
                 (dyn_cast<CompositeType>(this->type) && InstructionUtils::same_types(this->type,dstTag->type) 
                  && this->fieldId == dstTag->fieldId && this->is_global == dstTag->is_global)
               ){
                return true;
            }
            return false;
            */
        }

        void dumpInfo(raw_ostream &OS) {
            OS << "Taint Tag: " << (const void *)this << "\n";
            OS << "Type: " << InstructionUtils::getTypeStr(this->type) << " | " << this->fieldId << " is_global: " << this->is_global << "\n";
            OS << "Obj: " << (const void*)this->priv << " Value: " << InstructionUtils::getValueStr(this->v) << "\n";
        }

        void dumpInfo_light(raw_ostream &OS, bool lbreak = true) {
            OS << "TAG(" << (const void *)this << "):" << InstructionUtils::getTypeName(this->type) 
            << "|" << this->fieldId << "(OBJ:" << (const void*)this->priv << ",G:" << this->is_global << ")";
            if (lbreak) {
                OS << "\n";
            }
        }
    };

    //Class that holds the taint flag
    class TaintFlag {

    public:
        //Constructors
        TaintFlag(InstLoc *targetInstr, bool is_tainted = true, TaintTag *tag = nullptr, bool is_weak = false, bool is_active = true) {
            //Inherent TF may have a null targetInstr indicating that the taint is from the very beginning.
            //assert(targetInstr != nullptr && "Target Instruction cannot be NULL");
            this->targetInstr = targetInstr;
            if (targetInstr) {
                this->instructionTrace.push_back(targetInstr);
            }
            this->is_tainted = is_tainted;
            this->tag = tag;
            this->is_weak = is_weak;
            this->is_active = is_active;
        }

        TaintFlag(TaintFlag *copyTaint):
        TaintFlag(nullptr,copyTaint->isTainted(),copyTaint->tag,copyTaint->is_weak,copyTaint->is_active) {
            this->targetInstr = copyTaint->targetInstr;
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            this->loadTag = copyTaint->loadTag;
            this->memTag = copyTaint->memTag;
        }

        //A copy w/ a different target instruction, this is a wrapper for convenience.
        TaintFlag(TaintFlag *copyTaint, InstLoc *targetInstr):
        TaintFlag(copyTaint) {
            this->targetInstr = targetInstr;
            // add target inst to the trace.
            this->addInstructionToTrace(targetInstr);
        }

        //A copy w/ a different tag, this is a wrapper for convenience.
        TaintFlag(TaintFlag *copyTaint, TaintTag *tag):
        TaintFlag(copyTaint) {
            this->tag = tag;
        }

        //Destructors
        ~TaintFlag() {}

        void setTag(TaintTag *tag) {
            this->tag = tag;
        }

        //Append the tag pointer to the 1st inst in the taint trace, for debugging purpose
        //(e.g., we can easily see the high-order "breakpoints" in the final trace).
        void addTag2Trace() {
            if (this->instructionTrace.empty()) {
                return;
            }
            InstLoc *init = this->instructionTrace[0];
            if (init->p0) {
                //Tag pointer already exists.
                return;
            }
            //We need to make a copy of the 1st InstLoc instead of directly attaching the tag pointer to the existing one,
            //since the existing InstLoc instance may also appear in other TFs...
            InstLoc *ni = new InstLoc(init);
            ni->p0 = this->tag;
            ni->p1 = this;
            ni->icnt = this->instructionTrace.size();
            //TODO: we don't free "init" since it might be used in other TFs, but if not, we have a memory leak..
            //Replace the current 1st InstLoc w/ the new one.
            this->instructionTrace.erase(this->instructionTrace.begin());
            this->instructionTrace.insert(this->instructionTrace.begin(),ni);
        }

        bool isTainted() const {
            return is_tainted;
        }

        //NOTE: we don't consider the "is_weak" and "is_active" properties in the comparison now.
        bool isTaintEquals(const TaintFlag *dstTaint) const {
            if (!dstTaint) {
                return false;
            }
            if (dstTaint == this) {
                return true;
            }
            //hz: we consider the below three properties:
            //(1) whether it's tainted or not
            //(2) the taint source, which is wrapped in our TaintTag class.
            //(3) the targetInst of this taintFlag
            //(opt)(4) the taint path/trace
            //These are properties we consider when comparing two taint flags.
            //Property (1)
            if (this->isTainted() != dstTaint->isTainted()) {
                return false;
            }
            //Property (2):
            if (!this->tag != !dstTaint->tag) {
                return false;
            }
            if (this->tag && !this->tag->isTagEquals(dstTaint->tag)) {
                return false;
            }
            //Property (3)
            if (!this->targetInstr != !dstTaint->targetInstr) {
                return false;
            }
            if (this->targetInstr && !this->targetInstr->same(dstTaint->targetInstr)) {
                return false;
            }
            //Property (4):
            //NOTE: we will not compare the paths by the exact insts, but by the call chains behind the inst trace.
            std::vector<std::vector<Instruction*>*> ctx0, ctx1;
            getCtxOfLocTr(&(this->instructionTrace),ctx0);
            getCtxOfLocTr(&(dstTaint->instructionTrace),ctx1);
            if (ctx0.size() != ctx1.size()) {
                return false;
            }
            for (int i = 0; i < ctx0.size(); ++i) {
                if (*(ctx0[i]) != *(ctx1[i])) {
                    return false;
                }
            }
            /*
            //Compare by the exact inst trace.
            if (this->instructionTrace.size() != dstTaint->instructionTrace.size()) {
                return false;
            }
            for (int i = 0; i < this->instructionTrace.size(); ++i) {
                if (!this->instructionTrace[i] != !dstTaint->instructionTrace[i]) {
                    return false;
                }
                if (this->instructionTrace[i] && !(this->instructionTrace[i])->same(dstTaint->instructionTrace[i])) {
                    return false;
                }
            }
            */
            return true;
        }

        void addInstructionToTrace(InstLoc *toAdd) {
            if (!toAdd) {
                return;
            }
            if (this->instructionTrace.size() > 0) {
                // check if last instruction is the current instruction.
                InstLoc *lastInstr = this->instructionTrace.back();
                if (toAdd->same(lastInstr)) {
                    return;
                }
            }
            this->instructionTrace.push_back(toAdd);
        }

        //Decide whether this TF can be propagated to a target inst location, used to validate a taint path.
        //This is just a wrapper for convenience.
        bool canReach(InstLoc *dest) {
            if (!dest) {
                return false;
            }
            return dest->reachable(this->targetInstr);
        }

        InstLoc *targetInstr;
        // trace of instructions that resulted in this taint.
        std::vector<InstLoc*> instructionTrace;
        
        void dumpInfo(raw_ostream &OS) {
            OS << " Instruction Trace: [\n";
            for (InstLoc *inst : this->instructionTrace) {
                if (inst) {
                    inst->print(OS);
                }
            }
            OS << "]\n";
            OS << "is_inherent: " << this->is_inherent << " is_active: " << this->is_active << " is_weak: " << this->is_weak << "\n";
            //hz: dump tag information if any.
            if (this->tag) {
                this->tag->dumpInfo(OS);
            }

        }

        //Output a compact info line of this TF, omitting the trace.
        void dumpInfo_light(raw_ostream &OS, bool lbreak = true) {
            //Print the tag info.
            if (this->tag) {
                this->tag->dumpInfo_light(OS,false);
            }else {
                OS << "NULL";
            }
            OS << " TF(" << (const void*)this << ") " << " FROM: ";
            if (!this->instructionTrace.empty()) {
                this->instructionTrace[0]->print_light(OS,false);
            }
            OS << " TO: ";
            //Print the target inst.
            if (this->targetInstr) {
                this->targetInstr->print_light(OS,false);
            }
            //Print current #inst in the trace of this TF
            OS << " tr_len: " << this->instructionTrace.size();
            //Print states.
            OS << " tan/inh/act/wea: " << (int)this->is_tainted << "/" << (int)this->is_inherent << "/" 
            << (int)this->is_active << "/" << (int)this->is_weak;
            if (lbreak) {
                OS << "\n";
            }
        }

        //hz: add taint tag support.
        TaintTag *tag;

        //hz: "inherent" means this TaintFlag is not propagated to a value, instead, it's created together w/ the value, indicating
        //that the value itself is a taint source (i.e. an OutsideObject).
        bool is_inherent = false;

        //Indicates whether the flag is currently in effect (e.g. it may be overwritten by another taint).
        bool is_active = true;

        //Indicates whether this is a weak taint flag (i.e. it may or may not taint the target 
        //value/field since the "may point-to" results yielded by the pointer analysis).
        bool is_weak = false;

        // flag to indicate the taint flag.
        //NOTE that if this is "false", we treat it as a taint kill (sanitizer)..
        bool is_tainted;

        // The same loadTag as in PointerPointsTo (someday we need to unify the point-to and taint analysis...).
        std::vector<TypeField*> loadTag;

        // Record all the FieldTaint that this TF has ever appeared in.
        std::vector<FieldTaint*> memTag;
    private:

    };

    /***
     * Class that represents taint of an object field.
     */
    class FieldTaint {
    public:
        long fieldId;
        std::set<TaintFlag*> targetTaint;
        //This should be the host AliasObject*
        void *priv = nullptr;

        //This is the first inst of the entry function for which we have already swicthed to and done the TF reset.
        Instruction *lastReset = nullptr;

        //"winner" means that a non-inherent field taint TF can last until the top-level entry function returns, 
        //w/o being killed or masked by other TFs, we count on these "winner" TFs to construct reliable single-thread user-taint chain.
        //NOTE that if we want to detect the concurrency bugs, we can extend our scope to those killed/masked TFs on the half way.
        std::map<Instruction*,std::set<TaintFlag*>> winnerTfs;

        FieldTaint(long srcField, void *priv = nullptr) {
            this->fieldId = srcField;
            this->priv = priv;
        }

        FieldTaint(void *priv = nullptr) {
            this->fieldId = -1;
            this->priv = priv;
        }

        ~FieldTaint() {
            //TODO: implement this in a smart way.
            /*for(auto currT:targetTaint) {
                delete(currT);
            }*/
        }

        //If "loc" is specified, only copy those TFs that are valid at the "loc", and we will not keep the winnerTFs since
        //this is a fresh copy (e.g. memcpy at loc) w/o history; otherwise, we simply copy everything.
        //"priv" should be the new AliasObject* this FieldTaint is copied for.
        FieldTaint *makeCopy(void *priv, InstLoc *loc = nullptr) {
            FieldTaint *ft = new FieldTaint(this->fieldId,priv);
            ft->lastReset = this->lastReset;
            if (loc) {
                std::set<TaintFlag*> tfs;
                this->getTf(loc,tfs);
                for (TaintFlag *tf : tfs) {
                    TaintFlag *ntf = new TaintFlag(tf,loc);
                    ft->targetTaint.insert(ntf);
                }
            }else {
                //Copy the taintFlags and related info like WinnerTfs.
                std::map<TaintFlag*,TaintFlag*> oldMap;
                for (TaintFlag *tf : this->targetTaint) {
                    TaintFlag *ntf = new TaintFlag(tf);
                    if (tf->is_inherent) {
                        ntf->is_inherent = true;
                        //TODO: Whether or not to replace the inherent tag w/ new obj...
                    }
                    oldMap[tf] = ntf;
                    ft->targetTaint.insert(ntf);
                }
                for (auto &e : this->winnerTfs) {
                    for (TaintFlag *tf : e.second) {
                        if (oldMap.find(tf) == oldMap.end()) {
                            dbgs() << "!!! FieldTaint::makeCopy(): Winner TF doesn't present in oldMap: ";
                            tf->dumpInfo_light(dbgs(),true);
                            continue;
                        }
                        (ft->winnerTfs)[e.first].insert(oldMap[tf]);
                    }
                }
            }
            return ft;
        }

        void reset(FieldTaint *ft) {
            if (!ft) {
                return;
            }
            this->fieldId = ft->fieldId;
            this->targetTaint = ft->targetTaint;
            this->priv = ft->priv;
            this->lastReset = ft->lastReset;
            this->winnerTfs = ft->winnerTfs;
        }

        void removeInhTFs() {
            for (auto it = this->targetTaint.begin(); it != this->targetTaint.end();) {
                TaintFlag *tf = *it;
                if (tf && tf->is_inherent) {
                    it = this->targetTaint.erase(it);
                }else {
                    ++it;
                }
            }
            for (auto &e : this->winnerTfs) {
                for (auto it = e.second.begin(); it != e.second.end();) {
                    TaintFlag *tf = *it;
                    if (tf && tf->is_inherent) {
                        it = e.second.erase(it);
                    }else {
                        ++it;
                    }
                }
            }
        }

        bool empty() {
            return (this->targetTaint.size() == 0);
        }

        bool hasActiveTaint() {
            for (auto tf : this->targetTaint) {
                if (tf && tf->is_active && tf->is_tainted) {
                    return true;
                }
            }
            return false;
        }

        //Insert a TaintFlag to the existing TF set, there are multiple things we need to consider:
        //(1) duplication
        //(2) whether the new TF will block/mask any old TFs (e.g. post-dominate).
        //This is very similar to the logic of "updateFieldPointsTo" in the Alias Analysis, we also need to rely on memory SSA.
        bool addTf(TaintFlag *ntf) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::addTf(): add TF for field " << this->fieldId << ", FieldTaint: " 
            << (const void*)this << ", Host: " << this->priv << "\n";
#endif
            if (!ntf) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): null new TF!\n";
#endif
                return false;
            }
            //Reactivation phase: if the entry function has changed, we need to deactivate the TFs propagated in the previous entry,
            //and then re-activate the inherent TF if present.
            InstLoc *loc = ntf->targetInstr;
            if (loc && loc->hasCtx() && (*loc->ctx)[0]) {
                this->resetTfs((*loc->ctx)[0]);
            }
            //If the to_add is a taint kill but we actually don't have any active taints (i.e. not tainted now), we can just return. 
            if (!ntf->is_tainted && !this->hasActiveTaint()) {
                return false;
            }
            //If this TF has ever been propagated to this same FieldTaint, we'd better not add it again to avoid the potential
            //TF explosion due to the self-taint issue appeared in certain code snippets, e.g., 
            //(1) load from one mem loc, do some calculations, and then store back
            //(2) two mem locs propagating TFs to each other back and forth
            //(3) a linked list in its initial state will have the node->next pointing to itself, if in this case we perform a del_init
            //again to this node, the TFs in node->prev will propagate to the same loc (we need to do "node->next->prev = node->prev", however
            //node->next is node).
            //Solution: we record all the FieldTaint that one TF has ever appeared at in the TF and avoid the self-taint.
            if (std::find(ntf->memTag.begin(),ntf->memTag.end(),this) != ntf->memTag.end()) {
                //Ever being here, we have two situations then:
                //(1) we still have an active TF w/ the same tag on file, so we will not add this new TF.
                //(2) otherwise, proceed w/ the new TF.
                for (TaintFlag *tf : this->targetTaint) {
                    if (tf && tf->is_active && tf->tag == ntf->tag) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                        dbgs() << "FieldTaint::addTf(): self-taint detected, skip: ";
                        ntf->dumpInfo_light(dbgs());
#endif
                        return false;
                    }
                }
            }
            bool is_dup = false;
            std::set<TaintFlag*> to_del;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                if (tf->is_active && ntf->is_active && !ntf->is_weak) {
                    //Strong taint, see whether it will kill/override the existing taint.
                    if (loc && loc->postDom(tf->targetInstr)) {
                        to_del.insert(tf);
                    }
                }
                if (is_dup || (tf != ntf && !ntf->isTaintEquals(tf))) {
                    continue;
                }
                //Ok, we already have an exactly same taint flag.
                is_dup = true;
                //TODO: justify the decision to update the "is_weak" to the strongest value...
                if (ntf->is_weak != tf->is_weak) {
                    tf->is_weak = false;
                }
                //Update the active state to the latest.
                tf->is_active = ntf->is_active;
            }
            if (!is_dup) {
                //Insert the new TF.
                this->targetTaint.insert(ntf);
                //Mark the existence of this TF in this FieldTaint.
                ntf->memTag.push_back(this);
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): +++TF: ";
                ntf->dumpInfo_light(dbgs());
#endif
            }
            //De-activate the overriden TFs, if any.
            for (TaintFlag *tf : to_del) {
                tf->is_active = false;
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): ---TF: ";
                tf->dumpInfo_light(dbgs());
#endif
            }
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::addTf(): post-stats: ";
            this->logFieldTaint(dbgs());
#endif
            return !is_dup;
        }

        //This function needs to be called (and only called) when we have just finished analyzing an top-level entry function
        //and want to record which non-inherent TFs can last to the end.
        void collectWinnerTfs() {
            //First get the current entry function we are in.
            if (!this->lastReset || !this->lastReset->getParent()) {
                return;
            }
            Function *efunc = this->lastReset->getFunction();
            if (!efunc) {
                return;
            }
            if (this->winnerTfs.find(this->lastReset) != this->winnerTfs.end()) {
                //Winner TFs already collected for current entry.
                return;
            }
            //Then get all return sites of the entry function.
            std::set<Instruction*> rets;
            BBTraversalHelper::getRetInsts(efunc, rets);
            //Now caculate the winners..
            std::vector<Instruction*> ctx;
            ctx.push_back(this->lastReset);
            for (Instruction *ri : rets) {
                if (!ri) {
                    continue;
                }
                InstLoc rloc(ri,&ctx);
                std::set<TaintFlag*> wtfs;
                this->doGetTf(&rloc,wtfs);
                for (TaintFlag *wtf : wtfs) {
                    if (wtf) {
                        this->winnerTfs[this->lastReset].insert(wtf);
                    }
                }
            }
        }

        //Return all winner TFs (i.e. as long as it can survivie one entry function).
        //NOTE: this function should only be invoked after we finish all main analyses and in the bug detection phase. 
        void getWinners(std::set<TaintFlag*> &r) {
            //First we need to make sure the winner TFs in the last entry function have been collected, e.g. if it's the
            //last entry function in the analysis sequence, we don't have the opportunity to resetTfs() and thus collect the winners.
            this->collectWinnerTfs();
            //Now simply return all winner TFs.
            for (auto &e : this->winnerTfs) {
                for (TaintFlag *tf : e.second) {
                    if (tf) {
                        r.insert(tf);
                    }
                }
            }
            return;
        }

        //Reset the TFs due to the top entry function switch.
        void resetTfs(Instruction *entry) {
            assert(entry);
            if (!this->lastReset) {
                this->lastReset = entry;
            }
            if (this->lastReset == entry) {
                //Still within the same top-level entry func, no need to reset.
                return;
            }
            //Ok, we need to do the reset...
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::resetTfs(): reset field (" << this->fieldId << ", FieldTaint: " 
            << (const void*)this << ", Host: " << this->priv << ") taint since we have switched to a new entry: ";
            InstructionUtils::printInst(entry,dbgs());
#endif
            //Before the actual reset, let's first record the winner TFs in the previous entry function.
            this->collectWinnerTfs();
            //Update the last reset inst to the current.
            this->lastReset = entry;
            //Do the reset, we need to:
            //(1) deactivate those TFs propagated under different entry functions.
            //(2) reactivate the inherent TFs if any. (it will be strange if we don't have one...)
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                InstLoc *loc = tf->targetInstr;
                //TODO: whether to treat the TF w/ null targetInstr the same as an inherent TF.
                if (tf->is_inherent || !loc) {
                    tf->is_active = true;
                    continue;
                }
                if (tf->is_active && loc && !loc->sameEntry(entry)) {
                    tf->is_active = false;
                }
            }
            return;
        }

        //Get the TFs that are valid at the "loc" (e.g. some TFs may be overridden by the others).
        //The logic is similar to "fetchFieldPointsTo" in the Alias Analysis.
        bool getTf(InstLoc *loc, std::set<TaintFlag*> &r) {
#ifdef DEBUG_FETCH_FIELD_TAINT
            dbgs() << "FieldTaint::getTf(): fetch taint for field: " << this->fieldId << ", FieldTaint: " 
            << (const void*)this << ", Host: " << this->priv << "\n";
#endif
            //Reactivation phase: if the entry function has changed, we need to deactivate the TFs propagated in the previous entry,
            //and then re-activate the inherent TF if present.
            if (loc && loc->hasCtx() && (*loc->ctx)[0]) {
                this->resetTfs((*loc->ctx)[0]);
            }
            return this->doGetTf(loc,r);
        }

        //This method simply returns all inherent TFs w/o considering the current "loc" and memory SSA,
        //this can be useful since inherent TFs are special and in some scenarios we may need access them.
        //NOTE: in theory there can be only one inherent TF for each object or field, we use such a "return set" interface just for safe.
        bool getInherentTf(std::set<TaintFlag*> &r) {
            for (TaintFlag *tf : this->targetTaint) {
                if (tf && tf->is_inherent) {
                    r.insert(tf);
                }
            }
            return !!r.size();
        }

        TaintFlag *getInherentTf() {
            for (TaintFlag *tf : this->targetTaint) {
                if (tf && tf->is_inherent) {
                    return tf;
                }
            }
            return nullptr;
        }

        void logFieldTaint(raw_ostream &O, bool lbreak = true) {
            int act = 0, inh = 0, wea = 0, tan = 0;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                if (tf->is_tainted) {
                    ++tan;
                }
                if (tf->is_active) {
                    ++act;
                }
                if (tf->is_inherent) {
                    ++inh;
                }
                if (tf->is_weak) {
                    ++wea;
                }
            }
            O << "total/tan/act/inh/weak: " << this->targetTaint.size() << "/" << tan << "/" << act << "/" << inh << "/" << wea;
            if (lbreak) {
                O << "\n";
            }
         }

        bool doGetTf(InstLoc *loc, std::set<TaintFlag*> &r, bool filter_active = true) {
            //First get all active non-kill TFs and blockers.
            std::set<InstLoc*> blocklist;
            std::set<TaintFlag*> actTf;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                if (filter_active && !tf->is_active) {
                    continue;
                }
                //The taint kill TF (i.e. ->is_tainted == false) will not be added to "actTf", but they will be added
                //to the "blocklist", so that we will only return the normal TFs, or null if all normal TFs are sanitized.
                if (tf->is_tainted) {
                    actTf.insert(tf);
                }
                if (tf->targetInstr && !tf->is_weak) {
                    blocklist.insert(tf->targetInstr);
                }
            }
            //Get the live TFs at the "loc"..
            int numTf = 0;
            if (loc) {
                for (TaintFlag *tf : actTf) {
                    //NOTE that if "tf->targetInstr" is null, the TF will treated as a pre-set global TF.
                    if (loc->reachable(tf->targetInstr,&blocklist)) {
                        r.insert(tf);
                        ++numTf;
                    }
                    //For logging..
                    if (!tf->is_inherent && !tf->targetInstr) {
#ifdef DEBUG_FETCH_FIELD_TAINT
                        dbgs() << "!!! FieldTaint::getTf(): TF (non-inherent) w/o targetInstr: ";
                        tf->dumpInfo_light(dbgs());
#endif
                    }
                }
            }else {
#ifdef DEBUG_FETCH_FIELD_TAINT
                dbgs() << "FieldTaint::getTf(): null target loc! Return all active TFs: " << actTf.size() << "\n";
#endif
                r.insert(actTf.begin(),actTf.end());
                numTf = actTf.size();
            }
#ifdef DEBUG_FETCH_FIELD_TAINT
            dbgs() << "FieldTaint::getTf(): final stats: total/act_tan/ret: " << this->targetTaint.size() << "/" 
            << actTf.size() << "/" << r.size() << "\n";
#endif
            return true;
        }
    };

}

#endif //PROJECT_TAINTFLAG_H
