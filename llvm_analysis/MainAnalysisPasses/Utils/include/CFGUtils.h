//
// Created by machiry on 12/3/16.
//

#ifndef PROJECT_CFGUTILS_H
#define PROJECT_CFGUTILS_H
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {

    #define DEBUG_INTER_PROC_POSTDOM

    // This encodes the information to locate an instruction within a certain call context,
    // it also provides some utilities like reachability test w/ another instruction.
    class InstLoc {
        public:
        //The llvm inst itself.
        Value *inst;
        //The calling context of this inst.
        std::vector<Instruction*> *ctx;
        //To store taint tag pointer, for debugging purpose.
        void *p0 = nullptr;
        //To store TF pointer.
        void *p1 = nullptr;
        //If p0 is effective, this is the #inst in the trace of the TF.
        unsigned icnt = 0;

        InstLoc(Value *inst, std::vector<Instruction*> *ctx) {
            this->inst = inst;
            this->ctx = ctx;
        }

        InstLoc(InstLoc *other) {
            if (other) {
                this->inst = other->inst;
                this->ctx = other->ctx;
            }else {
                this->inst = nullptr;
                this->ctx = nullptr;
            }
        }

        bool same(InstLoc *other) {
            if (!other) {
                return false;
            }
            //Compare the llvm inst itself.
            if (this->inst != other->inst) {
                return false;
            }
            //Compare the calling context of the inst.
            if (!this->ctx != !other->ctx) {
                return false;
            }
            //shortcut
            if (this->ctx == other->ctx) {
                return true;
            }
            if (this->ctx && *this->ctx != *other->ctx) {
                return false;
            }
            return true;
        }

        bool hasCtx() {
            return (this->ctx && !this->ctx->empty());
        }

        //Whether this InstLoc is in an entry function.
        bool inEntry() {
            if (!this->hasCtx()) {
                return false;
            }
            Instruction *e = (*this->ctx)[0];
            if (!e || !e->getParent()) {
                return false;
            }
            return true;
        }

        //Return the first inst in the calling context (i.e. the first inst of the top-level entry function).
        Instruction *getEntryInst() {
            return (this->hasCtx() ? (*this->ctx)[0] : nullptr);
        }

        //Return true if this is in an entry func and is in a same one as "e".
        //We assume that "e" is also in an entry block, just as those insts in the calling context.
        bool sameEntry(Instruction *e) {
            if (!e || !e->getParent() || !this->inEntry()) {
                return false;
            }
            return this->getEntryInst()->getParent() == e->getParent();
        }

        //Whether "this"'s ctx is a prefix of "other"'s.
        //Identical ctx: return 0, prefix: return the 1st index after the prefix, otherwise -1.
        int isCtxPrefix(InstLoc *other) {
            if (!other) {
                return -1;
            }
            if (!other->hasCtx()) {
                return (this->hasCtx() ? -1 : 0);
            }
            int i = 0;
            for (;i < this->ctx->size() && i < other->ctx->size(); ++i) {
                if ((*this->ctx)[i] != (*other->ctx)[i]) {
                    break;
                }
            }
            if (i >= this->ctx->size()) {
                return (i < other->ctx->size() ? i : 0);
            }
            return -1;
        }

        Function *getFunc() {
            Instruction *I = dyn_cast<Instruction>(this->inst);
            if (!I || !I->getParent()) {
                return nullptr;
            }
            return I->getFunction();
        }

        void print(raw_ostream &O);

        //One line compact output of this InstLoc.
        void print_light(raw_ostream &O, bool lbreak = true);

        //Return true if this InstLoc post-dominates the "other" InstLoc.
        bool postDom(InstLoc *other, bool is_strict = true);

        //Return true if this is reachable from the "other" InstLoc, under the presence of the blocking instructions in the "blocklist".
        bool reachable(InstLoc *other, std::set<InstLoc*> *blocklist = nullptr);
        
        //Decide whether current inst can be reached from (or return to) its one specified upward callsite (denoted by the
        //index "ci" in its calling context), in the presence of the blocking insts in the "blocklist".
        bool chainable(int ci, std::set<InstLoc*> *blocklist, bool callFrom = true);

        //Decide whether "this" can be reached from the entry or can reach the return of its host function when there exists some blocking nodes.
        bool canReachEnd(std::set<InstLoc*> *blocklist, bool fromEntry = true);

        void getBlockersInCurrFunc(std::set<InstLoc*> *blocklist, std::set<Instruction*> &validBis);
    };

    extern void printInstlocJson(InstLoc *inst, llvm::raw_ostream &O);

    extern void printInstlocTraceJson(std::vector<InstLoc*> *instTrace, llvm::raw_ostream &O);

    extern void getCtxOfLocTr(const std::vector<InstLoc*> *tr, std::vector<std::vector<Instruction*>*> &res);

    extern bool sameLocTr(std::vector<InstLoc*> *tr0, std::vector<InstLoc*> *tr1);

    //Get the order of this warning, order can be viewed as the necessary invocation times of entry functions to trigger
    //the bug (e.g. if to trigger this warning we need to first invoke entry function A then B, we say its order is 2, 
    //another example is we may need to first invoke ioctl() w/ cmd 0, then the same ioctl() w/ cmd 1, the order is still
    //2 since we need to invoke an entry function for 2 times).
    extern int getTrOrder(std::vector<InstLoc*> *tr);

    class BBTraversalHelper {
    public:
        /***
         * Get the Strongly connected components(SCC) of the CFG of the provided function in topological order
         * @param currF Function whose SCC visiting order needs to be fetched.
         * @return vector of vector of BasicBlocks.
         *     i.e vector of SCCs
         */
        static std::vector<std::vector<BasicBlock *> *> *getSCCTraversalOrder(Function &currF);

        //print the TraversalOrder to the output stream
        static void printSCCTraversalOrder(std::vector<std::vector<BasicBlock *>*> *order, raw_ostream *OS);

        /***
         * Get number of times all the BBs in the provided strongly connected component need to be analyzed
         * So that all the information is propagated correctly.
         * @param currSCC vector of BBs in the Strongly connected component.
         * @return number of times all the BBs needs to be analyzed to ensure
         * that all the information with in SCC is properly propagated.
         */
        static unsigned long getNumTimesToAnalyze(std::vector<BasicBlock *> *currSCC);

        /***
         * Checks whether a path exists from startInstr to endInstr along provided callSites.
         *
         * @param startInstr src or from instruction from where we need to check for path.
         * @param endInstr dst or to instruction to check for path
         * @param callSites pointer to the vector of callsites through which endInstr is reached from startInstr
         * @return true/false depending on whether a path exists or not.
         */
        static bool isReachable(Instruction *startInstr, Instruction *endInstr, std::vector<Instruction*> *callSites);

        static llvm::DominatorTree *getDomTree(llvm::Function*);

        static void getDominators(llvm::BasicBlock *bb, std::set<llvm::BasicBlock*> &res, bool self = true);

        static void getDominatees(llvm::BasicBlock *bb, std::set<llvm::BasicBlock*> &res, bool self = true);

        //NOTE: as long as we have the post-dom tree, we can invoke its member function "->dominates()" to decide the
        //post-dominance relationship of two Insts:
        //Prototype from the llvm src file:
        /// Return true if \p I1 dominates \p I2. This checks if \p I2 comes before
        /// \p I1 if they belongs to the same basic block.
        /// bool dominates(const Instruction *I1, const Instruction *I2) const;
        static llvm::PostDominatorTree *getPostDomTree(llvm::Function*);

        //We assume src and end are within the same function.
        static bool instPostDom(Instruction *src, Instruction *end, bool is_strict = false);

        //Get all dom nodes for all return sites (i.e. in order to return we must pass these nodes).
        static void getDomsForRet(llvm::Function* pfunc, std::set<llvm::BasicBlock*> &ret);

        static void getRetBBs(llvm::Function* pfunc, std::set<llvm::BasicBlock*> &r);
        
        static void getRetInsts(llvm::Function* pfunc, std::set<llvm::Instruction*> &r);

        //The mapping from one BB to all its successors (recursively).
        static std::map<BasicBlock*,std::set<BasicBlock*>> succ_map;

        static void _get_all_successors(BasicBlock *bb, std::set<BasicBlock*> &res);

        static std::set<BasicBlock*> *get_all_successors(BasicBlock *bb);
    };
}
#endif //PROJECT_CFGUTILS_H
