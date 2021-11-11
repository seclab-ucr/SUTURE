//
// Created by machiry on 12/3/16.
//

#include "CFGUtils.h"

namespace DRCHECKER {

    // NOTE: this "TopoSorter" class is adpated from online:
    // https://github.com/eliben/llvm-clang-samples/blob/master/src_llvm/bb_toposort_sccs.cpp
    // Runs a topological sort on the basic blocks of the given function. Uses
    // the simple recursive DFS from "Introduction to algorithms", with 3-coloring
    // of vertices. The coloring enables detecting cycles in the graph with a simple
    // test.
    class TopoSorter {
    public:
        TopoSorter() {
            //
        }
        // Given a set of BBs (e.g., BBs belonging to a SCC), we try to sort them in the topological order.
        // The most important thing is we will try to identify back edges if any and act as if they don't exist, which is useful
        // if we want to get a topological sort of BBs in a loop as if the loop is only executed once (e.g., most topo sort
        // yield wrong results in the presence of back edges).
        // The passed-in BBs will be sorted in-place.
        void runToposort(std::vector<BasicBlock*> *BBs) {
            if (!BBs || BBs->size() <= 1) {
                return;
            }
            this->BBs = BBs;
            // Initialize the color map by marking all the vertices white.
            for (BasicBlock *bb : *BBs) {
                ColorMap[bb] = TopoSorter::WHITE;
            }
            // We will always start DFS from the first BB in the vector (e.g., assuming it's the loop head).
            bool success = recursiveDFSToposort((*BBs)[0]);
            if (success) {
                // Now we have all the BBs inside SortedBBs in reverse topological order.
                // Put the reversed sorted results in BBs.
                BBs->clear();
                for (unsigned i = 0; i < SortedBBs.size(); ++i) {
                    BBs->insert(BBs->begin(),SortedBBs[i]);
                }
            }
        }

    private:
        // "BBs": The BB set to be sorted.
        // "SortedBBs": Collects vertices (BBs) in "finish" order. The first finished vertex is first, and so on.
        std::vector<BasicBlock*> *BBs, SortedBBs;
        enum Color { WHITE, GREY, BLACK };
        // Color marks per vertex (BB).
        DenseMap<BasicBlock *, Color> ColorMap;

        // Helper function to recursively run topological sort from a given BB.
        // This will ignore the back edge when encountered.
        bool recursiveDFSToposort(BasicBlock *BB) {
            if (!BB || std::find(this->BBs->begin(),this->BBs->end(),BB) == this->BBs->end()) {
                return true;
            }
            ColorMap[BB] = TopoSorter::GREY;
            for (llvm::succ_iterator sit = llvm::succ_begin(BB), set = llvm::succ_end(BB); sit != set; ++sit) {
                BasicBlock *Succ = *sit;
                Color SuccColor = ColorMap[Succ];
                if (SuccColor == TopoSorter::WHITE) {
                    if (!recursiveDFSToposort(Succ))
                        return false;
                } else if (SuccColor == TopoSorter::GREY) {
                    // This detects a cycle because grey vertices are all ancestors of the
                    // currently explored vertex (in other words, they're "on the stack").
                    // But we just ignore it and act as if current "Succ" has been explored.
                }
            }
            // This BB is finished (fully explored), so we can add it to the vector.
            ColorMap[BB] = TopoSorter::BLACK;
            SortedBBs.push_back(BB);
            return true;
        }
    };

    // This code is copied from an online source.
    std::vector<std::vector<BasicBlock*>*> *BBTraversalHelper::getSCCTraversalOrder(Function &currF) {
        std::vector<std::vector<BasicBlock *> *> *bbTraversalList = new std::vector<std::vector<BasicBlock *> *>();
        const Function *F = &currF;
        //NOTE: both the SCCs and the BBs within each SCC are sorted in the reverse topological order with scc_iterator,
        //so we need to re-revert the order.  
        for (scc_iterator<const Function *> I = scc_begin(F), IE = scc_end(F); I != IE; ++I) {
            // Obtain the vector of BBs in this SCC and print it out.
            const std::vector<const BasicBlock *> &SCCBBs = *I;
            std::vector<BasicBlock *> *newCurrSCC = new std::vector<BasicBlock *>();
            for (unsigned int i = 0; i < SCCBBs.size(); ++i) {
                for (Function::iterator b = currF.begin(), be = currF.end(); b != be; ++b) {
                    BasicBlock *BB = &(*b);
                    if (BB == SCCBBs[i]) {
                        newCurrSCC->insert(newCurrSCC->begin(), BB);
                        break;
                    }
                }
            }
            //HZ: NOTE: "succ_iterator" maintains the reverse topological order between SCCs, but inside a single SCC that
            //has multiple BBs, the output order is "reverse DFS visit order" instead of "reverse topological order",
            //e.g., assume the SCC: A->B, A->C, B->C, C->A, the DFS visit order might be A->C->B (if A's child C is visited before B),
            //however, the topo order should be A->B->C as B has an edge to C.
            //To solve this problem, we need to run an extra sorting for SCCs which have more than 1 nodes, forcing it to be in the topo order.
            if (newCurrSCC->size() > 1) {
                TopoSorter tps;
                tps.runToposort(newCurrSCC);
            }
            bbTraversalList->insert(bbTraversalList->begin(), newCurrSCC);
        }
        return bbTraversalList;
    }

    void BBTraversalHelper::printSCCTraversalOrder(std::vector<std::vector<BasicBlock *>*> *order, raw_ostream *OS) {
        if (!order || !OS) {
            return;
        }
        for (auto m1 : *order) {
            (*OS) << "SCC START:" << m1->size() << ":\n";
            for (auto m2 : *m1) {
                (*OS) << InstructionUtils::getBBStrID(m2) << " -> ";
            }
            (*OS) << "SCC END\n";
        }
    }

    unsigned long BBTraversalHelper::getNumTimesToAnalyze(std::vector<BasicBlock *> *currSCC) {
        /***
             * get number of times all the loop basicblocks should be analyzed.
             *  This is same as the longest use-def chain in the provided
             *  strongly connected component.
             *
             *  Why is this needed?
             *  This is needed because we want to ensure that all the
             *  information inside the loops have been processed.
             */

        std::map<BasicBlock *, unsigned long> useDefLength;
        useDefLength.clear();

        std::set<BasicBlock *> useDefChain;
        useDefChain.clear();
        std::set<BasicBlock *> visitedBBs;
        std::set<BasicBlock *> currBBToAnalyze;
        currBBToAnalyze.clear();
        unsigned long numToAnalyze = 1;

        for(BasicBlock *currBBMain:(*currSCC)) {
            if(useDefLength.find(currBBMain) == useDefLength.end()) {
                currBBToAnalyze.clear();
                currBBToAnalyze.insert(currBBToAnalyze.end(), currBBMain);
                useDefChain.clear();
                useDefChain.insert(useDefChain.end(), currBBMain);
                visitedBBs.clear();
                while (!currBBToAnalyze.empty()) {
                    for (auto currBB:currBBToAnalyze) {
                        visitedBBs.insert(visitedBBs.end(), currBB);
                        for (BasicBlock::iterator bstart = currBB->begin(), bend = currBB->end();
                             bstart != bend; bstart++) {
                            Instruction *currIns = &(*bstart);

                            for(int jkk=0;jkk < currIns->getNumOperands();jkk++) {
                                Value *i=currIns->getOperand(jkk);
                                if (Instruction *Inst = dyn_cast<Instruction>(i)) {
                                    BasicBlock *useBB = Inst->getParent();
                                    if (std::find(currSCC->begin(), currSCC->end(), useBB) != currSCC->end()) {
                                        if (useDefChain.find(useBB) == useDefChain.end()) {
                                            useDefChain.insert(useDefChain.end(), useBB);
                                        }
                                    }
                                }
                            }
                        }
                    }


                    currBBToAnalyze.clear();

                    for(auto b:useDefChain) {
                        if(visitedBBs.find(b) == visitedBBs.end()) {
                            currBBToAnalyze.insert(currBBToAnalyze.end(), b);
                        }
                    }

                }

                for (BasicBlock *vicBB:useDefChain) {
                    if(useDefLength.find(vicBB) == useDefLength.end()) {
                        useDefLength[vicBB] = useDefChain.size();
                    }
                }
            }
        }

        for(auto b:(*currSCC)) {
            if(useDefLength.find(b) != useDefLength.end()) {
                if(numToAnalyze < useDefLength[b]) {
                    numToAnalyze = useDefLength[b];
                }
            }
        }

        return numToAnalyze;

    }


    unsigned getSuccNum(BasicBlock *bb) {
        if (!bb) {
            return 0;
        }
        unsigned c = 0;
        for (auto I = succ_begin(bb), E = succ_end(bb); I != E; ++I, ++c);
        return c;
    }

    // The basic skeleton of the below code is from llvm, but we need to add support 
    //for "blocklist" and accurate reachability test instead of "potentially".
    // "limit": Limit the number of blocks we visit. The goal is to avoid run-away compile times on large CFGs without hampering sensible code.
    // We can set "limit" to 0 to have an accurate reachability test (i.e. exhaust *all* the paths).
    bool isPotentiallyReachableFromMany(SmallVectorImpl<BasicBlock*> &Worklist, Instruction *Stop, 
                                        unsigned limit = 32, std::set<Instruction*> *blocklist = nullptr) {
        bool has_limit = (limit > 0);
        SmallSet<const BasicBlock*, 32> Visited;
        do {
            BasicBlock *BB = Worklist.pop_back_val();
            if (!Visited.insert(BB).second)
                continue;
            //Visit this BB to see whether the path is killed by a blocking inst or it can reach the target inst already.
            //First get the effective blocking insts in current BB.
            std::set<Instruction*> validBis;
            if (blocklist && !blocklist->empty()) {
                for (Instruction *bi : *blocklist) {
                    if (bi && bi->getParent() == BB) {
                        validBis.insert(bi);
                    }
                }
            }
            //Scan current BB.
            if (Stop) {
                if (Stop->getParent() != BB) {
                    if (!validBis.empty()) {
                        //Killed...
                        continue;
                    }
                }else {
                    if (validBis.empty()) {
                        //Victory!
                        return true;
                    }else {
                        //See whether we will be killed before reaching "Stop".
                        for (Instruction &I : *BB) {
                            if (&I == Stop) {
                                return true;
                            }
                            if (validBis.find(&I) != validBis.end()) {
                                //No need to explore more paths since the killer is just before the destination in the same BB.
                                return false;
                            }
                        }
                        //Impossible to get here.
                        assert(false);
                    }
                }
            }else {
                if (!getSuccNum(BB)) {
                    //We have reached a return site (null Stop means we need to find a path to the return).
                    if (validBis.empty()) {
                        //Nothing between us and a return.
                        return true;
                    }else {
                        continue;
                    }
                }else {
                    //Need to continue explore unless it's already killed.
                    if (!validBis.empty()) {
                        continue;
                    }
                }
            }
            if (has_limit && !--limit) {
                // We haven't been able to prove it one way or the other. Conservatively
                // answer true -- that there is potentially a path.
                return true;
            }
            Worklist.append(succ_begin(BB), succ_end(BB));
        } while (!Worklist.empty());
        // We have exhausted all possible paths and are certain that 'To' can not be
        // reached from 'From'.
        return false;
    }

    //This assumes A and B are within the same BB, perform a linear scan to decide the reachability from A to B.
    //NOTE: the scope is only the single BB, e.g. we don't consider the case where B reach an earlier position in the BB via a outside loop.
    bool isReachableInBB(Instruction *A, Instruction *B) {
        if (!A || !B || A->getParent() != B->getParent()) {
            return false;
        }
        BasicBlock *BB = const_cast<BasicBlock*>(A->getParent());
        // Linear scan, start at 'A', see whether we hit 'B' or the end first.
        for (BasicBlock::iterator I = A->getIterator(), E = BB->end(); I != E;
             ++I) {
            if (&*I == B)
                return true;
        }
        return false;
    }

    //NOTE: we assume both "A", "B", and those blocking instructions in "blocklist" all belong to the *same* function!
    //If "A" is nullptr, we will set the entry inst as "A";
    //If "B" is nullptr, we will regard any function return inst as "B" (e.g. return true if "A" can reach any ret inst).
    bool isPotentiallyReachable(Instruction *A, Instruction *B, unsigned limit = 32, std::set<Instruction*> *blocklist = nullptr) {
        if (!A && !B) {
            return true;
        }
        if ((A && !A->getParent()) || (B && !B->getParent())) {
            //One of these insts may be created by ourselves.. Conservatively return true.
            dbgs() << "!!! isPotentiallyReachable(): A or B doesn't belong to any BBs! A: " << InstructionUtils::getValueStr(A);
            dbgs() << " B: " << InstructionUtils::getValueStr(B) << "\n";
            return true;
        }
        if (A && B && A->getParent()->getParent() != B->getParent()->getParent()) {
            //They belong to different functions.
            dbgs() << "!!! isPotentiallyReachable(): A and B have different host functions! A: " << InstructionUtils::getValueStr(A);
            dbgs() << " B: " << InstructionUtils::getValueStr(B) << "\n";
            return false;
        }
        SmallVector<BasicBlock*, 32> Worklist;
        if (!A) {
            //Whether we can reach inst B from the function entry w/ the blocking insts.
            //If no blocking insts at all obviously we can arrive anywhere within the function from entry.
            if (!blocklist || blocklist->empty()) {
                return true;
            }
            //Otherwise perform the standard path search from the entry node.
            BasicBlock *BB = const_cast<BasicBlock*>(B->getParent());
            Worklist.push_back(&BB->getParent()->getEntryBlock());
        }else if (!B) {
            //Test whether A can reach any return site w/ the block list.
            //If no blocking insts obviously we can arrive at the return sites.
            if (!blocklist || blocklist->empty()) {
                return true;
            }
            //Otherwise first see whether it's already blocked within the same node.
            BasicBlock *BB = const_cast<BasicBlock*>(A->getParent());
            for (Instruction *bi : *blocklist) {
                if (bi && bi->getParent() == BB && bi != A && isReachableInBB(A,bi)) {
                    return false;
                }
            }
            //It can survive the current node, then do the standard path search towards the return sites.
            Worklist.append(succ_begin(BB), succ_end(BB));
            if (Worklist.empty()) {
                //This means A is already in a return node, and it's not blocked to the end, so directly return true.
                return true;
            }
        }else {
            //Both A and B are not null.
            //Optimizations for null "blocklist":
            if (!blocklist || blocklist->empty()) {
                if (A->getParent() != B->getParent()) {
                    if (A->getParent() == &A->getParent()->getParent()->getEntryBlock())
                        return true;
                    if (B->getParent() == &A->getParent()->getParent()->getEntryBlock())
                        return false;
                }
            }
            //First see whether A can go out of its host BB w/o being killed by blocking inst (return false) or meeting B (return true).
            BasicBlock *BB = const_cast<BasicBlock*>(A->getParent());
            for (BasicBlock::iterator I = A->getIterator(), E = BB->end(); I != E; ++I) {
                if (&*I == B) {
                    return true;
                }
                if (blocklist && &*I != A && blocklist->find(&*I) != blocklist->end()) {
                    //Blocked before reaching B...
                    return false;
                }
            }
            //Shortcuts from the original llvm code: if A and B are both in entry node (cannot be in a loop) and B is before A, return false.
            if (BB == B->getParent() && BB == &BB->getParent()->getEntryBlock()) {
                return false;
            }
            //Then standard path search..
            Worklist.append(succ_begin(BB), succ_end(BB));
            if (Worklist.empty()) {
                // We've proven that there's no path!
                return false;
            }
        }
        //A final optimization: if there are any blocking insts just before B within the same BB, return false directly.
        //NOTE: the cases where A and B are in the same BB and A is after certain blocking insts in the BB are all handled above.
        if (B && blocklist && !blocklist->empty()) {
            BasicBlock *BB = B->getParent();
            for (Instruction *bi : *blocklist) {
                if (bi && bi->getParent() == BB && isReachableInBB(bi,B)) {
                    return false;
                }
            }
        }
        return isPotentiallyReachableFromMany(Worklist, B, limit, blocklist);
    }

    // llvm skeleton ends.

    //We now have a set of blocking insts "bis" associated w/ a same up-level callsite (e-1 is the callsite index in their ctx),
    //we need to decide whether these blocking insts will prevent that callsite from returning.
    //NOTE: this callsite may have multiple different callees (e.g. indirect call), in that case, as long as one callee can be
    //bypassed, we will conclude that the callsite can be bypassed to be conservative.
    bool bypassCall(std::set<InstLoc*> &bis, unsigned e) {
        if (bis.empty() || !e) {
            return true;
        }
        //First group the blocking insts according to the 1st callee of the callsite.
        Instruction *cs = nullptr;
        std::map<Instruction*,std::set<InstLoc*>> callBis; 
        for (InstLoc *bi : bis) {
            if (bi && bi->hasCtx() && e < bi->ctx->size() && 
                (*bi->ctx)[e] && (*bi->ctx)[e-1]) {
                if (!cs) {
                    cs = (*bi->ctx)[e-1];
                }else if (cs != (*bi->ctx)[e-1]) {
                    //This doesn't match our pre-condition about this function - blcokers should originate from the same call site.
                    continue;
                }
                callBis[(*bi->ctx)[e]].insert(bi);
            }
        }
        if (callBis.empty()) {
            return true;
        }
        //Insepct each group, as long as one can be bypassed, return true.
        for (auto &p : callBis) {
            Instruction *ei = p.first;
            std::set<InstLoc*> &ebis = p.second;
            //Recursion: for the 1st layer callee, get all direct blocking insts and potential blocking callsites (i.e. the actual blocking inst
            //is in a >1 layer callee), then recursively call "bypassCall" to see whether these callsites are true blockers.
            //After deciding all blocker sites in this 1st level callee, just test the reachability from the entry to return to see whether
            //the original callsite in the up-level can be bypassed.
            std::map<Instruction*, std::set<InstLoc*>> callsiteBis;
            std::set<Instruction*> instBis;
            for (InstLoc *bi : ebis) {
                if (e + 1 >= bi->ctx->size()) {
                    //No more callsites, the blocker is just in current function.
                    if (dyn_cast<Instruction>(bi->inst)) {
                        instBis.insert(dyn_cast<Instruction>(bi->inst));
                    }
                }else {
                    //Another callsite - a potential blocker but not sure.
                    //Some sanity checks..
                    Instruction *I0 = (*bi->ctx)[e];
                    Instruction *I1 = (*bi->ctx)[e+1];
                    if (I0 && I1 && I0->getParent() && I1->getParent() && I0->getFunction() == I1->getFunction()) {
                        callsiteBis[I1].insert(bi);
                    }
                }
            }
            //Before resorting to the standard reachability test, we can do some optimizations for early decisions.
            unsigned isz = instBis.size();
            unsigned csz = callsiteBis.size();
            if (isz + csz == 0) {
                return true;
            }
            std::set<BasicBlock*> retDoms;
            BBTraversalHelper::getDomsForRet(ei->getFunction(), retDoms);
            //In theory there must exist some dominators for the return sites (e.g. the entry node), so if the return set is empty there must 
            //be something wrong - in that case we fallback to not have any optimizations since it's already unreliable. 
            if (isz + csz == 1 && !retDoms.empty()) {
                if (isz > 0) {
                    //We can conclude immediately.
                    BasicBlock *bib = (*instBis.begin())->getParent();
                    if (retDoms.find(bib) == retDoms.end()) {
                        //The only blocker is not in the critical path from the entry to return, so it can be bypassed.
                        return true;
                    }
                    //Otherwise still need to see the next group for a different callee, if any.
                    continue;
                }else {
                    //If the potential blocker is not in a critical path then no need for another layer of recursion. 
                    BasicBlock *bib = (*callsiteBis.begin()).first->getParent();
                    if (retDoms.find(bib) == retDoms.end()) {
                        //The only blocker is not in the critical path from the entry to return, so it can be bypassed.
                        return true;
                    }
                    //Ok it's on the critical path, we need to know whether it's a true blocker, if not, still return true directly, 
                    //otherwise, this group is already killed, turn to the next group.
                    if (bypassCall((*callsiteBis.begin()).second, e+2)) {
                        return true;
                    }
                    continue;
                }
            }
            //Decide whether the potential callsite blockers are true...
            for (auto &cs : callsiteBis) {
                if (!bypassCall(cs.second,e+2)) {
                    //Ok this is a real blocker.
                    instBis.insert(cs.first);
                }
            }
            //At this point, we get all blockers in "instBis" (potential callsite blockers also finalized).
            //Try the optimization again before invoking the standard reachability test.
            if (instBis.size() == 0) {
                return true;
            }
            if (instBis.size() == 1 && !retDoms.empty()) {
                BasicBlock *bib = (*instBis.begin())->getParent();
                if (retDoms.find(bib) == retDoms.end()) {
                    return true;
                }
                continue;
            }
            //Ok finally the reachability test..
            if (isPotentiallyReachable(ei,nullptr,0,&instBis)) {
                return true;
            }
        }
        return false;
    }

    void InstLoc::getBlockersInCurrFunc(std::set<InstLoc*> *blocklist, std::set<Instruction*> &validBis) {
        if (!blocklist || blocklist->empty()) {
            return;
        }
        if (!this->hasCtx()) {
            return;
        }
        std::map<Instruction*, std::set<InstLoc*>> callsiteBis;
        for (InstLoc *bi : *blocklist) {
            if (bi && bi->hasCtx()) {
                int r = this->isCtxPrefix(bi);
                if (r == 0) {
                    //The blocking inst is in exactly the same host function w/ the same calling context as "this".
                    if (dyn_cast<Instruction>(bi->inst)) {
                        validBis.insert(dyn_cast<Instruction>(bi->inst));
                    }
                }else if (r > 0) {
                    //While the blocker is not in the same ctx and function as "this", one of its up level callsite is..
                    //So we need to further inspect whether this callsite can block our way (e.g. the blocking inst post-dominates this callsite).
                    if ((*bi->ctx)[r]) {
                        callsiteBis[(*bi->ctx)[r]].insert(bi);
                    }
                }
            }
        }
        //Start to inspect the callsites who can lead to blocking insts to see whether they can be bypassed (i.e. there is one path from 
        //the callsite to the return w/o triggering the underlying blocking insts), if not, 
        //these callsites also need to be regarded as blocking insts.
        for (auto &e : callsiteBis) {
            Instruction *cs = e.first;
            std::set<InstLoc*> &bis = e.second;
            //Some sanity check..
            if (!cs || !cs->getParent() || cs->getFunction() != this->getFunc()) {
                continue;
            }
            if (!bypassCall(bis,this->ctx->size()+1)) {
                validBis.insert(cs);
            }
        }
        return;
    }

    //Decide whether "this" can be reached from the entry of its host function when there exists some blocking nodes.
    bool InstLoc::canReachEnd(std::set<InstLoc*> *blocklist, bool fromEntry) {
        //First see whether there are any blocking insts within the same function and calling contexts as "this", if none, return true directly.
        std::set<Instruction*> validBis;
        this->getBlockersInCurrFunc(blocklist,validBis);
        if (validBis.empty()) {
            return true;
        }
        //Ok there are some blocking insts, we need to traverse all possible paths.
        Instruction *ei = dyn_cast<Instruction>(this->inst);
        if (!ei || !ei->getParent()) {
            //In case "this" is a inst created by ourselves or a simple var.
            return true;
        }
        if (fromEntry) {
            return isPotentiallyReachable(nullptr, ei, 0, &validBis);
        }
        return isPotentiallyReachable(ei, nullptr, 0, &validBis);
    }

    bool BBTraversalHelper::isReachable(Instruction *startInstr, Instruction *endInstr,
                                        std::vector<Instruction*> *callSites) {
        /***
         * Check if endInst is reachable from startInstr following the call sites
         * in the provided vector.
         */

        // both belong to the same function.
        if(startInstr->getParent()->getParent() == endInstr->getParent()->getParent()) {
            return isPotentiallyReachable(startInstr, endInstr, 0);
        }

        // OK, both instructions belongs to different functions.
        // we need to find if startInstr can reach the
        // call instruction that resulted in invocation of the function of
        // endInstr
        assert(callSites->size() > 0 && "How can this be possible? we have 2 instructions, that belong to "
                                                "different functions, yet the call sites stack is empty");

        Instruction *newEndInstr;
        for(long i=(callSites->size() - 1);i>=0; i--) {
            newEndInstr = (*callSites)[i];
            if(newEndInstr->getParent()->getParent() == startInstr->getParent()->getParent()) {
                if(isPotentiallyReachable(startInstr, newEndInstr, 0)) {
                    return true;
                }
            }
        }
        return false;
    }

    llvm::DominatorTree *BBTraversalHelper::getDomTree(llvm::Function* pfunc) { 
        //The mapping from one Func to its dominator tree;
        static std::map<llvm::Function*,llvm::DominatorTree*> domMap;
        if (!pfunc) {
            return nullptr;
        }
        if (domMap.find(pfunc) == domMap.end()) {
            llvm::DominatorTree *pdom = new llvm::DominatorTree(*pfunc);
            domMap[pfunc] = pdom;
        }
        return domMap[pfunc];
    }

    void BBTraversalHelper::getDominators(llvm::BasicBlock *bb, std::set<llvm::BasicBlock*> &res, bool self) {
        if (!bb || !bb->getParent()) {
            return;
        }
        llvm::DominatorTree *domT = BBTraversalHelper::getDomTree(bb->getParent());
        if (!domT) {
            return;
        }
        DomTreeNodeBase<BasicBlock> *dtn = domT->getNode(bb);
        while (dtn->getIDom()) {
            dtn = dtn->getIDom();
            res.insert(dtn->getBlock());
        }
        if (self) {
            res.insert(bb);
        }
        return;
    }

    void getAllSuccsInDomTree(DomTreeNodeBase<BasicBlock> *dtn, std::set<llvm::BasicBlock*> &res) {
        if (!dtn) {
            return;
        }
        for (auto n : *dtn) {
            if (n) {
                res.insert(n->getBlock());
                getAllSuccsInDomTree(n,res);
            }
        }
        return;
    }

    void BBTraversalHelper::getDominatees(llvm::BasicBlock *bb, std::set<llvm::BasicBlock*> &res, bool self) {
        if (!bb || !bb->getParent()) {
            return;
        }
        llvm::DominatorTree *domT = BBTraversalHelper::getDomTree(bb->getParent());
        if (!domT) {
            return;
        }
        DomTreeNodeBase<BasicBlock> *dtn = domT->getNode(bb);
        getAllSuccsInDomTree(dtn,res);
        if (self) {
            res.insert(bb);
        }
        return;
    }

    void BBTraversalHelper::getRetBBs(llvm::Function* pfunc, std::set<llvm::BasicBlock*> &r) {
        if (!pfunc) {
            return;
        }
        for (llvm::BasicBlock &bb : *pfunc) {
            if (getSuccNum(&bb) == 0) {
                r.insert(&bb);
            }
        }
        return;
    }

    void BBTraversalHelper::getRetInsts(llvm::Function* pfunc, std::set<llvm::Instruction*> &r) {
        if (!pfunc) {
            return;
        }
        std::set<llvm::BasicBlock*> bbs;
        BBTraversalHelper::getRetBBs(pfunc,bbs);
        for (llvm::BasicBlock *bb : bbs) {
            if (bb) {
                r.insert(&(bb->back()));
            }
        }
        return;
    }

    void BBTraversalHelper::getDomsForRet(llvm::Function* pfunc, std::set<llvm::BasicBlock*> &r) {
        if (!pfunc) {
            return;
        }
        //Ok, first get all ret nodes (i.e. #succ = 0).
        std::set<llvm::BasicBlock*> rets;
        BBTraversalHelper::getRetBBs(pfunc,rets);
        //Get dominators for all ret nodes.
        r.clear();
        std::set<llvm::BasicBlock*> t;
        for (llvm::BasicBlock *bb : rets) {
            t.clear();
            BBTraversalHelper::getDominators(bb,t);
            if (r.empty()) {
                r.insert(t.begin(),t.end());
            }else {
                //Keep the intersection of "t" and "r" in "r".
                for (auto it = r.begin(); it != r.end(); ) {
                    if (t.find(*it) == t.end()) {
                        it = r.erase(it);
                    }else {
                        ++it;
                    }
                }
            }
        }
        return;
    }

    llvm::PostDominatorTree *BBTraversalHelper::getPostDomTree(llvm::Function* pfunc) { 
        //The mapping from one Func to its post-dominator tree;
        static std::map<llvm::Function*,llvm::PostDominatorTree*> postDomMap;
        if (!pfunc) {
            return nullptr;
        }
        if (postDomMap.find(pfunc) == postDomMap.end()) {
            llvm::PostDominatorTree *pdom = new llvm::PostDominatorTree(*pfunc);
            postDomMap[pfunc] = pdom;
        }
        return postDomMap[pfunc];
    }

    //Some code are borrowed from llvm 11.0, since lower version llvm may not have "dominates()" for two instructions. 
    bool BBTraversalHelper::instPostDom(Instruction *src, Instruction *end, bool is_strict) {
        if (!end || !src || end->getFunction() != src->getFunction()) {
            return false;
        }
        BasicBlock *bsrc = src->getParent();
        BasicBlock *bend = end->getParent();
        if (bsrc != bend) {
            Function *func = end->getFunction();
            llvm::PostDominatorTree *pdom = BBTraversalHelper::getPostDomTree(func);
            if (!pdom) {
                return false;
            }
            return pdom->dominates(bend,bsrc);
        }
        //Ok they are within the same BB, we simply look at their relative order.
        if (src == end) {
            return !is_strict;
        }
        // PHINodes in a block are unordered.
        if (isa<PHINode>(src) && isa<PHINode>(end))
            return false;
        // Loop through the basic block until we find I1 or I2.
        BasicBlock::const_iterator I = bsrc->begin();
        for (; &*I != src && &*I != end; ++I);
        //If src comes before end in a same BB, then end post-dom src.
        return &*I == src;
    }

    void InstLoc::print(raw_ostream &O) {
        if (this->inst) {
            //First print the inst.
            if (dyn_cast<Instruction>(this->inst)) {
                InstructionUtils::printInst(dyn_cast<Instruction>(this->inst),O);
            }else {
                O << InstructionUtils::getValueStr(this->inst) << "\n";
            }
            //Then print the calling context by the function names.
            if (this->ctx && this->ctx->size() > 0) {
                O << "[";
                std::string lastFunc;
                for (Instruction *inst : *this->ctx) {
                    if (inst && inst->getParent() && inst->getFunction()) {
                        std::string func = inst->getFunction()->getName().str();
                        //TODO: self-recursive invocation
                        if (func != lastFunc) {
                            O << func << " -> ";
                            lastFunc = func;
                        }
                    }
                }
                O << "]\n";
            }
        }
    }

    void InstLoc::print_light(raw_ostream &O, bool lbreak) {
        if (this->inst) {
            O << InstructionUtils::getValueStr(this->inst);
            O << " (";
            InstructionUtils::printCallingCtx(O,this->ctx,false);
            O << ")";
        }
        if (lbreak) {
            O << "\n";
        }
    }

    //Different from the normal post-dom algorithm for two instructions within a same function, here we consider
    //the post-dom relationship for two InstLoc (i.e. instructions plus their full calling contexts), so if InstLoc A
    //post-dom InstLoc B, that means all execution flows from InstLoc B will eventually reach InstLoc A w/ its specific
    //calling contexts.
    bool InstLoc::postDom(InstLoc *other, bool is_strict) {
        if (!other) {
            return false;
        }
        //(1) First identify the common prefix of the calling contexts, if none, then obviously no post-dom relationship,
        //if any, then the question is converted to "whether this inst post-dom the call site of 'other' in the common prefix".
        if (!this->hasCtx()) {
            //This means current InstLoc is outside of any functions (e.g. a preset global variable), so no way it can post-dominate "other".
            return false;
        }
        int ip = 0;
        if (other->hasCtx()) {
            //Both "this" and "other" has some contexts.
            //NOTE 1: the structure of the calling context is "entry inst -> call site -> entry inst -> call site -> ...", 
            //so odd ctx index indicates
            //a call inst.
            //NOTE 2: the total size of a calling context must be odd. (i.e. it must end w/ the entry inst of the callee).
            assert(this->ctx->size() % 2);
            assert(other->ctx->size() % 2);
            while (ip < this->ctx->size() && ip < other->ctx->size() && (*this->ctx)[ip] == (*other->ctx)[ip] && ++ip);
            if (ip == 0) {
                //Both have calling contexts but no common prefix... This means the top-level entry functions are different, no way to post-dom.
                return false;
            }
            //The two calling contexts diverges at a certain point, here we have different situations:
            //1. They diverge within a same caller.
            //1.1. "this" takes callee A while "other" takes callee B.
            //1.2. "this" is just a normal inst within the caller and "other" takes callee B.
            //1.3. "this" takes callee A while "other" is a normal inst
            //1.4. both are normal inst
            //For 1. we need to first see whether "this" post-doms "other" within the common caller, if not return false immediately, otherwise
            //we need to further inspect the remaining part of "this" calling context to see whether it *must* end w/ this->inst.
            //2. They diverge at a same call site and take different callees (e.g. an indirect call), in this case "this" cannot post-dom "other".
            if (ip >= this->ctx->size()) {
                //This must be case 1.2. or 1.4., since there are no further context for "this", no need for further inspect.
                Instruction *end = dyn_cast<Instruction>(this->inst);
                Instruction *src = dyn_cast<Instruction>(other->inst);
                if (ip < other->ctx->size()) {
                    src = (*other->ctx)[ip];
                }
                if (!end || !src || end->getFunction() != src->getFunction()) {
                    //Is this possible?
#ifdef DEBUG_INTER_PROC_POSTDOM
                    dbgs() << "InstLoc::postDom(): !end || !src || end->getFunction() != src->getFunction() - 0\n"; 
#endif
                    return false;
                }
                //NOTE: the "is_strict" only makes sense when two InstLoc are exactly the same, if that happens here is the only point we can reach
                //and need to honor the "is_strict" flag in "instPostDom".
                return BBTraversalHelper::instPostDom(src,end,is_strict);
            }
            if (ip >= other->ctx->size()) {
                //This must be case 1.3. We may still need to inspect the remaining "this" context.
                Instruction *src = dyn_cast<Instruction>(other->inst);
                Instruction *end = dyn_cast<Instruction>((*this->ctx)[ip]);
                if (!end || !src || end->getFunction() != src->getFunction()) {
                    //Is this possible?
#ifdef DEBUG_INTER_PROC_POSTDOM
                    dbgs() << "InstLoc::postDom(): !end || !src || end->getFunction() != src->getFunction() - 1\n"; 
#endif
                    return false;
                }
                if (!BBTraversalHelper::instPostDom(src,end)) {
                    return false;
                }
            }else {
                //Ok, the common prefix are well contained in both contexts, it may be case 1.1. or 2., we can differentiate them by index oddness. 
                if (ip % 2) {
                    //case 2, return false directly.
                    return false;
                }
                //case 1.1., we may still need further inspect.
                if (!BBTraversalHelper::instPostDom((*other->ctx)[ip],(*this->ctx)[ip])) {
                    return false;
                }
            }
            ++ip;
        }
        //(2) Then we need to decide the post-dom relationship between the caller entrance and callee invocation site of each function
        //in the remaining calling context (beside the common prefix) of "this".
        //NOTE: at this point "ip" must be the index of an entry inst in "this" calling context.
        assert(!(ip % 2));
        assert(ip < this->ctx->size());
        while (ip + 1 < this->ctx->size()) {
            if (!BBTraversalHelper::instPostDom((*this->ctx)[ip],(*this->ctx)[ip+1])) {
                return false;
            }
            ++ip;
        }
        Instruction *end = dyn_cast<Instruction>(this->inst);
        if (end && !BBTraversalHelper::instPostDom((*this->ctx)[ip],end)) {
            return false;
        }
        return true;
    }

    //Decide whether current inst can be reached from (or return to) its one specified upward callsite (denoted by the
    //index "ci" in its calling context), in the presence of the blocking insts in the "blocklist".
    bool InstLoc::chainable(int ci, std::set<InstLoc*> *blocklist, bool callFrom) {
        if (!blocklist || blocklist->empty()) {
            //Without blocking nodes it's easily reachable/returnable if we don't consider the static dead code, which should be rare..
            return true;
        }
        if (!this->hasCtx()) {
            return true;
        }
        assert(this->ctx->size() % 2);
        //Align ci to always be the callsite index in the calling context where we want to call/return from/to.
        if (ci < 0) {
            ci = 1;
        }else if (ci % 2 == 0) {
            //"ci" indexes an entry inst of a function, re-point it to the next callsite.
            ++ci;
        }else {
            //"ci" indexes a callsite, start from the callsite in the callee.
            ci += 2;
        }
        if (callFrom) {
            //Decide the reachability in each segment of the call chain.
            for (;ci < this->ctx->size(); ci += 2) {
                Instruction *I = (*this->ctx)[ci];
                if (I && I->getParent()) { 
                    std::vector<Instruction*> newCtx(this->ctx->begin(), this->ctx->begin()+ci);
                    InstLoc il(I,&newCtx);
                    if (!il.canReachEnd(blocklist,true)) {
                        return false;
                    }
                }
            }
            //The final segment.
            return this->canReachEnd(blocklist,true);
        }else {
            //First decide whether current end inst can return to the up-level.
            if (!this->canReachEnd(blocklist,false)) {
                return false;
            }
            for (int i = this->ctx->size() - 2; i >= ci; --i) {
                Instruction *I = (*this->ctx)[i];
                if (I && I->getParent()) { 
                    std::vector<Instruction*> newCtx(this->ctx->begin(), this->ctx->begin()+i);
                    InstLoc il(I,&newCtx);
                    if (!il.canReachEnd(blocklist,false)) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    //Whether "other" can reach "this", inter-procedually.
    bool InstLoc::reachable(InstLoc *other, std::set<InstLoc*> *blocklist) {
        //NOTE: if "other" is nullptr or has a null ctx, we treat it as a global position.
        if (!other || !other->hasCtx()) {
            //This means the "other" is a global var and and in theory can reach every inst inside functions,
            //but still we need to consider whether the blocklist (if any) is in the way.
            if (!blocklist || blocklist->empty()) {
                return true;
            }
            //There does exist some blockers.
            if (this->hasCtx()) {
                return this->chainable(0,blocklist,true);
            }else {
                //TODO: both are gloabl vars, what's the definition of the "reachability" then...
                return true;
            }
        }
        if (!this->hasCtx()) {
            //"this" is a global var but "other" isn't, obviously "other" cannot reach "this" reversally.
            return false;
        }
        assert(this->ctx->size() % 2);
        assert(other->ctx->size() % 2);
        //Ok, both contexts exist, decide whether "other" can reach "this" from its current context.
        //Get the first divergence point in the call chains of both.
        int ip = 0;
        while (ip < this->ctx->size() && ip < other->ctx->size() && (*this->ctx)[ip] == (*other->ctx)[ip] && ++ip);
        if (ip == 0) {
            //Different top-level entry function, not reachable.
            return false;
        }
        //The two calling contexts diverges at a certain point, here we have different situations:
        //1. They diverge within a same caller.
        //1.1. "this" takes callee A while "other" takes callee B.
        //1.2. "this" is just a normal inst within the caller and "other" takes callee B.
        //1.3. "this" takes callee A while "other" is a normal inst
        //1.4. both are normal inst
        //For 1. we need to see whether "this" is reachable from "other" within the common caller, if so return true, otherwise false.
        //2. They diverge at a same call site and take different callees (e.g. an indirect call), 
        //in this case "this" cannot be reached from "other".
        Instruction *end = nullptr, *src = nullptr;
        if (ip >= this->ctx->size()) {
            //Case 1.2. or 1.4.
            //First make sure that "other" can successfully return to the callsite within current caller.
            if (blocklist && !blocklist->empty() && ip < other->ctx->size() && !other->chainable(ip,blocklist,false)) {
                //This is case 1.2. and "other" cannot successfully return.
                return false;
            }
            //Then we can only consider the intra-procedural reachability.
            src = dyn_cast<Instruction>(other->inst);
            if (ip < other->ctx->size()) {
                src = (*other->ctx)[ip];
            }
            end = dyn_cast<Instruction>(this->inst);
        }else if (ip >= other->ctx->size()) {
            //Case 1.3.
            //First make sure "this" can be reached from the call site within current caller.
            if (blocklist && !blocklist->empty() && !this->chainable(ip,blocklist,true)) {
                return false;
            }
            //Then intra-procedural reachability.
            src = dyn_cast<Instruction>(other->inst);
            end = (*this->ctx)[ip];
        }else if (ip % 2) {
            //Case 1.1.
            //First make sure "other" can return *and* "this" can be reached...
            if (blocklist && !blocklist->empty() && (!other->chainable(ip,blocklist,false) || !this->chainable(ip,blocklist,true))) {
                return false;
            }
            //Then intra-procedural reachability.
            src = (*other->ctx)[ip];
            end = (*this->ctx)[ip];
        }else {
            //Case 2.
            return false;
        }
        if (!end || !src || !end->getParent() || !src->getParent() || end->getFunction() != src->getFunction()) {
            //Is this possible?
            //assert(false);
            dbgs() << "!!! InstLoc::reachable(): src and end are not normal insts within the same function: src: ";
            dbgs() << InstructionUtils::getValueStr(src) << " end: " << InstructionUtils::getValueStr(end) << "\n";
            return false;
        }
        //Finally the reachability test between "src" and "end" intra-procedurally.
        //First we need to finalize the blocker list wirthin current function (e.g. some callsites may also be blockers).
        std::set<Instruction*> validBis;
        if (blocklist && !blocklist->empty()) {
            std::vector<Instruction*> newCtx(this->ctx->begin(), (ip < this->ctx->size() ? this->ctx->begin()+ip : this->ctx->end()));
            InstLoc il(src,&newCtx);
            il.getBlockersInCurrFunc(blocklist,validBis);
        }
        //Do the test.
        return isPotentiallyReachable(src,end,0,&validBis);
    }

    void printInstlocJson(InstLoc *inst, llvm::raw_ostream &O) {
        if (!inst) {
            return;
        }
        if (inst->inst && dyn_cast<Instruction>(inst->inst)) {
            InstructionUtils::printInstJson(dyn_cast<Instruction>(inst->inst),O);
        }else {
            O << "\"instr\":\"" << InstructionUtils::escapeValueString(inst->inst) << "\"";
        }
        //Any tag pointer attached to the InstLoc for debugging?
        if (inst->p0) {
            O << ",\"tag\":\"" << (const void*)inst->p0 << "\",\"tf\":\"" << (const void*)(inst->p1)
            << "\",\"icnt\":" << inst->icnt;
        }
        //Each inst in the trace also has its own calling context...
        if (inst->hasCtx()) {
            O << ",\"ctx\":[";
            bool comma = false;
            for (Instruction *ci : *inst->ctx) {
                if (ci) {
                    if (comma) {
                        O << ",";
                    }
                    O << "{";
                    InstructionUtils::printInstJson(ci,O);
                    O << "}";
                    comma = true;
                }
            }
            O << "]";
        }
        return;
    }

    void printInstlocTraceJson(std::vector<InstLoc*> *instTrace, llvm::raw_ostream &O) {
        O << "{" << "\"order\":" << getTrOrder(instTrace) << ",\"tr\":[";
        if (instTrace && !instTrace->empty()) {
            bool comma = false;
            for (InstLoc *inst : *instTrace) {
                if (!inst) {
                    continue;
                }
                if (comma) {
                    O << ",";
                }
                O << "{";
                printInstlocJson(inst,O);
                O << "}";
                comma = true;
            }
        }
        O << "]}";
        return;
    }

    void getCtxOfLocTr(const std::vector<InstLoc*> *tr, std::vector<std::vector<Instruction*>*> &res) {
        if (!tr) {
            return;
        }
        std::vector<Instruction*> *last = nullptr;
        for (InstLoc *il : *tr) {
            if (!il || !il->ctx) {
                continue;
            }
            if (!last || *last != *(il->ctx)) {
                res.push_back(il->ctx);
                last = il->ctx;
            }
        }
        return;
    }

    bool sameLocTr(std::vector<InstLoc*> *tr0, std::vector<InstLoc*> *tr1) {
        if (!tr0 != !tr1) {
            return false;
        }
        if (!tr0) {
            return true;
        }
        if (tr0->size() != tr1->size()) {
            return false;
        }
        for (int i = 0; i < tr0->size(); ++i) {
            if (!(*tr0)[i]->same((*tr1)[i])) {
                return false;
            }
        }
        return true;
    }

    int getTrOrder(std::vector<InstLoc*> *tr) {
        if (!tr || tr->empty()) {
            return 0;
        }
        int order = 1;
        for (int i = 0; i < tr->size() - 1; ++i) {
            if ((*tr)[i+1] && !(*tr)[i+1]->reachable((*tr)[i])) {
                ++order;
            }
        }
        return order;
    }

    std::map<BasicBlock*,std::set<BasicBlock*>> BBTraversalHelper::succ_map;

    void BBTraversalHelper::_get_all_successors(BasicBlock *bb, std::set<BasicBlock*> &res) {
        if (!bb || res.find(bb) != res.end()) {
            return;
        }
        //A result cache.
        if (BBTraversalHelper::succ_map.find(bb) != BBTraversalHelper::succ_map.end()) {
            res.insert(BBTraversalHelper::succ_map[bb].begin(),BBTraversalHelper::succ_map[bb].end());
            return;
        }
        //inclusive
        res.insert(bb);
        for (llvm::succ_iterator sit = llvm::succ_begin(bb), set = llvm::succ_end(bb); sit != set; ++sit) {
            BBTraversalHelper::_get_all_successors(*sit,res);
        }
        return;
    }

    //NOTE: this will be inclusive (the successor list also contains the root BB.)
    std::set<BasicBlock*> *BBTraversalHelper::get_all_successors(BasicBlock *bb) {
        if (!bb) {
            return nullptr;
        }
        //A result cache.
        if (BBTraversalHelper::succ_map.find(bb) != BBTraversalHelper::succ_map.end()) {
            return &BBTraversalHelper::succ_map[bb];
        }
        std::set<BasicBlock*> res;
        BBTraversalHelper::_get_all_successors(bb,res);
        BBTraversalHelper::succ_map[bb] = res;
        return &BBTraversalHelper::succ_map[bb];
    }


}
