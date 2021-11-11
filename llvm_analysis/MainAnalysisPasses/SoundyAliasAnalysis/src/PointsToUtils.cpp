//
// Created by machiry on 12/6/16.
//

#include "PointsToUtils.h"
#include "../../Utils/include/InstructionUtils.h"

using namespace llvm;

namespace DRCHECKER {
#define DEBUG_FUNCTION_PTR_ALIASING

    std::set<PointerPointsTo*>* PointsToUtils::getPointsToObjects(GlobalState &currState,
                                                                  std::vector<Instruction *> *currFuncCallSites,
                                                                  Value *srcPointer) {
        // Get points to objects set of the srcPointer at the entry of the instruction
        // currInstruction.
        // Note that this is at the entry of the instruction. i.e INFLOW.
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = currState.getPointsToInfo(currFuncCallSites);
        // Here srcPointer should be present in points to map.
        if(targetPointsToMap->find(srcPointer) != targetPointsToMap->end()) {
            return (*targetPointsToMap)[srcPointer];
        }
        return nullptr;

    }

    bool PointsToUtils::hasPointsToObjects(GlobalState &currState,
                                           std::vector<Instruction *> *currFuncCallSites,
                                           Value *srcPointer) {
        /***
         * Check if the srcPointer has any pointto objects at currInstruction
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = currState.getPointsToInfo(currFuncCallSites);
        return targetPointsToMap != nullptr &&
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end();
    }

    bool PointsToUtils::getTargetFunctions(GlobalState &currState, std::vector<Instruction*> *currFuncCallSites,
                                           Value *srcPointer, std::set<Function*> &dstFunctions) {
        // first get the type of the function we are looking for.
        // NOTE: what we get here is a function *pointer* type, but what it's compared to later (i.e. targetFunction->getType())
        // is actually also a function pointer type, that means, by default a llvm function's type is a pointer.
#ifdef DEBUG_FUNCTION_PTR_ALIASING
        dbgs() << "PointsToUtils::getTargetFunctions(): retrieve target functions for pointer: " 
        << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
        Type *targetFunctionType = srcPointer->getType();
        bool retVal = false;
        // get points to information, handling casts.
        std::set<PointerPointsTo*>* basePointsTo = PointsToUtils::getPointsToObjects(currState, currFuncCallSites,
                                                                                     srcPointer);
        if(basePointsTo == nullptr) {
            basePointsTo = PointsToUtils::getPointsToObjects(currState, currFuncCallSites,
                                                             srcPointer->stripPointerCasts());
        }
        // OK, we have some points to information for the srcPointer.
        if(basePointsTo != nullptr) {
            for(PointerPointsTo *currPointsTo: *(basePointsTo)) {
                // OK, this is a global object.
                if(currPointsTo && currPointsTo->targetObject && currPointsTo->targetObject->isGlobalObject()) {
                    // Check if it is function.
                    GlobalObject *currGlobObj = (GlobalObject*)(currPointsTo->targetObject);
                    Function *targetFunction = dyn_cast<Function>(currGlobObj->targetVar);
                    if(targetFunction != nullptr) {
                        if (InstructionUtils::same_types(targetFunction->getType(), targetFunctionType, true)) {
                            retVal = true;
                            dstFunctions.insert(targetFunction);
#ifdef DEBUG_FUNCTION_PTR_ALIASING
                            dbgs() << "Found Target Function: " << targetFunction->getName() << "\n";
#endif
                        } else {
#ifdef DEBUG_FUNCTION_PTR_ALIASING
                            dbgs() << "!!! Function pointer points to a function whose type does not match the pointer type: "
                            << "expected: " << InstructionUtils::getTypeStr(targetFunctionType)
                            << " actual: " << InstructionUtils::getTypeStr(targetFunction->getType()) << "\n";
#endif
                        }
                    }
                }
            }
        }
        return retVal;
    }

    bool PointsToUtils::getAllAliasObjects(GlobalState &currState, std::vector<Instruction *> *currFuncCallSites,
                            Value *srcPointer,
                            std::set<AliasObject*> &dstObjects) {
        std::set<PointerPointsTo*>* pointsToSet = PointsToUtils::getPointsToObjects(currState,
                                                                                    currFuncCallSites, srcPointer);
        bool addedAtleastOne = false;
        if(pointsToSet != nullptr) {
            for(auto currp:*pointsToSet) {
                // if the current object is not present?
                // then add the object into the dstObjects.
                if(dstObjects.find(currp->targetObject) == dstObjects.end()) {
                    dstObjects.insert(currp->targetObject);
                    addedAtleastOne = true;
                }
            }
        }
        return addedAtleastOne;
    }

    bool PointsToUtils::getTargetObjects(std::set<PointerPointsTo*> *dstPointsTo, std::set<std::pair<long, AliasObject*>> &targetObjects) {
        if (!dstPointsTo || dstPointsTo->empty()) {
            return false;
        }
        for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject *dstObj = currPointsToObj->targetObject;
            auto to_check = std::make_pair(target_field, dstObj);
            if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                targetObjects.insert(targetObjects.end(), to_check);
            }
        }
        return true;
    }

};
