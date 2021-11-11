#ifndef PROJECT_CONSTRAINT_H
#define PROJECT_CONSTRAINT_H

#include "InstructionUtils.h"
#include "z3++.h"

using namespace z3;

namespace DRCHECKER {

    // This class abstracts the path constraints posed to a certain variable, within one function. 
    class Constraint {
    public:

        Value *v = nullptr;
        Function *func = nullptr;

        context *z3c = nullptr;
        solver *z3s = nullptr;
        expr *zv = nullptr;

        std::map<BasicBlock*, expr*> cons;

        //All BBs in which the value constraints are unsatisfiable.
        std::set<BasicBlock*> deadBBs;

        Constraint(Value *v, Function *func) {
            this->v = v;
            this->func = func;
            this->z3c = new context();
            //We need to map the llvm value to the z3 domain.
            //For now we simply create a z3 integer for all llvm vars.
            //TODO: consider different z3 counterparts for different llvm vars.
            this->zv = new expr(*(this->z3c));
            *(this->zv) = this->z3c->bv_const("v",64);
            this->z3s = new solver(*(this->z3c));
        }

        //Make a copy of "c", but w/ value and function replaced and existing constraints removed.
        Constraint(Constraint *c, Value *v, Function *func) {
            assert(c);
            this->z3c = c->z3c;
            this->z3s = c->z3s;
            this->zv = c->zv;
            this->v = v;
            this->func = func;
        }

        ~Constraint() {
            //
        }

        bool satisfiable(expr *e) {
            if (!e) {
                return false;
            }
            this->z3s->reset();
            this->z3s->add(*e);
            //"sat", "unsat" or "unknown"
            switch (this->z3s->check()) {
            case unsat: return false;
            default: return true;
            }
            return false;
        }

        expr *getConstraint(BasicBlock *bb) {
            if (!bb) {
                return nullptr;
            }
            if (this->cons.find(bb) != this->cons.end()) {
                return this->cons[bb];
            }
            return nullptr;
        }

        //Add a new constraint for the value in a certain BB, then returns whether for this BB the
        //value constraint can be satisfied.
        bool addConstraint(expr *con, BasicBlock *bb) {
            if (!con || !bb) {
                return true;
            }
            if (this->deadBBs.find(bb) != this->deadBBs.end()) {
                //Already dead..
                return false;
            }
            if (this->cons.find(bb) == this->cons.end()) {
                expr *e = new expr(*(this->z3c));
                *e = *con;
                this->cons[bb] = e;
            }else {
                //Combine the constraints w/ "and".
                *(this->cons[bb]) = (*(this->cons[bb]) && *con);
            }
            if (!this->satisfiable(this->cons[bb])) {
                //Simplify the constraint to "false".
                *(this->cons[bb]) = this->z3c->bool_val(false);
                this->deadBBs.insert(bb);
                return false;
            }
            return true;
        }

        //Add the constraint to all basic blocks in the host function.
        void addConstraint2AllBBs(expr *con) {
            if (!this->func || !con) {
                return;
            }
            for (BasicBlock &bb : *(this->func)) {
                this->addConstraint(con,&bb);
            }
            return;
        }

        //Add the constraint to some specified basic blocks in the host function.
        void addConstraint2BBs(expr *con, std::set<BasicBlock*> &bbs) {
            if (!con || bbs.empty()) {
                return;
            }
            for (BasicBlock *bb : bbs) {
                this->addConstraint(con,bb);
            }
            return;
        }

        //Return an expr that is true when "zv" is equal to any value in "vs".
        expr getEqvExpr(std::set<int64_t> &vs) {
            if (!this->zv) {
                return this->z3c->bool_val(true);
            }
            expr e(*(this->z3c));
            bool first = true;
            for (int64_t i : vs) {
                expr t = (*(this->zv) == this->z3c->bv_val(i, 64));
                if (first) {
                    e = t;
                    first = false;
                }else {
                    e = (e || t);
                }
            }
            return e;
        }

        //Return an expr that is true when "zv" is not equal to any value in "vs".
        expr getNeqvExpr(std::set<int64_t> &vs) {
            if (!this->zv) {
                return this->z3c->bool_val(true);
            }
            expr e(*(this->z3c));
            bool first = true;
            for (int64_t i : vs) {
                expr t = (*(this->zv) != this->z3c->bv_val(i, 64));
                if (first) {
                    e = t;
                    first = false;
                }else {
                    e = (e && t);
                }
            }
            return e;
        }

        //This is a more general function, given an cmp operator (e.g., >, <) and a signed/unsigned integer,
        //return the expr for "zv" accordingly (zv > C).
        expr getExpr(CmpInst::Predicate pred, int64_t sc, uint64_t uc) {
            if (this->zv) {
                expr e(*(this->z3c));
                switch(pred) {
                case CmpInst::Predicate::ICMP_EQ:
                    return (*(this->zv) == this->z3c->bv_val(sc, 64));
                case CmpInst::Predicate::ICMP_NE:
                    return (*(this->zv) != this->z3c->bv_val(sc, 64));
                case CmpInst::Predicate::ICMP_UGT:
                    return ugt(*(this->zv), this->z3c->bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_UGE:
                    return uge(*(this->zv), this->z3c->bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_ULT:
                    return ult(*(this->zv), this->z3c->bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_ULE:
                    return ule(*(this->zv), this->z3c->bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_SGT:
                    return (*(this->zv) > this->z3c->bv_val(sc, 64));
                case CmpInst::Predicate::ICMP_SGE:
                    return (*(this->zv) >= this->z3c->bv_val(sc, 64));
                case CmpInst::Predicate::ICMP_SLT:
                    return (*(this->zv) < this->z3c->bv_val(sc, 64));
                case CmpInst::Predicate::ICMP_SLE:
                    return (*(this->zv) <= this->z3c->bv_val(sc, 64));
                }
            }
            //Default
            return this->z3c->bool_val(true);
        }

    private:
        //
    };

} //namespace

#endif //PROJECT_CONSTRAINT_H
