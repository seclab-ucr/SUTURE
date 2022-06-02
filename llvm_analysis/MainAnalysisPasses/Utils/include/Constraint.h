#ifndef PROJECT_CONSTRAINT_H
#define PROJECT_CONSTRAINT_H

#include "InstructionUtils.h"
#include "z3++.h"

using namespace z3;

namespace DRCHECKER {

    //One context for all z3 solving tasks across the analysis.
    extern context z3c;

    //Given a pointer to anything (Value*, InstLocTr*, etc.), return
    //a unique z3 variable representing it.
    extern expr get_z3v_expr_bv(void *p);

    //Just return a trivial z3 variable.
    extern expr get_z3v();

    extern expr get_z3v_expr_int(void *p);

    // This class abstracts the path constraints posed to a certain variable, within one function. 
    // TODO: use std::shared_ptr to replace expr*, or avoid expr* altogether, or
    // consider to use expr_vector.
    class Constraint {
    public:

        Value *v = nullptr;
        Function *func = nullptr;
        std::map<BasicBlock*, expr*> cons;

        //Sometimes the constraint is only on an edge, e.g.,
        // if (a) do_sth; return;
        //while in the "do_sth" BB we have the constraint "a != 0", the "a == 0" constraint
        //only exists on the edge from the "br" to "return" BB, but not the "return" BB.
        //We record such edge constraints because they can be useful when we analyze the
        //constraints of a value resulted from a phi node, which conditionally merges values
        //from different edges.
        std::map<BasicBlock*, std::map<BasicBlock*, expr*>> cons_edge;

        //All BBs in which the value constraints are unsatisfiable.
        std::set<BasicBlock*> deadBBs;

        Constraint(Value *v, Function *func) {
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
            solver s(z3c);
            s.add(*e);
            //"sat", "unsat" or "unknown"
            bool is_sat = false;
            switch (s.check()) {
            case unsat: 
                break;
            default: 
                is_sat = true;
                break;
            }
            //Z3_finalize_memory();
            return is_sat;
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

        //Add a new constraint for the value on the edge from "b0" to "b1",
        //then returns true upon success, false otherwise.
        bool addEdgeConstraint(expr *con, BasicBlock *b0, BasicBlock *b1) {
            if (!con || !b0 || !b1) {
                return false;
            }
            //TODO: verifies that b1 is a successor of b0.
            if (this->deadBBs.find(b0) != this->deadBBs.end() ||
                this->deadBBs.find(b1) != this->deadBBs.end()) {
                //Already dead..
                return false;
            }
            if (this->cons_edge.find(b0) == this->cons_edge.end() ||
                this->cons_edge[b0].find(b1) == this->cons_edge[b0].end()) {
                expr *e = new expr(z3c);
                *e = *con;
                this->cons_edge[b0][b1] = e;
            } else {
                //This should be impossible..
                *(this->cons_edge[b0][b1]) = (*(this->cons_edge[b0][b1]) && *con);
            }
            return true;
        }

        expr *getEdgeConstraint(BasicBlock *b0, BasicBlock *b1) {
            if (!b0 || !b1) {
                return nullptr;
            }
            if (this->cons_edge.find(b0) == this->cons_edge.end() ||
                this->cons_edge[b0].find(b1) == this->cons_edge[b0].end()) {
                return nullptr;
            }
            return this->cons_edge[b0][b1];
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
                expr *e = new expr(z3c);
                *e = *con;
                this->cons[bb] = e;
            }else {
                //Combine the constraints w/ "and".
                *(this->cons[bb]) = (*(this->cons[bb]) && *con);
            }
            if (!this->satisfiable(this->cons[bb])) {
                //Simplify the constraint to "false".
                *(this->cons[bb]) = z3c.bool_val(false);
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
            expr ev = get_z3v_expr_bv((void*)this->v);
            expr e(z3c);
            bool first = true;
            for (int64_t i : vs) {
                expr t = (ev == z3c.bv_val(i, 64));
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
            expr ev = get_z3v_expr_bv((void*)this->v);
            expr e(z3c);
            bool first = true;
            for (int64_t i : vs) {
                expr t = (ev != z3c.bv_val(i, 64));
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
            expr ev = get_z3v_expr_bv((void*)this->v);
            expr e(z3c);
            switch (pred) {
                case CmpInst::Predicate::ICMP_EQ:
                    return ev == z3c.bv_val(sc, 64);
                case CmpInst::Predicate::ICMP_NE:
                    return ev != z3c.bv_val(sc, 64);
                case CmpInst::Predicate::ICMP_UGT:
                    return ugt(ev, z3c.bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_UGE:
                    return uge(ev, z3c.bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_ULT:
                    return ult(ev, z3c.bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_ULE:
                    return ule(ev, z3c.bv_val(uc, 64));
                case CmpInst::Predicate::ICMP_SGT:
                    return ev > z3c.bv_val(sc, 64);
                case CmpInst::Predicate::ICMP_SGE:
                    return ev >= z3c.bv_val(sc, 64);
                case CmpInst::Predicate::ICMP_SLT:
                    return ev < z3c.bv_val(sc, 64);
                case CmpInst::Predicate::ICMP_SLE:
                    return ev <= z3c.bv_val(sc, 64);
                default:
                    break;
            }
            // Default
            return z3c.bool_val(true);
        }

    private:
        //
    };

} //namespace

#endif //PROJECT_CONSTRAINT_H
