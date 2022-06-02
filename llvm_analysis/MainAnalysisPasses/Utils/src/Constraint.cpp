#include "Constraint.h"

using namespace z3;

namespace DRCHECKER {
    //One context for all z3 solving tasks across the analysis.
    context z3c;

    //Given a pointer to anything (Value*, InstLocTr*, etc.), return
    //a unique z3 variable representing it.
    expr get_z3v_expr_bv(void *p) {
        return z3c.bv_const(std::to_string((long)p).c_str(), 64);
    }

    //Just return a trivial z3 variable.
    expr get_z3v() {
        return z3c.bv_const("v", 64);
    }

    expr get_z3v_expr_int(void *p) {
        return z3c.int_const(std::to_string((long)p).c_str());
    }
}