/*@
Copyright (c) 2013-2014, Su Zhenyu steven.known@gmail.com
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the Su Zhenyu nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED "AS IS" AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
@*/
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "ggc.h"
#include "tree.h"
#include "rtl.h"
#include "output.h"
#include "basic-block.h"
#include "diagnostic.h"
#include "tree-flow.h"
#include "toplev.h"
#include "tree-dump.h"
#include "timevar.h"
#include "cfgloop.h"
#include "tree-chrec.h"
#include "tree-data-ref.h"
#include "tree-scalar-evolution.h"
#include "tree-pass.h"
#include "domwalk.h"
#include "value-prof.h"
#include "pointer-set.h"
#include "gimple.h"
#include "params.h"
#include "opts.h"

#ifdef HAVE_cloog
#include "cloog/cloog.h"
#include "ppl_c.h"
#include "sese.h"
#include "graphite-ppl.h"
#include "graphite.h"
#include "graphite-poly.h"
#include "graphite-dependences.h"

#include "btcode/ltype.h"
#include "btcode/comf.h"
#include "btcode/smempool.h"
#include "btcode/rational.h"
#include "btcode/flty.h"
#include "btcode/sstl.h"
#include "btcode/bs.h"
#include "btcode/sgraph.h"
#include "btcode/xmat.h"
#include "btcode/linsys.h"
#include "btcode/lpsol.h"

using namespace xcom;

#include "btcode/depvecs.h"
#include "btcode/poly.h"
#include "btcode/ldtran.h"

#include "tran_gcc_graphite.h"

//This file is an example to use xpoly as an loop transformation tool.

#define DUMP_FILE_NAME "dumpoly.tmp"

static CHAR const*  g_bitnames[] = {
    "fallthru",
    "ab",
    "abcall",
    "eh",
    "fake",
    "dfs_back",
    "can_fallthru",
    "irreducible",
    "sibcall",
    "loop_exit",
    "true",
    "false",
    "exec"
};


//
//START GPOLY
//
void GPOLY::dump_arr_base(poly_bb * pbb, FILE * h, INT indent)
{
    AccMgr * mgr = POLY_acc_mgr(*this);
    if (mgr == NULL) {
        return;
    }
    fprintf(h, "\n");
    for (INT i = 0; i <= mgr->get_max_arr_base_id(); i++) {
        List<AccMat*> * lst = mgr->mapArrayId2Refs(i);
        if (lst != NULL) {
            fprintf(h, "\nARRAY_BASE(%d) : ", i);
            poly_dr_p pdr;
            for (UINT j = 0; VEC_iterate(poly_dr_p, PBB_DRS(pbb), j, pdr);
                 j++) {
                if (PDR_BASE_OBJECT_SET(pdr) == i) {
                    struct data_reference * dr =
                                (data_reference_p)PDR_CDR(pdr);
                    print_generic_stmt(h, DR_REF(dr), 0);
                    fprintf(h, "\tBASE_OBJECT: ");
                    print_generic_stmt(h, DR_BASE_OBJECT(dr), 0);
                    fprintf(h, "\t#STMT: ");
                    print_gimple_stmt(h, DR_STMT(dr), 0, 0);
                    //dump_data_reference(h, );
                    break;
                }
            }
        }
    }

}


void GPOLY::dump(CHAR * name)
{
    if (name == NULL) { name = "local_gcc_dump"; }

    Poly::dump(name);

    poly_bb * pbb = (poly_bb*)POLY_stmt(*this);
    FILE * h = fopen(name, "a+");
    dump_arr_base(pbb, h, 4);

    fprintf(h, "\nBB_BODY : ");
    if (PBB_IS_REDUCTION(pbb)) {
        fprintf(h, "REDUCTION-BB : ");
    }
    fprintf(h, "\n");

    dump_bb(GBB_BB(PBB_BLACK_BOX(pbb)), h, 4);
    fclose(h);
}
//END GPOLY


//
//START REF_DG
//
REF_DG::REF_DG(IN List<Poly*> & lst) : DepGraph(lst, false)
{}


REF_DG::~REF_DG()
{}


//Return true when this poly 'p' related stmt is a reduction statement.
bool REF_DG::is_red_stmt(Poly const& p)
{
    poly_bb const* pbb = (poly_bb const*)POLY_stmt(p);
    return PBB_IS_REDUCTION(pbb);
}


void REF_DG::dump(IN List<Poly*> & lst, bool is_detail)
{
    C<Poly*> * it1;
    C<Poly*> * it2;
    FILE * h = fopen(DUMP_FILE_NAME, "a+");
    fprintf(h, "\nSTMT DEP PAIRS:");
    for (Poly const* p1 = lst.get_head(&it1);
         p1 != NULL; p1 = lst.get_next(&it1)) {
        for (Poly const* p2 = lst.get_head(&it2);
             p2 != NULL; p2 = lst.get_next(&it2)) {
            AccMgr const* mgr1 = POLY_acc_mgr(*p1);
            AccMgr const* mgr2 = POLY_acc_mgr(*p2);
            List<AccMat*> lst1, lst2;
            mgr1->get_read_refs(lst1);
            mgr1->get_write_refs(lst1);
            mgr2->get_read_refs(lst2);
            mgr2->get_write_refs(lst2);
            C<AccMat*> * iit1;
            C<AccMat*> * iit2;
            poly_bb * pbb1 = (poly_bb *)POLY_stmt(*p1);
            poly_bb * pbb2 = (poly_bb *)POLY_stmt(*p2);
            for (AccMat const* am1 = lst1.get_head(&iit1);
                 am1 != NULL; am1 = lst1.get_next(&iit1)) {
                for (AccMat const* am2 = lst2.get_head(&iit2);
                     am2 != NULL; am2 = lst2.get_next(&iit2)) {
                    if (m_orig_dpmgr.get_dpvec(*p1, *p2, *am1, *am2) != NULL) {
                        fprintf(h, "\n\tBB%d -> BB%d",
                                pbb_index(pbb1), pbb_index(pbb2));
                        goto FIN;
                    }
                }
            }
FIN:        ;
        }
    }

    fprintf(h, "\nDependence Relation:");
    for (Poly const* p1 = lst.get_head(&it1);
         p1 != NULL; p1 = lst.get_next(&it1)) {
        for (Poly const* p2 = lst.get_head(&it2);
             p2 != NULL; p2 = lst.get_next(&it2)) {
            AccMgr const* mgr1 = POLY_acc_mgr(*p1);
            AccMgr const* mgr2 = POLY_acc_mgr(*p2);
            List<AccMat*> lst1, lst2;
            mgr1->get_read_refs(lst1);
            mgr1->get_write_refs(lst1);
            mgr2->get_read_refs(lst2);
            mgr2->get_write_refs(lst2);
            C<AccMat*> * iit1;
            C<AccMat*> * iit2;
            poly_bb * pbb1 = (poly_bb *)POLY_stmt(*p1);
            poly_bb * pbb2 = (poly_bb *)POLY_stmt(*p2);
            for (AccMat const* am1 = lst1.get_head(&iit1);
                 am1 != NULL; am1 = lst1.get_next(&iit1)) {
                for (AccMat const* am2 = lst2.get_head(&iit2);
                     am2 != NULL; am2 = lst2.get_next(&iit2)) {
                    DepVec * dpvec = m_orig_dpmgr.get_dpvec(*p1, *p2, *am1, *am2);
                    if (dpvec != NULL) {
                        fprintf(h, "\n\tBB%d:ACC%d -> BB%d:ACC%d",
                                pbb_index(pbb1), ACC_MAT_id(*am1),
                                pbb_index(pbb2), ACC_MAT_id(*am2));
                        for (INT i = 0; i <= dpvec->get_last_idx(); i++) {
                            DepPolyList * dpl = dpvec->get(i);
                            if (dpl != NULL) {
                                fprintf(h, " : ");
                                for (DepPoly * dp = dpl->get_head();
                                     dp != NULL; dp = dpl->get_next()) {
                                    UINT flag = DEP_POLY_flag(*dp);
                                    if (HAVE_FLAG(flag, DEP_LOOP_CARRIED)) {
                                        fprintf(h, "LOOP_CARR, ");
                                        REMOVE_FLAG(flag, DEP_LOOP_CARRIED);
                                    }
                                    if (HAVE_FLAG(flag, DEP_LOOP_INDEP)) {
                                        fprintf(h, "LOOP_INDEP, ");
                                        REMOVE_FLAG(flag, DEP_LOOP_INDEP);
                                    }
                                    ASSERT(flag == 0, ("still has flag?"));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    fprintf(h, "\n");
    fclose(h);
    if (is_detail) {
        m_orig_dpmgr.dump(lst);
    }
}
//END REF_DG



//
//START STMT_DG (Stmt Dependence Graph)
//
STMT_DG::STMT_DG(scop * s)
{
    poly_bb * pbb;
    for (UINT i = 0; VEC_iterate(poly_bb_p, SCOP_BBS(s), i, pbb); i++) {
        basic_block bb = GBB_BB(PBB_BLACK_BOX(pbb));
        SDG_stmt_bs(*this).bunion(bb->index);
        SDG_stmt_vec(*this).set(bb->index, bb);
    }

    for (UINT i = 0; VEC_iterate(poly_bb_p, SCOP_BBS(s), i, pbb); i++) {
        basic_block bb = GBB_BB(PBB_BLACK_BOX(pbb));
        edge e;
        edge_iterator ei;
        FOR_EACH_EDGE(e, ei, bb->preds) {
            basic_block from = e->src;
            basic_block to = e->dest;
            addEdge(from->index, to->index);
            if (e->probability) {
                //fprintf(file, " [%.1f%%] ",
                //          e->probability * 100.0 / REG_BR_PROB_BASE);
            }
            if (e->count) {
                //fputs (" count:", file);
                //fprintf(file, HOST_WIDEST_INT_PRINT_DEC, e->count);
            }
            if (e->flags) {
                UINT b = 1;
                for (UINT i = 0; i < sizeof(g_bitnames)/sizeof(g_bitnames[0]);
                     i++) {
                    if (HAVE_FLAG(e->flags, b)) {
                        //fprintf(stdout, "\n%s", g_bitnames[i]);
                        b <<= 1;
                    }
                } //end if
            }
        } //end for each prev

        FOR_EACH_EDGE(e, ei, bb->succs) {
            basic_block from = e->src;
            basic_block to = e->dest;
            addEdge(from->index, to->index);
            if (e->probability) {
                //fprintf(file, " [%.1f%%] ",
                //          e->probability * 100.0 / REG_BR_PROB_BASE);
            }
            if (e->count) {
                //fputs (" count:", file);
                //fprintf(file, HOST_WIDEST_INT_PRINT_DEC, e->count);
            }
            if (e->flags) {
                UINT b = 1;
                for (UINT i = 0; i < sizeof(g_bitnames)/sizeof(g_bitnames[0]);
                     i++) {
                    if (HAVE_FLAG(e->flags, b)) {
                        //fprintf(stdout, "\n%s", g_bitnames[i]);
                        b <<= 1;
                    }
                } //end if
            }
        } //end FOR_EACH_EDGE
    } //end for each bb
}


void STMT_DG::dump(CHAR * name)
{
    ASSERT(m_is_init, ("not yet initialized."));
    if (name == NULL) {
        name = GRAPH_VCG_NAME;
    }
    unlink(name);
    FILE * h = fopen(name, "a+");
    ASSERT(h, ("%s create failed!!!",name));

    fprintf(h, "\n/*\n\n");
    for (INT i = SDG_stmt_bs(*this).get_first();
         i != -1; i = SDG_stmt_bs(*this).get_next(i)) {
        basic_block bb = SDG_stmt_vec(*this).get(i);
        ASSERT0(bb != NULL);
        dump_bb(bb, h, 2);
        fprintf(h, "\n---------\n");
    }
    fprintf(h, "\n*/\n\n");

    fprintf(h, "graph: {"
              "title: \"Graph\"\n"
              "shrink:  15\n"
              "stretch: 27\n"
              "layout_downfactor: 1\n"
              "layout_upfactor: 1\n"
              "layout_nearfactor: 1\n"
              "layout_splinefactor: 70\n"
              "spreadlevel: 1\n"
              "treefactor: 0.500000\n"
              "node_alignment: center\n"
              "orientation: top_to_bottom\n"
              "late_edge_labels: no\n"
              "display_edge_labels: yes\n"
              "dirty_edge_labels: no\n"
              "finetuning: no\n"
              "nearedges: no\n"
              "splines: yes\n"
              "ignoresingles: no\n"
              "straight_phase: no\n"
              "priority_phase: no\n"
              "manhatten_edges: no\n"
              "smanhatten_edges: no\n"
              "port_sharing: no\n"
              "crossingphase2: yes\n"
              "crossingoptimization: yes\n"
              "crossingweight: bary\n"
              "arrow_mode: free\n"
              "layoutalgorithm: mindepthslow\n"
              "node.borderwidth: 3\n"
              "node.color: lightcyan\n"
              "node.textcolor: darkred\n"
              "node.bordercolor: red\n"
              "edge.color: darkgreen\n");

    //Print node
    for (Vertex * v = m_vertexs.get_first(); v;  v = m_vertexs.get_next()) {
        if (SDG_stmt_bs(*this).is_contain(VERTEX_vid(v))) {
            fprintf(h, "\nnode: { title:\"%d\" label: \"%d\" shape: circle color: gold}",
                    VERTEX_vid(v), VERTEX_vid(v));
        } else {
            fprintf(h, "\nnode: { title:\"%d\" label: \"%d\" shape: circle color: blue}",
                    VERTEX_vid(v), VERTEX_vid(v));
        }
    }

    //Print edge
    for (Edge * e = m_edges.get_first(); e;  e = m_edges.get_next()) {
        fprintf(h, "\nedge: { sourcename:\"%d\" targetname:\"%d\" %s}",
                VERTEX_vid(EDGE_from(e)),
                VERTEX_vid(EDGE_to(e)),
                m_is_direction ? "" : "arrowstyle:none" );
    }
    fprintf(h,"\n}\n");
    fclose(h);
}
//END STMT_DG



//Walk through a list of polyhedra to compute the number of vars.
static UINT compute_max_dim(IN ppl_Pointset_Powerset_C_Polyhedron_t ps)
{
    ppl_Pointset_Powerset_C_Polyhedron_iterator_t iter, end;
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&iter);
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&end);
    INT max_dim = -1;
    for (ppl_Pointset_Powerset_C_Polyhedron_iterator_begin(ps, iter),
         ppl_Pointset_Powerset_C_Polyhedron_iterator_end(ps, end);
         !ppl_Pointset_Powerset_C_Polyhedron_iterator_equal_test(iter, end);
         ppl_Pointset_Powerset_C_Polyhedron_iterator_increment(iter)) {

        ppl_const_Polyhedron_t ph;

        //Get the POLYHEDRON which 'iter' corresponded to.
        ppl_Pointset_Powerset_C_Polyhedron_iterator_dereference(iter, &ph);

        ppl_const_Constraint_System_t pcs;
        ppl_Polyhedron_get_constraints(ph, &pcs);

        //Get dimension.
        ppl_dimension_type dim;

        //Get matrix cols.
        ppl_Constraint_System_space_dimension(pcs, &dim);

        if (max_dim == -1) {
            max_dim = dim;
        } else {
            max_dim = MAX(max_dim, (INT)dim);
        }
    }

    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(iter);
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(end);
    return (UINT)max_dim;
}


//Compute the number of constraints.
//'ph': polyhedron
static void compute_constrain_num(IN ppl_const_Polyhedron_t ph,
                                OUT UINT * num_of_ineq,
                                OUT UINT * num_of_eq)
{
    *num_of_ineq = 0;
    *num_of_eq = 0;
    ppl_Constraint_System_const_iterator_t iter, end;
    ppl_new_Constraint_System_const_iterator(&iter);
    ppl_new_Constraint_System_const_iterator(&end);
    ppl_const_Constraint_System_t pcs;
    ppl_Polyhedron_get_constraints(ph, &pcs);
    for (ppl_Constraint_System_begin(pcs, iter),
         ppl_Constraint_System_end(pcs, end);
         !ppl_Constraint_System_const_iterator_equal_test(iter, end);
         ppl_Constraint_System_const_iterator_increment(iter)) {

        //It is just indicate single inequalitly/equality.
        ppl_const_Constraint_t coeff;

        //Get its coefficient.
        ppl_Constraint_System_const_iterator_dereference(iter, &coeff);

        //Mark ineq or eq.
        switch (ppl_Constraint_type(coeff)) {
        case PPL_CONSTRAINT_TYPE_LESS_THAN:
        case PPL_CONSTRAINT_TYPE_GREATER_THAN:
        case PPL_CONSTRAINT_TYPE_LESS_OR_EQUAL:
        case PPL_CONSTRAINT_TYPE_GREATER_OR_EQUAL:
            (*num_of_ineq)++;
            break;
        case PPL_CONSTRAINT_TYPE_EQUAL:
            (*num_of_eq)++;
            break;
        default:
            ASSERT(0, ("Not yet implemented"));
        }
    }
    ppl_delete_Constraint_System_const_iterator(iter);
    ppl_delete_Constraint_System_const_iterator(end);
}


/* Walk through a list of constrains of a polyhedron.
Return rhs_idx of the linear system.

'ineq': add or create matrix to record inequalities.
'eq': add or create matrix to record equalities. */
static UINT create_mat(IN ppl_const_Polyhedron_t ph,
                        IN OUT INTMat & ineq,
                        IN OUT INTMat & eq)
{
    //Construct matrix.
    UINT num_of_ineq, num_of_eq;
    compute_constrain_num(ph, &num_of_ineq, &num_of_eq);
    UINT i_ineq = 0, i_eq = 0;

    ppl_dimension_type dim;
    ppl_const_Constraint_System_t pcs;
    ppl_Polyhedron_get_constraints(ph, &pcs);
    ppl_Constraint_System_space_dimension(pcs, &dim);
    UINT col_size = dim + 1;
    UINT rhs_idx = col_size - 1;

    if (num_of_ineq != 0) {
        if (ineq.size() == 0) {
            ineq.reinit(num_of_ineq, col_size);
            i_ineq = 0;
        } else {
            i_ineq = ineq.get_row_size();
            ineq.grow_row(num_of_ineq);
        }
    }
    if (num_of_eq != 0) {
        if (eq.size() == 0) {
            eq.reinit(num_of_eq, col_size);
            i_eq = 0;
        } else {
            i_eq = eq.get_row_size();
            eq.grow_row(num_of_eq);
        }
    }

    //Walk through each constrains to construct coefficient.
    ppl_Coefficient_t c;
    ppl_new_Coefficient(&c); //alloc memory, it must be free.
    ppl_Constraint_System_const_iterator_t iter, end;
    ppl_new_Constraint_System_const_iterator(&iter);
    ppl_new_Constraint_System_const_iterator(&end);

    Value v; //mpt_z
    value_init(v);
    for (ppl_Constraint_System_begin(pcs, iter),
         ppl_Constraint_System_end(pcs, end);
         !ppl_Constraint_System_const_iterator_equal_test(iter, end);
         ppl_Constraint_System_const_iterator_increment(iter)) {

        //it is just only one inequality.
        ppl_const_Constraint_t coeff;

        //get coefficient matrix.
        ppl_Constraint_System_const_iterator_dereference(iter, &coeff);

        //type as UINT
        ppl_dimension_type dim;

        //get the number of dimension(columns)
        ppl_Constraint_space_dimension(coeff, &dim);
        ASSERT0(dim < col_size);
        INTMat tmp(1, col_size);
        for (UINT j = 0; j < dim; j++) {
            //get coeff[j], c := coeff[j]
            ppl_Constraint_coefficient(coeff, j, c);

            //v := c
            ppl_Coefficient_to_mpz_t(c, v);
            INT vv = value_get_si(v);
            tmp.set(0, j, vv);
        }

        ppl_Constraint_inhomogeneous_term(coeff, c);
        ppl_Coefficient_to_mpz_t(c, v);
        INT vv = value_get_si(v);
        tmp.set(0, rhs_idx, vv);

        bool is_ineq = true;
        switch (ppl_Constraint_type(coeff)) {
        case PPL_CONSTRAINT_TYPE_GREATER_THAN:
            tmp.mul(-1);
            //Fall through
        case PPL_CONSTRAINT_TYPE_LESS_THAN:
            tmp.set(0, rhs_idx, tmp.get(0, rhs_idx) - 1);
            break;
        case PPL_CONSTRAINT_TYPE_GREATER_OR_EQUAL:
            tmp.mul(-1);
        case PPL_CONSTRAINT_TYPE_LESS_OR_EQUAL:
            break;
        case PPL_CONSTRAINT_TYPE_EQUAL:
            is_ineq = false;
            break;
        default: ASSERT(0, ("Not yet implemented"));
        }

        if (is_ineq) {
            ineq.set_rows(i_ineq, i_ineq, tmp, 0);
            i_ineq++;
        } else {
            eq.set_rows(i_eq, i_eq, tmp, 0);
            i_eq++;
        }
    }

    value_clear(v);
    ppl_delete_Coefficient(c);
    ppl_delete_Constraint_System_const_iterator(iter);
    ppl_delete_Constraint_System_const_iterator(end);
    return rhs_idx;
}


//Create constrains.
//Walk through a list of polyhedron, and return the rhs_idx.
static UINT create_mat_lst(IN ppl_Pointset_Powerset_C_Polyhedron_t ps,
                            OUT INTMat & ineq,
                            OUT INTMat & eq)
{
    UINT tot_dim = compute_max_dim(ps); //iter_var + lcl_var + parameters_var
    ppl_Pointset_Powerset_C_Polyhedron_iterator_t iter, end;
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&iter);
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&end);
    for (ppl_Pointset_Powerset_C_Polyhedron_iterator_begin(ps, iter),
         ppl_Pointset_Powerset_C_Polyhedron_iterator_end(ps, end);
         !ppl_Pointset_Powerset_C_Polyhedron_iterator_equal_test(iter, end);
         ppl_Pointset_Powerset_C_Polyhedron_iterator_increment(iter)) {

        ppl_const_Polyhedron_t ph;

        //get the POLYHEDRON which 'iter' corresponded to.
        ppl_Pointset_Powerset_C_Polyhedron_iterator_dereference(iter, &ph);
        UINT d = create_mat(ph, ineq, eq);
        ASSERT0(d == tot_dim);
    }
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(iter);
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(end);
    return tot_dim;
}


//Create constrains.
//Walk through a list of polyhedron, and return the rhs_idx.
static UINT create_mat_lst(IN ppl_Pointset_Powerset_C_Polyhedron_t ps,
                            OUT List<INTMat*> & ineq_lst,
                            OUT List<INTMat*> & eq_lst)
{
    UINT tot_dim = compute_max_dim(ps); //iter_var + lcl_var + parameters_var
    ppl_Pointset_Powerset_C_Polyhedron_iterator_t iter, end;
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&iter);
    ppl_new_Pointset_Powerset_C_Polyhedron_iterator(&end);

    INTMat ineq, eq;
    for (ppl_Pointset_Powerset_C_Polyhedron_iterator_begin(ps, iter),
         ppl_Pointset_Powerset_C_Polyhedron_iterator_end(ps, end);
         !ppl_Pointset_Powerset_C_Polyhedron_iterator_equal_test(iter, end);
         ppl_Pointset_Powerset_C_Polyhedron_iterator_increment(iter)) {
        ppl_const_Polyhedron_t ph;

        //get the POLYHEDRON which 'iter' corresponded to.
        ppl_Pointset_Powerset_C_Polyhedron_iterator_dereference(iter, &ph);
        UINT d = create_mat(ph, ineq, eq);
        ASSERT0(d == tot_dim);
        if (ineq.size() != 0) {
            ineq_lst.append_tail(new INTMat(ineq));
        }
        if (eq.size() != 0) {
            eq_lst.append_tail(new INTMat(eq));
        }
    }
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(iter);
    ppl_delete_Pointset_Powerset_C_Polyhedron_iterator(end);
    return tot_dim;
}


//Generate domain matrix.
static void gen_domain_mat(IN OUT Poly & p,
                            IN INTMat & ineq,
                            IN INTMat & eq,
                            UINT rhs_idx,
                            IN poly_bb * pbb)
{
    RMat tineq(ineq), teq(eq);
    if (eq.size() != 0) {
        Lineq l(&tineq, rhs_idx);
        l.appendEquation(teq);
    }
    ASSERT0(pbb_nb_local_vars(pbb) == 0);
    ASSERT0(tineq.get_col_size() == rhs_idx + 1);
    tineq.mulOfColumn(rhs_idx, -1);
    UINT new_rhs_idx = 0;
    UINT n_p = pbb_nb_params(pbb);
    ASSERT(n_p == 0, ("Parameter is not support presently."));
    UINT n_d = pbb_dim_iter_domain(pbb);
    if (n_p > 0) {
        Lineq l(NULL);
        UINT fs, ls;
        l.move2cstsym(tineq,
                    rhs_idx,
                    n_d,
                    n_d + n_p - 1,
                    &fs,
                    &ls);
        new_rhs_idx = rhs_idx - n_p;
    } else {
        new_rhs_idx = rhs_idx;
    }
    POLY_domain(p)->copy(tineq);
    POLY_domain_rhs_idx(p) = new_rhs_idx;
}


//Layout of m: is_ineq, scattering_transform, local_vars,
//iter_domain, gammas, cst.
//e.g: is_ineq s0 s1 s2 s3 s4 i0 i1 g0, g1, g2, cst
static void gen_sche_mat(IN OUT Poly & p, INTMat const& m, IN poly_bb * pbb)
{
    ScheduleMat * sm = POLY_sche(p);
    sm->init(POLY_domain_rhs_idx(p), pbb_nb_params(pbb)/*Number of CST SYM*/);
    for (UINT l = 0; l < POLY_domain_rhs_idx(p); l++) {
        sm->setMapDepth2IV(l+1, l);
    }
    for (UINT d = 0; d <= pbb_dim_iter_domain(pbb); d++) {
        INT v = m.get(2*d, m.get_col_size() - 1);
        ASSERT(m.get(2*d, 2*d) >= 0 && v <= 0,
                ("scattering matrix format has changed!"));
        sm->set_stmt_order(d, -v);
    }
    ASSERT0(POLY_domain_rhs_idx(p) == sm->get_syn_order_idx());
}


//Generate accessing matrix.
static void gen_acc_mat(IN poly_dr * pdr,
                        INTMat const& ineq,
                        INTMat const& eq,
                        OUT AccMat & am)
{
    poly_bb * pbb = PDR_PBB(pdr);
    INT as = pdr_alias_set_dim(pdr);
    am.reinit(PDR_NB_SUBSCRIPTS(pdr),
              pbb_dim_iter_domain(pbb) + 1 + pbb_nb_params(pbb));
    UINT rhs_idx = pbb_dim_iter_domain(pbb);
    for (UINT k = 0; k < PDR_NB_SUBSCRIPTS(pdr); k++) {
        UINT col = pdr_subscript_dim(pdr, k);
        for (UINT row = 0; row < eq.get_row_size(); row++) {
            if (eq.get(row, col) != 0) {
                INT v;
                if (eq.get(row, col) < 0) {
                    v = 1;
                } else {
                    v = -1;
                }
                UINT i;
                for (i = 0; i < pbb_dim_iter_domain(pbb); i++) {
                    UINT c = pdr_iterator_dim(pdr, i);
                    am.set(k, i, eq.get(row, c) * v);
                }
                for (i = 0; i < pbb_nb_params(pbb); i++) {
                    UINT c = pdr_parameter_dim(pdr, i);
                    am.set(k, rhs_idx + 1 + i, eq.get(row, c) * v);
                }
                am.set(k, rhs_idx, eq.get(row, eq.get_col_size() - 1));
                break;
            }
        }
    }
}


/* Example:
     int A[1335][123];
     int *p = malloc ();
     k = ...
     for i {
         if (unknown_function()) {
             p = A;
             ... = p[?][?];
              for j {
                 A[i][j+k] = m;
             }
         }
     }

     The data access A[i][j+k] in alias set "5" is described like this:
     | i   j   k   a  s0  s1   1
     | 0   0   0   1   0   0  -5     =  0
     |-1   0   0   0   1   0   0     =  0
     | 0  -1  -1   0   0   1   0     =  0
     | 0   0   0   0   1   0   0     >= 0  # The last four lines describe the
     | 0   0   0   0   0   1   0     >= 0  # array size.
     | 0   0   0   0  -1   0 1335    >= 0
     | 0   0   0   0   0  -1 123     >= 0

     The pointer "*p" in alias set "5" and "7" is described as a union of
     polyhedron:
     | i   k   a  s0   1
     | 0   0   1   0  -5   =  0
     | 0   0   0   1   0   >= 0
     "or"
     | i   k   a  s0   1
     | 0   0   1   0  -7   =  0
     | 0   0   0   1   0   >= 0
     "*p" accesses all of the object allocated with 'malloc'.

     The scalar data access "m" is represented as an array with zero subscript
     dimensions.
     | i   j   k   a   1
     | 0   0   0  -1   15  = 0
*/
static UINT gen_acc_mat(IN poly_bb * pbb, OUT AccMgr & mgr)
{
    poly_dr_p pdr;
    INTMat ineq, eq;
    AccMat am;
    for (UINT i = 0; VEC_iterate(poly_dr_p, PBB_DRS(pbb), i, pdr); i++) {
        ineq.clean();
        eq.clean();
        {/*TEST
            FILE * h = fopen(DUMP_FILE_NAME, "a+");
            print_pdr(h, pdr, 100);
            fclose(h);
            */
        }
        INT dim = create_mat_lst(PDR_ACCESSES(pdr), ineq, eq);
        ACC_MAT_id(am) = PDR_ID(pdr);
        ACC_MAT_arr_id(am) = PDR_BASE_OBJECT_SET(pdr);
        gen_acc_mat(pdr, ineq, eq, am);

        if (PDR_TYPE(pdr) == PDR_READ) {
            mgr.set_ref(am, true);
        } else if (PDR_TYPE(pdr) == PDR_WRITE) {
            mgr.set_ref(am, false);
        } else {
            UNREACH();
        }
    }
    return 0;
}


/* Convert one of rows of 'r' to ppl constrain.
Caller need to invoke 'ppl_delete_Constraint()' to free memory.
The last column of r is const term column.
'is_eq': true if row of 'r' indicates equation. */
static ppl_Constraint_t convert_ppl_cs(RMat const& r, UINT row, bool is_eq)
{
    ppl_Constraint_t cstr;
    ppl_Coefficient_t coef;
    ppl_Linear_Expression_t expr;
    ppl_dimension_type dim = r.get_col_size() - 1;

    ppl_new_Coefficient(&coef);
    ppl_new_Linear_Expression_with_dimension(&expr, dim);

    Value v; //mpt_z
    value_init(v);
    for (UINT j = 0; j < r.get_col_size() - 1; j++) {
        ASSERT0(r.get(row, j).den() == 1);
        value_set_si(v, r.get(row, j).num());
        ppl_assign_Coefficient_from_mpz_t(coef, v);
        ppl_Linear_Expression_add_to_coefficient(expr, j, coef);
    }

    ASSERT0(r.get(row, r.get_col_size() - 1).den() == 1);
    value_set_si(v, r.get(row, r.get_col_size() - 1).num());
    ppl_assign_Coefficient_from_mpz_t(coef, v);
    ppl_Linear_Expression_add_to_inhomogeneous(expr, coef);
    ppl_delete_Coefficient(coef);

    if (is_eq) {
        ppl_new_Constraint(&cstr, expr, PPL_CONSTRAINT_TYPE_EQUAL);
    } else {
        ppl_new_Constraint(&cstr, expr, PPL_CONSTRAINT_TYPE_GREATER_OR_EQUAL);
    }
    ppl_delete_Linear_Expression(expr);
    value_clear(v);
    return cstr;
}


/* Convert matrix to ppl constrains.
The last column of r is const term column.
'is_eq': true if row of 'r' indicates equation. */
static void convert_ppl_cs(OUT ppl_Constraint_System_t * cs,
                           RMat const& r, bool is_eq)
{
    for (UINT i = 0; i < r.get_row_size(); i++) {
        ppl_Constraint_t c = convert_ppl_cs(r, i, is_eq);
        ppl_Constraint_System_insert_Constraint(*cs, c);
        ppl_delete_Constraint(c);
    }
}


//Construct PPL structures.
static void gen_ppl_domain(IN Poly & p)
{
    DomainMat * domain = POLY_domain(p);
    ScheduleMat * sm = POLY_sche(p);
    RMat tmp;
    domain->innerColumn(tmp, 0, p.get_num_of_var() - 1);
    tmp.mul(-1);
    //COL:s0 s1 s2 s3 s4 l0 l1 i0 i1 g0 g1 g2 C
    //RMat cldomain(domain->get_row_size(), sm->get_row_size() +
    //                                    p.get_num_of_localvar() +
    //                                    p.get_num_of_var() +
    //                                    p.get_num_of_param() + 1);
    RMat cldomain(domain->get_row_size(), p.get_num_of_var() +
                  p.get_num_of_param() + 1);
    //INT c = sm->get_row_size() + p.get_num_of_localvar();
    INT c = 0;
    cldomain.set_cols(c, c + tmp.get_col_size() - 1, tmp, 0);
    UINT d = c + tmp.get_col_size();
    ASSERT0(d + p.get_num_of_param() == cldomain.get_col_size() - 1);
    if (p.get_num_of_param() > 0) {
        cldomain.set_cols(d, d + p.get_num_of_param() - 1,
                          *(RMat*)domain, POLY_domain_rhs_idx(p) + 1);
    }
    cldomain.set_cols(cldomain.get_col_size() - 1,
                      cldomain.get_col_size() - 1,
                      *(RMat*)domain, POLY_domain_rhs_idx(p));

    ppl_Constraint_System_t cs;
    ppl_new_Constraint_System(&cs);
    convert_ppl_cs(&cs, cldomain, false);
    ppl_Pointset_Powerset_C_Polyhedron_t ppldomain;
    ppl_new_Pointset_Powerset_C_Polyhedron_from_Constraint_System(&ppldomain, cs);
    ppl_delete_Constraint_System(cs);
    //ppl_new_Pointset_Powerset_C_Polyhedron_from_Pointset_Powerset_C_Polyhedron(&ppldomain, PBB_DOMAIN(pbb));
    //ppl_Pointset_Powerset_C_Polyhedron_add_constraints(ppldomain, cs);
    //ppl_Pointset_Powerset_C_Polyhedron_intersection_assign(ppldomain, cs);
    //ppl_Pointset_Powerset_C_Polyhedron_space_dimension(ph, &dim);
    //ppl_Pointset_Powerset_C_Polyhedron_add_space_dimensions_and_embed(ph, nb_new_dims); //insert dimension

    //Updata pbb.
    poly_bb * pbb = (poly_bb*)POLY_stmt(p);
#ifdef _DEBUG_
    INTMat ineq,eq;
    create_mat_lst(PBB_DOMAIN(pbb), ineq, eq);
    ineq.clean();
    eq.clean();
    create_mat_lst(ppldomain, ineq, eq);
#endif
    ppl_delete_Pointset_Powerset_C_Polyhedron(PBB_DOMAIN(pbb));
    PBB_DOMAIN(pbb) = ppldomain;
}


//Updates the scattering of PBB.
static void gen_ppl_sc(IN Poly & p)
{
    ScheduleMat * sm = POLY_sche(p);
    UINT row_size = sm->get_row_size();
    UINT col_size = sm->get_row_size() +
                    p.get_num_of_var() + p.get_num_of_param() + 1;
    RMat r(row_size, col_size);
    UINT i;

    //Colums:s0 s1 s2 s3 s4 l0 l1 i0 i1 g0 g1 g2 C
    for (i = 0; i < row_size; i++) {
        r.set(i, i, 1);
    }
    INT c = row_size;
    r.set_cols(c, c + sm->get_num_of_var() - 1, (RMat&)*sm, 0);
    if (sm->get_num_of_gamma() > 0) {
        INT d = c + sm->get_num_of_var();
        r.set_cols(d, d + sm->get_num_of_gamma() - 1,
                   (RMat&)*sm, sm->get_syn_order_idx() + 1);
    }
    r.set_cols(col_size - 1, col_size - 1, (RMat&)*sm, sm->get_syn_order_idx());
    r.mulOfColumns(c, col_size - 1, -1);

    poly_bb * pbb = (poly_bb*)POLY_stmt(p);
    ppl_Constraint_System_t cs;
    ppl_new_Constraint_System(&cs);
    convert_ppl_cs(&cs, r, true);
    ppl_Polyhedron_t scatter; //new scattering
    ppl_new_C_Polyhedron_from_Constraint_System(&scatter, cs);
    ppl_delete_Constraint_System(cs);

    ppl_delete_Polyhedron(PBB_TRANSFORMED_SCATTERING(pbb));
    PBB_TRANSFORMED_SCATTERING(pbb) = scatter;
    PBB_NB_SCATTERING_TRANSFORM(pbb) = row_size;
    PBB_NB_LOCAL_VARIABLES(pbb) = 0;
}


//Construct PPL structures.
static void    gen_ppl_acc(IN Poly & p)
{
    poly_bb * pbb = (poly_bb*)POLY_stmt(p);
}


static void poly2cloog(OUT scop * s, IN PolyMgr & pm, IN List<Poly*> & lst)
{
    Poly * p = lst.get_head();
    if (p == NULL) { return; }

    graphite_dim_t nb = p->get_num_of_param();
    scop_set_nb_params(s, nb);

    for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
        gen_ppl_domain(*p);
        gen_ppl_sc(*p);
        gen_ppl_acc(*p);
    }
}


//Convert PPL polyhedra information to xpoly representation.
static void ppl2poly(scop * s, PolyMgr & pm, OUT List<Poly*> & lst)
{
    poly_bb * pbb;
    for (UINT i = 0; VEC_iterate(poly_bb_p, SCOP_BBS(s), i, pbb); i++) {
        ppl_Pointset_Powerset_C_Polyhedron_t domain_list = PBB_DOMAIN(pbb);
        if (ppl_Pointset_Powerset_C_Polyhedron_is_empty(domain_list)) {
            continue;
        }
        Poly * p = pm.createPoly();
        POLY_id(*p) = pbb_index(pbb);
        POLY_stmt(*p) = pbb;
        lst.append_tail(p);
        INTMat ineq, eq;

        //init domain matrix
        UINT rhs_idx = create_mat_lst(domain_list, ineq, eq);
        ASSERT0(pbb_dim_iter_domain(pbb) + pbb_nb_params(pbb) +
                 pbb_nb_local_vars(pbb)  == rhs_idx);
        gen_domain_mat(*p, ineq, eq, rhs_idx, pbb);

        //init schedul matrix
        ineq.clean();
        eq.clean();
        create_mat(PBB_ORIGINAL_SCATTERING(pbb), ineq, eq);
        ASSERT0(ineq.size() == 0);
        gen_sche_mat(*p, eq, pbb);

        //init access matrix
        gen_acc_mat(pbb, *POLY_acc_mgr(*p));

        p->dump();
    }
}


//This function demostrates how to use xpoly to transform
//gcc graphite scop.
static void example_trans(scop_p s,
                        IN List<Poly*> & lst,
                        OUT List<Poly*> & after_lst,
                        GPOLY_MGR & pm)
{
    REF_DG * rdg = new REF_DG(lst);
    List<Poly*> before_lst;
    pm.copyPolyList(lst, before_lst);
    INT const u = lst.get_head()->get_max_depth();
    PolyTran pt;
    Poly * p = NULL;
    bool cpy = true;

    List<Poly*> tmp;
    if (cpy) pm.copyPolyList(lst, before_lst);
    if (cpy) pm.copyPolyList(lst, after_lst);

    //Perform loop transformations.
    for (int i = 0; i <= u; i++) {
        for (int j = 0; j <= u; j++) {
            if (pt.interchange(after_lst, i, j)) {
                if (rdg->is_legal(after_lst)) {
                    //Record successful transformation.
                    if (cpy) pm.copyPolyList(after_lst, before_lst);
                } else {
                    if (cpy) pm.copyPolyList(before_lst, after_lst);
                }
            } else {
                if (cpy) pm.copyPolyList(before_lst, after_lst);
            }

            if (pt.reverse(after_lst, j)) {
                if (rdg->is_legal(after_lst)) {
                    //Record successful transformation.
                    if (cpy) pm.copyPolyList(after_lst, before_lst);
                } else {
                    if (cpy) pm.copyPolyList(before_lst, after_lst);
                }
            } else {
                if (cpy) pm.copyPolyList(before_lst, after_lst);
            }

            if (pt.skew(after_lst, j, i, 1)) {
                if (rdg->is_legal(after_lst)) {
                    //Record successful transformation.
                    if (cpy) pm.copyPolyList(after_lst, before_lst);
                } else {
                    if (cpy) pm.copyPolyList(before_lst, after_lst);
                }
            } else {
                if (cpy) pm.copyPolyList(before_lst, after_lst);
            }

            UINT changed_iv_idx, generated_iv_idx;
            if (pt.tiling(after_lst, j, 32, &changed_iv_idx,
                          &generated_iv_idx)) {
                rdg->get_orig_dep_mgr()->insertLoopBefore(generated_iv_idx);
                //rdg->get_orig_dep_mgr()->insertLocalVar();
                if (rdg->is_legal(after_lst)) {
                    //Record successful transformation.
                    if (cpy) pm.copyPolyList(after_lst, before_lst);
                } else {
                    if (cpy) pm.copyPolyList(before_lst, after_lst);
                    rdg->get_orig_dep_mgr()->removeLoop(generated_iv_idx);
                    //rdg->get_orig_dep_mgr()->removeLocalVar();
                }
            } else {
                if (cpy) pm.copyPolyList(before_lst, after_lst);
            }
        }
    }

    pm.freePolyList(before_lst);
    delete rdg;
}


//Return the first lst representing a PBB statement in list.
static lst_p find_first_pbb(lst_p lst)
{
    if (lst == NULL) { return NULL; }
    if (!LST_LOOP_P(lst)) { return lst; }

    lst_p l;
    for (INT i = 0; VEC_iterate(lst_p, LST_SEQ(lst), i, l); i++) {
        lst_p res = lst_find_first_pbb (l);
        if (res != NULL) { return res; }
    }
    return NULL;
}


static void scan_pbblst(OUT List<poly_bb*> & pbblst, IN lst_p lst)
{
    if (lst == NULL) { return; }
    if (!LST_LOOP_P(lst)) {
        //lst node is a statement.
        pbblst.append_tail(LST_PBB(find_first_pbb(lst)));
        return;
    }

    lst_p l;
    for (INT i = 0; VEC_iterate(lst_p, LST_SEQ(lst), i, l); i++) {
        scan_pbblst(pbblst, l);
    }
}


//Generate code even if we apply polyhedral transformation in scop.
//transformation: GIMPLE -> GRAPHITE -> GIMPLE.
bool do_poly_transforms(scop_p scop)
{
    List<poly_bb*> pbblst;
    scan_pbblst(pbblst, SCOP_TRANSFORMED_SCHEDULE(scop));

    List<Poly*> lst;
    GPOLY_MGR pm;
    ppl2poly(scop, pm, lst);

    UINT depth = 0;
    pm.growToMaxDepth(lst);

    List<Poly*> after_lst;
    pm.copyPolyList(lst, after_lst);
    example_trans(scop, lst, after_lst, pm);
    pm.removeVirtualDepth(after_lst);
    poly2cloog(scop, pm, after_lst);

    pm.freePolyList(lst);
    pm.freePolyList(after_lst);
    return true;
}
#endif
