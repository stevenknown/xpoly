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
#include "ltype.h"

//Most general utilies for common used
#include "comf.h"
#include "smempool.h"
#include "sstl.h"
#include "matt.h"
#include "bs.h"
#include "sgraph.h"
#include "rational.h"
#include "flty.h"

//Utilies/algorithm for common used
#include "xmat.h"
#include "depvecs.h"
#include "linsys.h"
#include "poly.h"
#include "ldtran.h"
#include "lpsol.h"

#define DUMP_FILE_NAME "dumpoly.tmp"
//#define ONLY_CHECK_INNERMOST_DEPTH
#define INTERCH_BY_UNI

static CHAR * format_rational(IN RATIONAL const& rat,
							IN CHAR * buf, bool is_coeff)
{
	CHAR * blank;
	CHAR * blank2 = "      ";
	if (is_coeff) {
		blank = "";
		if (rat.den() == 1) {
			if (rat.num() == 1) {
				buf[0] = 0;
			} else if (rat.num() == -1) {
				sprintf(buf, "-");
			} else {
				sprintf(buf, "%d", (INT)rat.num());
			}
		} else if (rat.den() == -1) {
			if (rat.num() == 1) {
				sprintf(buf, "-");
			} else {
				sprintf(buf, "%d", -((INT)rat.num()));
			}
		} else if (rat.num() == 0) {
			if (rat.den() == 1) {
				sprintf(buf, "0");
			} else {
				sprintf(buf, "%d/%d", (INT)rat.num(), (INT)rat.den());
			}
		} else {
			sprintf(buf, "%d/%d", (INT)rat.num(), (INT)rat.den());
		}
	} else {
		blank = "      ";
		if (rat.den() == 1) {
			sprintf(buf, "%5d%s", (INT)rat.num(), blank);
		} else if (rat.den() == -1) {
			sprintf(buf, "%5d%s", -((INT)rat.num()), blank);
		} else if (rat.num() == 0) {
			if (rat.den() == 1) {
				sprintf(buf, "%5d %s", 0, blank);
			} else {
				sprintf(buf, "%5d/%-5d", (INT)rat.num(), (INT)rat.den());
			}
		} else {
			sprintf(buf, "%5d/%-5d", (INT)rat.num(), (INT)rat.den());
		}
	}
	return buf;
}


//
//START DG
//
DG::DG(IN LIST<POLY*> & lst, bool is_build_graph)
{
	m_is_build_graph = false;
	rebuild(lst, is_build_graph);
}


DG::~DG()
{
	for (INT i = 0; i <= m_sch_mat.get_last_idx(); i++) {
		RMAT * sch = m_sch_mat.get(i);
		if (sch != NULL) {
			sch->destroy();
		}
	}
}


bool DG::is_red_stmt(IN POLY const& p)
{
	return false;
}


//Return true if 'am1', 'am2' is the references of a reduction.
bool DG::is_red_pair(IN POLY const& p1,
					IN POLY const& p2,
					IN ACC_MAT const& am1,
					IN ACC_MAT const& am2)
{
	if (is_red_stmt(p1)) {
		LIST<ACC_MAT*> lst;
		ACC_MGR const* mgr = POLY_acc_mgr(p1);
		mgr->get_write_refs(lst);
		for (ACC_MAT * rv = lst.get_head();
			 rv != NULL; rv = lst.get_next()) {
			if (ACC_MAT_arr_id(am1) == ACC_MAT_arr_id(*rv) &&
				ACC_MAT_arr_id(am2) == ACC_MAT_arr_id(*rv)) {
				return true;
			}
		}
		return false;
	}

	if (is_red_stmt(p2)) {
		LIST<ACC_MAT*> lst;
		ACC_MGR const* mgr = POLY_acc_mgr(p2);
		mgr->get_write_refs(lst);
		for (ACC_MAT * rv = lst.get_head();
			 rv != NULL; rv = lst.get_next()) {
			if (ACC_MAT_arr_id(am1) == ACC_MAT_arr_id(*rv) &&
				ACC_MAT_arr_id(am2) == ACC_MAT_arr_id(*rv)) {
				return true;
			}
		}
		return false;
	}

	return false;
}


bool DG::is_legal(IN LIST<POLY*> & lst)
{
	C<POLY*> * it1;
	C<POLY*> * it2;
	VC_MAT vc, * pvc;
	DEP_POLY_MGR tran_dep_mgr;
	LIST<ACC_MAT*> lst_1;
	LIST<ACC_MAT*> lst_2;
	DPVEC tran_dpvec(0, 0);
	for (POLY const* p1 = lst.get_head(&it1);
		 p1 != NULL; p1 = lst.get_next(&it1)) {
		for (POLY const* p2 = lst.get_head(&it2);
			 p2 != NULL; p2 = lst.get_next(&it2)) {
			ACC_MGR const* mgr1 = POLY_acc_mgr(*p1);
			ACC_MGR const* mgr2 = POLY_acc_mgr(*p2);
			lst_1.clean();
			lst_2.clean();
			mgr1->get_read_refs(lst_1);
			mgr1->get_write_refs(lst_1);
			mgr2->get_read_refs(lst_2);
			mgr2->get_write_refs(lst_2);
			C<ACC_MAT*> * iit1;
			C<ACC_MAT*> * iit2;
			pvc = tran_dep_mgr.build_vc(*p1, *p2, vc);
			for (ACC_MAT const* am1 = lst_1.get_head(&iit1);
				 am1 != NULL; am1 = lst_1.get_next(&iit1)) {
				for (ACC_MAT const* am2 = lst_2.get_head(&iit2);
					 am2 != NULL; am2 = lst_2.get_next(&iit2)) {
					DPVEC * orig_dpvec;
					if ((orig_dpvec = m_orig_dpmgr.get_dpvec(*p1,
											*p2, *am1, *am2)) != NULL) {
						if (is_red_pair(*p1, *p2, *am1, *am2)) {
							continue;
						}
						tran_dep_mgr.build_dep_poly(*p1,
											*p2, *am1, *am2,
											pvc, tran_dpvec, true);
						if (tran_dpvec.get_last_idx() == -1) {
							continue;
						}
						if (!tran_dpvec.is_intersect_empty(*orig_dpvec)) {
							tran_dpvec.free_elem();
							tran_dpvec.clean();
							return false;
						}
						tran_dpvec.free_elem();
						tran_dpvec.clean();
					}
				}
			}
		}
	}
	return true;
}


bool DG::verify(IN LIST<POLY*> & lst, IN DEP_POLY_HASH & dh)
{
	C<POLY*> * it1;
	C<POLY*> * it2;
	for (POLY const* p1 = lst.get_head(&it1);
		 p1 != NULL; p1 = lst.get_next(&it1)) {
		for (POLY const* p2 = lst.get_head(&it2);
			 p2 != NULL; p2 = lst.get_next(&it2)) {
			ACC_MGR const* mgr1 = POLY_acc_mgr(*p1);
			ACC_MGR const* mgr2 = POLY_acc_mgr(*p2);
			LIST<ACC_MAT*> lst_1, lst_2;
			mgr1->get_read_refs(lst_1);
			mgr1->get_write_refs(lst_1);
			mgr2->get_read_refs(lst_2);
			mgr2->get_write_refs(lst_2);
			C<ACC_MAT*> * iit1;
			C<ACC_MAT*> * iit2;
			for (ACC_MAT const* am1 = lst_1.get_head(&iit1);
				 am1 != NULL; am1 = lst_1.get_next(&iit1)) {
				for (ACC_MAT const* am2 = lst_2.get_head(&iit2);
					 am2 != NULL; am2 = lst_2.get_next(&iit2)) {
					if (m_orig_dpmgr.get_dpvec(*p1,
								*p2, *am1, *am2) != NULL ||
					 	m_orig_dpmgr.get_dpvec(*p2,
					 			*p1, *am2, *am1) != NULL ) {
						IS_TRUE(dh.find(*p1, *p2, *am1, *am2) != NULL ||
								dh.find(*p2, *p1, *am2, *am1) != NULL,
								("there is unmatched dependences."));
					}
				}
			}
		}
	}
	return true;
}


void DG::rebuild(IN LIST<POLY*> & lst, bool is_build_graph)
{
	m_is_build_graph = is_build_graph;
	erasure();
	set_unique(false);
	m_orig_dpmgr.clean();
	C<POLY*> * it1;
	C<POLY*> * it2;
	VC_MAT vc, * pvc;
	LIST<ACC_MAT*> lst_1, lst_2;
	for (POLY const* p1 = lst.get_head(&it1);
		 p1 != NULL; p1 = lst.get_next(&it1)) {
		for (POLY const* p2 = lst.get_head(&it2);
			 p2 != NULL; p2 = lst.get_next(&it2)) {
			IS_TRUE0(p1->is_same_dim(*p2));
			ACC_MGR const* mgr1 = POLY_acc_mgr(*p1);
			ACC_MGR const* mgr2 = POLY_acc_mgr(*p2);
			lst_1.clean();
			lst_2.clean();
			mgr1->get_read_refs(lst_1);
			mgr1->get_write_refs(lst_1);
			mgr2->get_read_refs(lst_2);
			mgr2->get_write_refs(lst_2);
			C<ACC_MAT*> * iit1;
			C<ACC_MAT*> * iit2;
			pvc = m_orig_dpmgr.build_vc(*p1, *p2, vc);
			for (ACC_MAT const* am1 = lst_1.get_head(&iit1);
				 am1 != NULL; am1 = lst_1.get_next(&iit1)) {
				for (ACC_MAT const* am2 = lst_2.get_head(&iit2);
					 am2 != NULL; am2 = lst_2.get_next(&iit2)) {
					DPVEC * dpvec = m_orig_dpmgr.build_dep_poly(*p1,
											*p2, *am1, *am2, pvc, false);
					if (is_build_graph && dpvec != NULL) {
						EDGE * e = add_edge(ACC_MAT_id(*am1),
											ACC_MAT_id(*am2));
						IS_TRUE0(EDGE_info(e) == NULL);
						DGEINFO * ei = (DGEINFO*)xmalloc(sizeof(DGEINFO));
						EDGE_info(e) = ei;
						DGEINFO_dpvec(ei) = dpvec;
					}
				}
			}
		}
	}
}


void DG::set_dep_poly(IN VERTEX const* from,
					IN VERTEX const* to,
					IN DPVEC const* dp)
{
	IS_TRUE0(from != NULL && to != NULL);
	set_dep_poly(get_edge(from, to), dp);
}


void DG::set_dep_poly(IN EDGE * e, IN DPVEC const* dp)
{
	IS_TRUE0(e != NULL && dp != NULL);
	DGEINFO * ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		ei = (DGEINFO*)xmalloc(sizeof(DGEINFO));
		EDGE_info(e) = ei;
	}
	DGEINFO_dpvec(ei) = dp;
}


DPVEC const* DG::get_dep_poly(IN EDGE const* e) const
{
	IS_TRUE0(e != NULL);
	DGEINFO const* ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		return NULL;
	}
	return DGEINFO_dpvec(ei);
}


void DG::set_from_quasi_func(IN EDGE * e, IN RMAT * quasi)
{
	DEP_POLY const* dp = get_dep_poly(e)->get_innermost()->get_head();
	IS_TRUE0(dp != NULL && dp->get_col_size() == quasi->get_col_size());
	DGEINFO * ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		ei = (DGEINFO*)xmalloc(sizeof(DGEINFO));
		EDGE_info(e) = ei;
	}
	DGEINFO_from_quasi_func(ei) = quasi;
}


RMAT * DG::get_from_quasi_func(IN EDGE const* e) const
{
	DGEINFO * ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		return NULL;
	}
	return DGEINFO_from_quasi_func(ei);
}


void DG::set_to_quasi_func(IN EDGE * e, IN RMAT * quasi)
{
	DEP_POLY const* dp = get_dep_poly(e)->get_innermost()->get_head();
	IS_TRUE0(dp != NULL && dp->get_col_size() == quasi->get_col_size());
	DGEINFO * ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		ei = (DGEINFO*)xmalloc(sizeof(DGEINFO));
		EDGE_info(e) = ei;
	}
	DGEINFO_to_quasi_func(ei) = quasi;
}


RMAT * DG::get_to_quasi_func(IN EDGE const* e) const
{
	DGEINFO * ei = (DGEINFO*)EDGE_info(e);
	if (ei == NULL) {
		return NULL;
	}
	return DGEINFO_to_quasi_func(ei);
}


RMAT * DG::get_sch_mat(IN POLY const* p)
{
	RMAT * sch = m_sch_mat.get(POLY_id(*p));
	if (sch == NULL) {
		sch = (RMAT*)xmalloc(sizeof(RMAT));
		sch->init(1, POLY_domain(*p)->get_col_size());
		m_sch_mat.set(POLY_id(*p), sch);
	}
	return sch;
}


void DG::set_poly(IN VERTEX * v, IN POLY * p)
{
	IS_TRUE0(v != NULL && p != NULL);
	VERTEX_info(v) = p;
}


POLY const* DG::get_poly(IN VERTEX const* v) const
{
	IS_TRUE0(v != NULL);
	return (POLY*)VERTEX_info(v);
}
//END DG



//
//START DEP_POLY_LIST
//
//Compute the intersection between two list of polyhedra.
void DEP_POLY_LIST::intersect(IN DEP_POLY_LIST & dpl)
{
	DEP_POLY tmp;
	DEP_POLY_LIST tlst;
	for (DEP_POLY const* dp1 = this->get_head();
		 dp1 != NULL; dp1 = this->get_next()) {
		for (DEP_POLY const* dp2 = dpl.get_head();
			 dp2 != NULL; dp2 = dpl.get_next()) {
			tmp.copy(*dp1);
			tmp.intersect(*dp2);
			if (!tmp.is_empty(false, NULL)) {
				tlst.append_tail(new DEP_POLY(tmp));
			}
		}
	}
	free_elem();
	copy(tlst);
	tlst.clean();
}


/* Return true if there is not empty for intersection of two list of polyhedra.
Keep original dep-poly list unchanged.
NOTICE: Each variables of dependence polyhedron must be positive. */
bool DEP_POLY_LIST::is_intersect_empty(IN DEP_POLY_LIST & dpl)
{
	DEP_POLY tmp;
	DEP_POLY_LIST tlst;
	for (DEP_POLY const* dp1 = this->get_head();
		 dp1 != NULL; dp1 = this->get_next()) {
		for (DEP_POLY const* dp2 = dpl.get_head();
			 dp2 != NULL; dp2 = dpl.get_next()) {
			tmp.copy(*dp1);
			tmp.intersect(*dp2);
			if (!tmp.is_empty(false, NULL)) {
				return false;
			}
		}
	}
	return true;
}


bool DEP_POLY_LIST::is_empty(bool keepit, VC_MAT const* vc)
{
	bool b = true;
	for (DEP_POLY * dp = this->get_head();
		 dp != NULL; dp = this->get_next()) {
		b &= dp->is_empty(keepit, vc);
	}
	return b;
}
//END DEP_POLY_LIST




//
//START DEP_POLY
//
//Polyhedral Operation: intersection between polyhedra.
void DEP_POLY::copy(IN DEP_POLY const& dp)
{
	RMAT::copy(dp);
	rhs_idx = dp.rhs_idx;
	flag = dp.flag;
	id = dp.id;
}


void DEP_POLY::copy(IN RMAT const& r, UINT rhs_idx)
{
	RMAT::copy(r);
	this->rhs_idx = rhs_idx;
}


void DEP_POLY::intersect(IN RMAT const& r)
{
	intersect((DEP_POLY const&)r);
}


void DEP_POLY::intersect(IN DEP_POLY const& dp)
{
	if (dp.get_row_size() == 0) {
		clean();
		return;
	}
	IS_TRUE0(dp.get_col_size() == get_col_size() &&
			 dp.rhs_idx == rhs_idx);
	grow_row(dp, 0, dp.get_row_size() - 1);
	//LINEQ lineq(this, rhs_idx);
	//if (!lineq.reduce(*this, rhs_idx, true)) {
	//	//Remove redundant constrains.
	//	this->clean();
	//}
}


/*
Return true if there is no rational point was inside polyhedra.
'keepit': it is true if one expect to keep the dep-poly unchanged.
*/
bool DEP_POLY::is_empty(bool keepit, VC_MAT const* vc)
{
	//Eliminate variable via FME.
	if (this->get_row_size() == 0) {
		return true;
	}

	//Reform i+j<=1+M+N to be i+j-M-N<=1
	LINEQ lin(NULL);
	RMAT * coeff = this;
	RMAT tmp;
	if (keepit) {
		tmp.copy(*this);
		coeff = &tmp;
	}
	UINT nv = DEP_POLY_rhs_idx(*this);
	if (DEP_POLY_rhs_idx(*this) != coeff->get_col_size() - 1) {
		lin.move2var(*coeff, rhs_idx,
					DEP_POLY_rhs_idx(*this) + 1,
					coeff->get_col_size() - 1, NULL, NULL);
	}
	if (!lin.reduce(*coeff, coeff->get_col_size() - 1, true)) {
		return true;
	}
	if (coeff->get_row_size() == 0) {
		//In conservative purpose, the polyhedron is not
		//empty even if there are only redundant constrains.
		return false;
	}

	INT num_of_var = DEP_POLY_rhs_idx(*this);
	RMAT lvc(num_of_var, num_of_var + 1);
	if (vc != NULL) {
		IS_TRUE0(lvc.get_row_size() == vc->get_row_size() &&
				 lvc.get_col_size() == vc->get_col_size());
		lvc.copy(*vc);
	} else {
		for (INT i = 0; i < num_of_var; i++) {
			lvc.set(i, i, -1);
		}
	}
	RMAT eq;
	return !lin.has_solution(*coeff, eq, lvc,
					DEP_POLY_rhs_idx(*this), true, true);
}


//Remove the last local variable.
void DEP_POLY::remove_local_var()
{
	UINT const dp_rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT const to_lv_idx = dp_rhs_idx - 1;
	UINT const from_lv_idx = to_lv_idx / 2;
	this->del_col(to_lv_idx);
	this->del_col(from_lv_idx);
	DEP_POLY_rhs_idx(*this) -= 2;
}


//Remove loop.
//'iv_idx': index of given loop index variable.
void DEP_POLY::remove_loop(UINT iv_idx)
{
	UINT const dp_rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT const num_iv_of_from = dp_rhs_idx / 2;
	this->del_col(iv_idx + num_iv_of_from);
	this->del_col(iv_idx);
	DEP_POLY_rhs_idx(*this) -= 2;
}


void DEP_POLY::insert_loop_before(UINT iv_idx)
{
	UINT const dp_rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT const num_iv_of_from = dp_rhs_idx / 2;
	this->insert_cols_before(iv_idx + num_iv_of_from, 1);
	this->insert_cols_before(iv_idx, 1);
	DEP_POLY_rhs_idx(*this) += 2;
}


void DEP_POLY::insert_local_var(OUT UINT * lv1_idx, OUT UINT * lv2_idx)
{
	UINT const dp_rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT const to_rhs_idx = dp_rhs_idx;
	UINT const from_rhs_idx = dp_rhs_idx / 2;
	this->insert_cols_before(to_rhs_idx, 1); //last part
	this->insert_cols_before(from_rhs_idx, 1); //first part
	DEP_POLY_rhs_idx(*this) += 2;
	if (lv1_idx != NULL) {
		*lv1_idx = from_rhs_idx;
	}
	if (lv2_idx != NULL) {
		*lv2_idx = DEP_POLY_rhs_idx(*this) - 1;
	}
}


void DEP_POLY::elim_aux_var(IN POLY const& from, IN POLY const& to)
{
	IS_TRUE(from.get_num_of_var() == to.get_num_of_var() &&
			from.get_num_of_param() == to.get_num_of_param() &&
			from.get_num_of_localvar() == to.get_num_of_localvar(),
			("iteration space must be isomorphism"));
	IS_TRUE0(DEP_POLY_rhs_idx(*this) == 2 * from.get_num_of_var());
	UINT const dp_rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT const l = dp_rhs_idx / 2;

	LINEQ lineq(NULL);
	lineq.set_param(this, dp_rhs_idx);
	for (UINT i = dp_rhs_idx - 1; i >= l; i--) {
		RMAT res;
		if (!lineq.fme(i, res, false)) {
			IS_TRUE(0, ("system is inconsistency!"));
			return;
		}
		//Very important!! Update information of LINEQ system.
		*(RMAT*)this = res;
	}

	//Remove columns of auxilary variable.
	this->del_col(l,  dp_rhs_idx - 1);
	DEP_POLY_rhs_idx(*this) = l;
}


void DEP_POLY::dump()
{
	FILE * h = fopen(DUMP_FILE_NAME, "a+");
	dump(h, 4);
	fclose(h);
}


void DEP_POLY::dump(FILE * h, UINT indent)
{
	UINT i;
	CHAR buf[64];
	UINT rhs_idx = DEP_POLY_rhs_idx(*this);
	UINT nvar = get_num_of_from_iv() + get_num_of_to_iv();
	for (i = 0; i < get_row_size(); i++) {
		UINT j;
		fprintf(h, "\n");
		for (j = 0; j < indent; j++) { fprintf(h, " "); }
		for (j = 0; j < nvar; j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		fprintf(h, " <= ");
		for (j = rhs_idx; j < get_col_size(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		//Print inequality symbol.
		fprintf(h, "  //  ");
		UINT k = 0;
		bool has_prt = false;
		bool first = true;
		bool is_from_var = true;
		for (j = 0; j < nvar; j++, k++) {
			if (k >= get_num_of_from_iv()) {
				k = 0;
				is_from_var = false;
			}
			if (get(i, j) != 0) {
				CHAR * c = format_rational(get(i, j), buf, true);
				if (!first) {
					fprintf(h, " + ");
				}
				if (first) {
					first = false;
				}

				if (get(i, j) != 1 && get(i, j) != -1) {
					fprintf(h, "%s*%s%d", c, is_from_var?"i":"i'", k);
				} else {
					fprintf(h, "%s%s%d", c, is_from_var?"i":"i'", k);
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}

		has_prt = false;
		fprintf(h, " <= ");

		//Print global constant symbol on RHS.
		k = 0;
		for (j = rhs_idx; j < get_col_size(); j++, k++) {
			if (get(i, j) != 0) {
				if (j == rhs_idx) {
					//Print constant.
					CHAR * c = format_rational(get(i, j), buf, false);
					fprintf(h, "%s", c);
				} else {
					//Print global constant symbol.
					CHAR * c = format_rational(get(i, j), buf, true);
					fprintf(h, " + ");
					if (get(i, j) != 1 && get(i, j) != -1) {
						fprintf(h, "%s*%s%d", c, "g", k);
					} else {
						fprintf(h, "%s%s%d", c, "g", k);
					}
				}
				has_prt = true;
			}
		} //end for
		if (!has_prt) {
			fprintf(h, "0");
		}
	} //end for each row
}
//END DEP_POLY



//
//START DEP_POLY_HASH
//
DPVEC * DEP_POLY_HASH::find(IN POLY const& from, IN POLY const& to,
							IN ACC_MAT const& am1, IN ACC_MAT const& am2)
{
	REF_HASH tmp(POLY_id(from), POLY_id(to));
	REF_HASH * rf;
	if (!STMT_HASH::find(&tmp, &rf)) {
		return NULL;
	}
	DPVEC tmp2(ACC_MAT_id(am1), ACC_MAT_id(am2));
	DPVEC * dpvec;
	if (rf->find(&tmp2, &dpvec)) {
		return dpvec;
	}
	return NULL;
}


/* Return the DPVEC record in hash-table, or inserting 'dp' into table if
there is no this item in the table.
'dp': the DPVEC want to inserted. */
DPVEC * DEP_POLY_HASH::append(IN POLY const& from, IN POLY const& to,
							  IN ACC_MAT const& am1, IN ACC_MAT const& am2)
{
	REF_HASH tmp(POLY_id(from), POLY_id(to));
	REF_HASH * rf;
	DPVEC * dp = new DPVEC(ACC_MAT_id(am1), ACC_MAT_id(am2));
	if (!STMT_HASH::find(&tmp, &rf)) {
		rf = new REF_HASH(POLY_id(from), POLY_id(to));
		STMT_HASH::append(rf);
		rf->append(dp);
		return dp;
	}
	DPVEC * ret = rf->append(dp);
	IS_TRUE(dp == ret, ("there exist one DPVEC."));
	return dp;
}
//END DEP_POLY_HASH



//
//START DPVEC
//
DPVEC::DPVEC(UINT from_id, UINT to_id)
{
	from_acc_mat_id = from_id;
	to_acc_mat_id = to_id;
}


DPVEC::~DPVEC()
{
	free_elem();
}


/* Return true if there is not empty for intersection of two
list of polyhedra. Keep original dep-poly list unchanged.

'is_cross_depth': true if one intends perform intersection
	of dependence polyhedrons in between different depths.
	And this will obtain the most conservative result.

NOTICE: Each variables of dependence polyhedron must be positive. */
bool DPVEC::is_intersect_empty(IN DPVEC const& dpvec,
							bool is_cross_depth) const
{
	DEP_POLY_LIST * my_dp;
	DEP_POLY_LIST * his_dp;
	INT u = MAX(get_last_idx(), dpvec.get_last_idx());
	if (is_cross_depth) {
		for (INT i = u; i >= 0; i--) {
			for (INT j = 0; j <= u; j++) {
				my_dp = this->get(i);
				his_dp = dpvec.get(j);
				if (my_dp != NULL &&
					his_dp != NULL &&
					!my_dp->is_intersect_empty(*his_dp)) {
					return false;
				}
			}
		}
	} else {
#ifdef ONLY_CHECK_INNERMOST_DEPTH
		my_dp = this->get_innermost();
		his_dp = dpvec.get_innermost();
		if (my_dp != NULL &&
			his_dp != NULL &&
			!my_dp->is_intersect_empty(*his_dp)) {
			return false;
		}
#else
		for (INT i = u; i >= 0; i--) {
			my_dp = this->get(i);
			his_dp = dpvec.get(i);
			if (my_dp != NULL && his_dp != NULL) {
				if (!my_dp->is_intersect_empty(*his_dp)) {
					return false;
				}
			}
		}
#endif
	}
	return true;
}


void DPVEC::free_elem()
{
	for (INT i = 0; i <= this->get_last_idx(); i++) {
		DEP_POLY_LIST * dp = this->get(i);
		if (dp != NULL) {
			delete dp;
		}
	}
}


//This function would NOT allocate new objects, so
//the caller could not delete pointers in 'd'.
void DPVEC::copy(DPVEC const& d)
{
	free_elem();
	SVECTOR<DEP_POLY_LIST*>::copy(d);
}


DEP_POLY_LIST * DPVEC::get_innermost() const
{
	DEP_POLY_LIST * dpl;
	for (INT i = this->get_last_idx(); i >= 0; i--) {
		if ((dpl = this->get(i)) != NULL) {
			return dpl;
		}
	}
	return NULL;
}


void DPVEC::dump()
{
	FILE * h = fopen(DUMP_FILE_NAME, "a+");
	dump(h, 4);
	fclose(h);
}


void DPVEC::dump(FILE * h, UINT indent)
{
	for (INT i = 0; i <= get_last_idx(); i++) {
		DEP_POLY_LIST * dpl = get(i);
		if (dpl != NULL) {
			fprintf(h, "\n");
			for (UINT j = 0; j < indent; j++) { fprintf(h, " "); }
			fprintf(h, "DEPTH%d : ", i);
			for (DEP_POLY * dp = dpl->get_head();
				 dp != NULL; dp = dpl->get_next()) {
				fprintf(h, "\n");
				for (UINT j = 0; j < indent; j++) { fprintf(h, " "); }
				UINT flag = DEP_POLY_flag(*dp);
				if (HAVE_FLAG(flag, DEP_LOOP_CARRIED)) {
					fprintf(h, "LOOP_CARR, ");
					REMOVE_FLAG(flag, DEP_LOOP_CARRIED);
				}
				if (HAVE_FLAG(flag, DEP_LOOP_INDEP)) {
					fprintf(h, "LOOP_INDEP");
					REMOVE_FLAG(flag, DEP_LOOP_INDEP);
				}
				IS_TRUE(flag == 0, ("still has flag?"));
				dp->dump(h, indent + 4);
			}
		}
	} //end for each depth.
}
//END DPVEC



//
//START DEP_POLY_MGR
//
DEP_POLY_MGR::DEP_POLY_MGR()
{
}


DEP_POLY_MGR::~DEP_POLY_MGR()
{
}


void DEP_POLY_MGR::clean()
{
	m_dh.clean();
}


//Build execute conflict condition.
void DEP_POLY_MGR::_build_acc_exec_cond(IN POLY const& from,
										IN POLY const& to,
										IN ACC_MAT const& from_acc,
										IN ACC_MAT const& to_acc,
										OUT RMAT & res)
{
	UINT const rhs_idx = POLY_domain_rhs_idx(from);
	UINT const nvar = from.get_num_of_var();
	UINT const dp_rhs_idx = nvar * 2;

	{
		/* Build conflict condition.
		One of accsess functions should be WRTIE.
		It is common for both loop-carried and loop-independent.
		Acc(from) == Acc(to) */
		IS_TRUE0(from_acc.is_homo(to_acc));
		RMAT eq(from_acc.get_row_size(), res.get_col_size());
		for (UINT i = 0; i < from_acc.get_row_size(); i++) {
			UINT j;
			for (j = 0; j < nvar; j++) {
				eq.set(i, j, from_acc.get(i, j));
				eq.set(i, j + nvar, -(to_acc.get(i, j)));
			}
			UINT k = 0;
			for (j = rhs_idx; j < from_acc.get_col_size(); j++, k++) {
				eq.set(i, dp_rhs_idx + k,
						to_acc.get(i, j) - from_acc.get(i, j));
			}
		}
		LINEQ linq(&res, dp_rhs_idx);
		linq.append_eq(eq);
	}
}


//Build execute conflict condition to domain.
void DEP_POLY_MGR::_build_domain_exec_cond(IN POLY const& from,
										IN POLY const& to,
										OUT RMAT & res)
{
	UINT const rhs_idx = POLY_domain_rhs_idx(from);
	UINT const nvar = from.get_num_of_var();
	DOMAIN_MAT const* from_domain = POLY_domain(from);
	DOMAIN_MAT const* to_domain = POLY_domain(to);
	UINT const dp_rhs_idx = nvar * 2;

	{
		UINT row_start = res.get_row_size();
		res.grow_row(from_domain->get_row_size() +
					 to_domain->get_row_size());
		/* Build execution condition. It is common for both
		loop-carried and loop-independent.
		The dependence pair from->to define a Cartesian
		product space of dimension
		(dFrom+dG+1)+(dTo+dG+1), where dFrom and dTo is
		index-variable space(i,j,k...),
		dG is global-variable space, '1' is constant column. */
		UINT i;
		//Insert domain info of 'from'.
		for (i = 0; i < from_domain->get_row_size(); i++) {
			UINT j;
			for (j = 0; j < nvar; j++) {
				res.set(row_start + i, j,
						from_domain->get(i, j));
			}
			UINT k = 0;
			for (j = rhs_idx; j < from_domain->get_col_size(); j++, k++) {
				res.set(row_start + i,
						dp_rhs_idx + k,
						from_domain->get(i, j));
			}
		}

		//Insert domain info of 'to'.
		row_start += from_domain->get_row_size();
		UINT col_start = nvar;
		for (i = 0; i < to_domain->get_row_size(); i++) {
			UINT j;
			for (j = 0; j < nvar; j++) {
				res.set(row_start + i,
						col_start + j,
						to_domain->get(i, j));
			}
			UINT k = 0;
			for (j = rhs_idx; j < to_domain->get_col_size(); j++, k++) {
				res.set(row_start + i,
						dp_rhs_idx + k,
						to_domain->get(i, j));
			}
		}
	}
}


DEP_POLY_LIST * DEP_POLY_MGR::conjoin(IN DEP_POLY const& c1,
									IN DEP_POLY const& c2,
									IN VC_MAT const* vc)
{
	DEP_POLY_LIST * dpl = new DEP_POLY_LIST();
	DEP_POLY * dp = new DEP_POLY(c1);
	dp->intersect(c2);
	if (!dp->is_empty(false, vc)) {
		DEP_POLY_flag(*dp) |= DEP_POLY_flag(c2);
		dpl->append_tail(dp);
		return dpl;
	}
	dp->copy(c1);
	dpl->append_tail(dp);
	dp = new DEP_POLY(c2);
	dpl->append_tail(dp);
	return dpl;
}


/* Build Syntax Order Relation:
(¦Âfrom) == (¦Âto), depth is in 0~p-1.
(¦Âfrom)+1¡Ü(¦Âto), at depth p.
*/
void DEP_POLY_MGR::_build_context_relation(IN POLY const& from,
										IN POLY const& to,
										OUT RMAT & res)
{

}


void DEP_POLY_MGR::revise_neg_iv_cs(IN POLY const& from,
									IN POLY const& to,
									IN OUT DEP_POLY & cs)
{
	SVECTOR<INT> coeff;
	build_map_iv_coeff(from, to, coeff);
	INT li = coeff.get_last_idx();
	IS_TRUE0((INT)(from.get_num_of_var() +
				to.get_num_of_var()) == li + 1);
	for (INT i = 0; i <= li; i++) {
		if (coeff.get(i) < 0) {
			/* If coefficient is negative, the map code
			would be generated during code generation,
			e.g:
				for (i' = -100; i' <= 0; i'++)
					i = -i'
					A[i] = ...
			*/
			cs.neg_of_cols(i, i);
		}
	}
}


/* Build dependency polyhedra from->to of given array access pair.
'from': source of dependence.
'to': target of dependence.
'dpvec': contained computed dependence polyhedra.
'is_reverse': build the dependence of reversed direction, to->from.
*/
void DEP_POLY_MGR::build(IN POLY const& from,
						IN POLY const& to,
						IN ACC_MAT const& from_acc,
						IN ACC_MAT const& to_acc,
						IN VC_MAT const* vc,
						OUT DPVEC & dpvec,
						bool is_reverse)
{
	IS_TRUE0(POLY_domain_rhs_idx(from) == POLY_domain_rhs_idx(to));
	UINT const nvar = from.get_num_of_var();
	UINT const dp_rhs_idx = nvar * 2;
	DOMAIN_MAT const* from_domain = POLY_domain(from);
	DOMAIN_MAT const* to_domain = POLY_domain(to);
	INT const max_depth =
		MIN(POLY_sche(from)->get_stmt_depth(),
			POLY_sche(to)->get_stmt_depth());
	IS_TRUE0(max_depth >= (INT)0);
	INT first_diff_depth = -1;
	for (INT m = 0; m <= max_depth; m++) {
		INT from_order = POLY_sche(from)->get_stmt_order(m);
		INT to_order = POLY_sche(to)->get_stmt_order(m);
		IS_TRUE0(from_order >= 0 && to_order >= 0);
		if (from_order != to_order) {
			first_diff_depth = m;
			break;
		}
	}

	UINT col_size = nvar * 2 + 1 + from.get_num_of_param();
	RMAT context(1, col_size);
	_build_context_relation(from, to, context);
	if (first_diff_depth == 0) {
		DEP_POLY * dp = new DEP_POLY(1, col_size);
		DEP_POLY_flag(*dp) = DEP_LOOP_INDEP;
		DEP_POLY_rhs_idx(*dp) = dp_rhs_idx;
		build_syn_order_relation(from,
							to, is_reverse,
							first_diff_depth, *dp);
		dp->intersect(context);
		DEP_POLY_LIST * dpl = new DEP_POLY_LIST();
		dpl->append_tail(dp);
		dpvec.set(first_diff_depth, dpl);
		goto FIN;
	}

	{
	RMAT domain(1, col_size);
	_build_domain_exec_cond(from, to, domain);
	RMAT acc(context);
	_build_acc_exec_cond(from, to, from_acc, to_acc, acc);
	RMAT comm_cs(domain);
	comm_cs.grow_row(acc, 0, acc.get_row_size() - 1);
	INT u = first_diff_depth == -1 ? max_depth : first_diff_depth;
	for (INT d = 1; d <= u; d++) {
		RMAT lp_ca(1, col_size), lp_indep(1, col_size);
		DEP_POLY tmp_ca, tmp_indep;
		build_loop_carried(from, to, is_reverse, d, lp_ca);
		tmp_ca.copy(comm_cs, dp_rhs_idx);
		tmp_ca.grow_row(lp_ca, 0, lp_ca.get_row_size() - 1);
		if (!tmp_ca.is_empty(false, vc)) {
			tmp_ca.copy(domain, dp_rhs_idx);
			revise_neg_iv_cs(from, to, tmp_ca);
			tmp_ca.grow_row(acc, 0, acc.get_row_size() - 1);
			tmp_ca.grow_row(lp_ca, 0, lp_ca.get_row_size() - 1);
		} else {
			tmp_ca.clean();
		}

		if (first_diff_depth >= 0) {
			build_loop_independent(from, to, is_reverse, d, lp_indep);
			build_syn_order_relation(from, to, is_reverse, d, lp_indep);
			tmp_indep.copy(comm_cs, dp_rhs_idx);
			tmp_indep.grow_row(lp_indep, 0, lp_indep.get_row_size() - 1);
			if (!tmp_indep.is_empty(false, vc)) {
				tmp_indep.copy(domain, dp_rhs_idx);
				revise_neg_iv_cs(from, to, tmp_indep);
				tmp_indep.grow_row(acc, 0, acc.get_row_size() - 1);
				tmp_indep.grow_row(lp_indep, 0,
								lp_indep.get_row_size() - 1);
			} else {
				tmp_indep.clean();
			}
		}
		if (tmp_ca.size() > 0 && tmp_indep.size() > 0) {
			DEP_POLY_flag(tmp_ca) = DEP_LOOP_CARRIED|DEP_LOOP_INDEP;
			DEP_POLY dp_ca(tmp_ca);
			DEP_POLY_flag(tmp_indep) = DEP_LOOP_INDEP;
			DEP_POLY dp_indep(tmp_indep);
			DEP_POLY_LIST * dpl = conjoin(dp_ca, dp_indep, vc);
			dpvec.set(d, dpl);
		} else if (tmp_ca.size() > 0) {
			DEP_POLY_flag(tmp_ca) = DEP_LOOP_CARRIED;
			DEP_POLY * dp = new DEP_POLY(tmp_ca);
			DEP_POLY_LIST * dpl = new DEP_POLY_LIST();
			dpl->append_tail(dp);
			dpvec.set(d, dpl);
		} else if (tmp_indep.size() > 0) {
			DEP_POLY_flag(tmp_indep) = DEP_LOOP_INDEP;
			DEP_POLY * dp = new DEP_POLY(tmp_indep);
			DEP_POLY_LIST * dpl = new DEP_POLY_LIST();
			dpl->append_tail(dp);
			dpvec.set(d, dpl);
		}
	} //end for
	}
FIN:
	return;
}


DPVEC * DEP_POLY_MGR::get_dpvec(IN POLY const& from,
								IN POLY const& to,
								IN ACC_MAT const& am1,
								IN ACC_MAT const& am2)
{
	return m_dh.find(from, to, am1, am2);
}


/* Build equalities which are commonly used in both LOOP CARRIRED and
LOOP INDEPENDENT analysis:
	Causality Equalities: from(A|¦£) == to(A|¦£), depth is in 1~p-1.

'include_depth': build causality condition from depth 1 to p-1
	or to p if the parameter is true.
*/
void DEP_POLY_MGR::_build_common_equation(POLY const& from,
										POLY const& to,
										INT depth,
										bool include_depth,
										OUT RMAT & res)
{
	DOMAIN_MAT const* from_domain = POLY_domain(from);
	SCH_MAT const* from_sch = POLY_sche(from);
	SCH_MAT const* to_sch = POLY_sche(to);
	UINT const nvar = from.get_num_of_var();
	UINT const dp_rhs_idx = nvar * 2;

	LINEQ linq(&res, dp_rhs_idx);
	//Build equalities: from(A|¦£) == to(A|¦£), depth is in 1~depth-1.
	if (!include_depth) {
		depth--;
	}
	for (INT u = 1; u <= (INT)depth; u++) {
		RMAT eq(1, res.get_col_size());

		{
			//Build Equality: Afrom - Ato == (-¦£from) + (¦£to).
			UINT row_pos = from_sch->compute_loop_row_pos(u);
			UINT j;
			//Set Values: Afrom - Ato <= ...
			for (j = 0; j < nvar; j++) {
				eq.set(0, j, from_sch->get(row_pos, j));
				eq.set(0, j + nvar, -(to_sch->get(row_pos, j)));
			}

			//Set Constant.
			eq.set(0, dp_rhs_idx, 0);

			//Set Values: ... == (-¦£from) + (¦£to).
			UINT k = 1;
			for (j = from_sch->get_syn_order_idx() + 1;
				 j < from_sch->get_col_size(); j++, k++) {
				eq.set(0, dp_rhs_idx + k,
					to_sch->get(row_pos, j) - from_sch->get(row_pos, j));
			}
		}
		linq.append_eq(eq);
	}
}


//Build Loop Carried Dependence: from(A|¦£)p + 1 ¡Üto(A|¦£)p at depth p.
void DEP_POLY_MGR::build_loop_carried(POLY const& from,
									POLY const& to,
									bool is_reverse,
									UINT depth,
									OUT RMAT & res)
{
	if (depth == 0) { return; }
	DOMAIN_MAT * from_domain = POLY_domain(from);
	IS_TRUE0(from_domain->get_col_size() ==
			 POLY_domain(to)->get_col_size());
	UINT const nvar = from.get_num_of_var();
	UINT const dp_rhs_idx = nvar * 2;
	UINT const col_size = dp_rhs_idx + 1 + from.get_num_of_param();

	//Build relations that depth is in 1~p-1.
	_build_common_equation(from, to, depth, false, res);

	/*
	Depth is p
	Build inequalities, if 'is_reverse' is false:
		Afrom + (¦£from) + 1 ¡Ü Ato + (¦£to), and reform to,
		 Afrom - Ato ¡Ü -1 + (-¦£from) + (+¦£to),
	else
		Afrom + (¦£from) ¡Ý Ato + (¦£to) + 1, and reform to,
		-Afrom + Ato ¡Ü -1 + (+¦£from) + (-¦£to).
	*/
	SCH_MAT * from_sch = POLY_sche(from);
	SCH_MAT * to_sch = POLY_sche(to);
	IS_TRUE0(depth <= from_sch->get_stmt_depth() &&
			 depth <= to_sch->get_stmt_depth());
	if (depth > 0) {
		UINT row_start = res.get_row_size();
		res.grow_row(1);
		INT row_pos = from_sch->compute_loop_row_pos(depth);
		IS_TRUE0(row_pos > 0);
		UINT j;
		for (j = 0; j < nvar; j++) {
			res.set(row_start, j, from_sch->get(row_pos, j));
			res.set(row_start, j + nvar, -(to_sch->get(row_pos, j)));
		}
		res.set(row_start, dp_rhs_idx, -1);
		UINT k = 1;
		for (j = from_sch->get_syn_order_idx() + 1;
			 j < from_sch->get_col_size(); j++, k++) {
			res.set(row_start, dp_rhs_idx + k,
					to_sch->get(row_pos, j) - from_sch->get(row_pos, j));
		}
		if (is_reverse) {
			for (j = 0; j < res.get_col_size(); j++) {
				if (j == dp_rhs_idx) {
					continue;
				}
				res.set(row_start, j, -res.get(row_start, j));
			}
		}
	}
}


//Build Loop Independent Dependence Relation: from(A|¦£) == to(A|¦£),
//depth is in 1~p, where p is stmt-depth.
void DEP_POLY_MGR::build_loop_independent(POLY const& from,
										POLY const& to,
										bool is_reverse,
										UINT depth,
										OUT RMAT & res)
{
	if (depth == 0) { return; }
	IS_TRUE0(POLY_domain(from)->get_col_size() ==
			 POLY_domain(to)->get_col_size());
	IS_TRUE0(depth <= POLY_sche(from)->get_stmt_depth() &&
			 depth <= POLY_sche(to)->get_stmt_depth());
	UINT const col_size =
		from.get_num_of_var() * 2 + 1 + from.get_num_of_param();
	res.reinit(1, col_size);
	_build_common_equation(from, to, depth, true, res);
}


/* Build Syntax Order Relation:
(¦Âfrom) == (¦Âto), depth is in 0~p-1.
(¦Âfrom)+1¡Ü(¦Âto), at depth p.
*/
void DEP_POLY_MGR::build_syn_order_relation(POLY const& from,
											POLY const& to,
											bool is_reverse,
											UINT depth,
											OUT RMAT & res)
{
	SCH_MAT const* from_sch = POLY_sche(from);
	SCH_MAT const* to_sch = POLY_sche(to);
	IS_TRUE0(depth <= from_sch->get_stmt_depth() &&
			 depth <= to_sch->get_stmt_depth());
	INT from_order = from_sch->get_stmt_order(depth);
	INT to_order = to_sch->get_stmt_order(depth);
	IS_TRUE0(from_order >= 0 && to_order >= 0);
	UINT const dp_rhs_idx = from.get_num_of_var() * 2;

	/* TODO: Quickly check.
	There is not loop-independent dependence
	if (¦Âfrom) != (¦Âto) while	depth is in 1~p-1. */
	if (depth > 0) {
		LINEQ linq(&res, dp_rhs_idx);
		for (INT u = 0; u <= (INT)depth - 1; u++) {
			INT to_so = to_sch->get_stmt_order(u);
			INT from_so = from_sch->get_stmt_order(u);
			IS_TRUE0(to_so >= 0 && from_so >= 0);
			{
				RMAT eq(1, res.get_col_size());
				eq.set(0, dp_rhs_idx, to_so - from_so);
				linq.append_eq(eq);
			}
		}
	}

	//Depth is p
	res.grow_row(1);
	UINT row_start = res.get_row_size() - 1;
	if (is_reverse) {
		//Build the reversed relation from<-to: (¦Âfrom)¡Ý(¦Âto)+1.
		res.set(row_start, dp_rhs_idx, from_order - to_order - 1);
	} else {
		//Build the relation from->to: (¦Âfrom)+1¡Ü(¦Âto).
		res.set(row_start, dp_rhs_idx, to_order - from_order - 1);
	}
}


//Compute dependenc vector and add into hash table.
DPVEC * DEP_POLY_MGR::build_dep_poly(POLY const& from,
									POLY const& to,
									ACC_MAT const& from_acc,
									ACC_MAT const& to_acc,
									VC_MAT const* vc,
									bool is_reverse)
{
	DPVEC lcldpvec(0, 0);
	build_dep_poly(from, to, from_acc,
				  to_acc, vc, lcldpvec, is_reverse);
	if (lcldpvec.get_last_idx() == -1) {
		return NULL;
	}

	//Add or update DPVEC.
	DPVEC * dpvec = m_dh.find(from, to, from_acc, to_acc);
	if (dpvec == NULL) {
		dpvec = m_dh.append(from, to, from_acc, to_acc);
	}
	dpvec->copy(lcldpvec);
	lcldpvec.clean();
	return dpvec;
}


//Compute dependenc vector and add into hash table.
void DEP_POLY_MGR::build_dep_poly(POLY const& from,
								POLY const& to,
								ACC_MAT const& from_acc,
								ACC_MAT const& to_acc,
								VC_MAT const* vc,
								OUT DPVEC & dpvec,
								bool is_reverse)
{
	if (&from == &to && &from_acc == &to_acc) {
		/* TODO:Check cyclic dep.
		e.g:
		  for t
		    for i
			  a[i] = f(x) cyclic-output-dep
		if (has_no_side_effect(f(x)) &&
			is_cyclic_invariant(f(x))) return NULL;
		*/
	}
	ACC_MGR const* mgr1 = POLY_acc_mgr(from);
	ACC_MGR const* mgr2 = POLY_acc_mgr(to);
	if (ACC_MAT_arr_id(from_acc) != ACC_MAT_arr_id(to_acc) ||
		from_acc.get_row_size() != to_acc.get_row_size() ||
		(mgr1->is_read(from_acc) && mgr2->is_read(to_acc))) {
		return;
	}
	build(from, to, from_acc, to_acc, vc, dpvec, is_reverse);
}


void DEP_POLY_MGR::get_all_dep_poly(IN OUT LIST<DEP_POLY*> & lst)
{
	INT c, d;
	for (REF_HASH * rf = m_dh.get_first(c);
		 rf != NULL; rf = m_dh.get_next(c)) {
		for (DPVEC * dpvec = rf->get_first(d);
			 dpvec != NULL; dpvec = rf->get_next(d)) {
			for (INT i = 0; i <= dpvec->get_last_idx(); i++) {
				DEP_POLY_LIST * dpl = dpvec->get(i);
				if (dpl != NULL) {
					for (DEP_POLY * dp = dpl->get_head();
						 dp != NULL; dp = dpl->get_next()) {
						lst.append_tail(dp);
					}
				}
			}
		}
	}
}


/* Add one local variable, the column is next to 'rhs_idx'.
and this operation will affect domain, access matrix.
Return column position of new local variable.
NOTICE: The operation of DEP_POLY will generate two local variable,
	but we only return the idx of the second. */
void DEP_POLY_MGR::insert_local_var(OUT UINT * lv1_idx, OUT UINT * lv2_idx)
{
	INT new_lv1 = -1;
	INT new_lv2 = -1;
	INT rhs_idx = -1;
	LIST<DEP_POLY*> lst;
	get_all_dep_poly(lst);
	for (DEP_POLY * dp = lst.get_head();
		 dp != NULL; dp = lst.get_next()) {
		if (rhs_idx == -1) { rhs_idx = DEP_POLY_rhs_idx(*dp); }
		IS_TRUE0(rhs_idx == (INT)DEP_POLY_rhs_idx(*dp));
		INT lv1, lv2;
		dp->insert_local_var((UINT*)&lv1, (UINT*)&lv2);
		if (new_lv1 == -1) { new_lv1 = lv1; new_lv2 = lv2; }
		IS_TRUE0(lv1 == new_lv1 && lv2 == new_lv2);
	}
	if (lv1_idx != NULL) {
		*lv1_idx = new_lv1;
	}
	if (lv2_idx != NULL) {
		*lv2_idx = new_lv2;
	}
}


void DEP_POLY_MGR::insert_loop_before(UINT iv_idx)
{
	INT rhs_idx = -1;
	LIST<DEP_POLY*> lst;
	get_all_dep_poly(lst);
	for (DEP_POLY * dp = lst.get_head();
		 dp != NULL; dp = lst.get_next()) {
		if (rhs_idx == -1) { rhs_idx = DEP_POLY_rhs_idx(*dp); }
		IS_TRUE0(rhs_idx == (INT)DEP_POLY_rhs_idx(*dp));
		dp->insert_loop_before(iv_idx);
	}
}


void DEP_POLY_MGR::remove_loop(UINT iv_idx)
{
	LIST<DEP_POLY*> lst;
	get_all_dep_poly(lst);
	for (DEP_POLY * dp = lst.get_head();
		 dp != NULL; dp = lst.get_next()) {
		dp->remove_loop(iv_idx);
	}
}


void DEP_POLY_MGR::remove_local_var()
{
	LIST<DEP_POLY*> lst;
	get_all_dep_poly(lst);
	for (DEP_POLY * dp = lst.get_head();
		 dp != NULL; dp = lst.get_next()) {
		dp->remove_local_var();
	}
}


//Extract coefficient of map-iv matrix to dependence polyhedron.
void DEP_POLY_MGR::build_map_iv_coeff(POLY const& from,
									POLY const& to,
									OUT SVECTOR<INT> & coeff)
{
	SCH_MAT const* sm_from = POLY_sche(from);
	SCH_MAT const* sm_to = POLY_sche(to);
	VC_MAT const* map_iv = sm_from->get_map_iv();
	UINT k = 0;
	UINT d;
	for (d = 1; d < map_iv->get_row_size(); d++, k++) {
		IS_TRUE0(sm_from->map_depth2iv(d) >= 0);
		coeff.set(k, map_iv->get_val(d, sm_from->map_depth2iv(d)));
	}

	map_iv = sm_to->get_map_iv();
	for (d = 1; d < map_iv->get_row_size(); d++, k++) {
		IS_TRUE0(sm_to->map_depth2iv(d) >= 0);
		coeff.set(k, map_iv->get_val(d, sm_to->map_depth2iv(d)));
	}
}


//Return variable constrains if there exist negative one.
VC_MAT * DEP_POLY_MGR::build_vc(POLY const& from,
								POLY const& to,
								OUT VC_MAT & vc)
{
	SCH_MAT const* sm_from = POLY_sche(from);
	SCH_MAT const* sm_to = POLY_sche(to);
	IS_TRUE0(sm_from->get_num_of_var() == sm_to->get_num_of_var());

	SVECTOR<INT> coeff;
	build_map_iv_coeff(from, to, coeff);
	IS_TRUE0(coeff.get_last_idx() + 1 ==
			(INT)(sm_from->get_num_of_var() +
				  sm_from->get_num_of_var()));
	LINEQ lin(NULL);
	RMAT tmp;
	lin.init_vc(&coeff, tmp,
				sm_from->get_num_of_var() +
				sm_from->get_num_of_var());
	vc.copy(tmp);
	return &vc;
}


void DEP_POLY_MGR::dump(IN LIST<POLY*> & lst)
{
	C<POLY*> * it1;
	C<POLY*> * it2;
	FILE * h = fopen(DUMP_FILE_NAME, "a+");
	fprintf(h, "\nDEP_POLY_MGR :");
	for (POLY const* p1 = lst.get_head(&it1);
		 p1 != NULL; p1 = lst.get_next(&it1)) {
		for (POLY const* p2 = lst.get_head(&it2);
			 p2 != NULL; p2 = lst.get_next(&it2)) {
			ACC_MGR const* mgr1 = POLY_acc_mgr(*p1);
			ACC_MGR const* mgr2 = POLY_acc_mgr(*p2);
			LIST<ACC_MAT*> lst_1, lst_2;
			mgr1->get_read_refs(lst_1);
			mgr1->get_write_refs(lst_1);
			mgr2->get_read_refs(lst_2);
			mgr2->get_write_refs(lst_2);
			C<ACC_MAT*> * iit1;
			C<ACC_MAT*> * iit2;
			for (ACC_MAT const* am1 = lst_1.get_head(&iit1);
				 am1 != NULL; am1 = lst_1.get_next(&iit1)) {
				for (ACC_MAT const* am2 = lst_2.get_head(&iit2);
					 am2 != NULL; am2 = lst_2.get_next(&iit2)) {
					DPVEC * dpvec;
					if ((dpvec = get_dpvec(*p1, *p2, *am1, *am2)) != NULL) {
						fprintf(h, "\n\tBB%d:ACC%d -> BB%d:ACC%d",
								POLY_id(*p1),
								ACC_MAT_id(*am1),
								POLY_id(*p2),
								ACC_MAT_id(*am2));
						dpvec->dump(h, 8);
					}
				}
			}
		}
	}
	fprintf(h, "\n");
	fclose(h);
}
//END DEP_POLY_MGR



//
//START ACC_MAT
//
void ACC_MAT::insert_loop_before(UINT iv_idx)
{
	insert_col_before(iv_idx);
}


void ACC_MAT::insert_loop_after(UINT iv_idx)
{
	insert_col_before(iv_idx + 1);
}


void ACC_MAT::remove_loop(UINT iv_idx)
{
	del_col(iv_idx);
}


//Append loop index variable.
void ACC_MAT::surround_acc_by_loop()
{
	insert_col_before(0);
}


void ACC_MAT::dump(IN FILE * h,	IN SVECTOR<CHAR*> & var_name,
					POLY const& p, UINT indent)
{
	UINT i,j;
	CHAR buf[64];
	UINT rhs_idx = POLY_domain_rhs_idx(p);
	UINT nvar = p.get_num_of_var();
	for (i = 0; i < get_row_size(); i++) {
		//Print inequlity coeff.
		fprintf(h, "\n");
		for (UINT v = 0; v < indent; v++) { fprintf(h, " "); }
		for (j = 0; j < nvar; j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}
		fprintf(h, " + ");
		for (j = rhs_idx; j < get_col_size(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		//Print inequality symbol.
		fprintf(h, "  //  ");
		bool has_prt = false;
		for (j = 0; j < nvar; j++) {
			if (get(i, j) != 0) {
				CHAR * c = format_rational(get(i, j), buf, true);
				CHAR * n = var_name.get(j);
				fprintf(h, " + ");
				if (n == NULL) {
					fprintf(h, "%s%s%d", c, "i", j);
				} else {
					fprintf(h, "%s%s", c, n);
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}

		has_prt = false;
		fprintf(h, " + ");
		for (j = rhs_idx; j < get_col_size(); j++) {
			if (get(i, j) != 0) {
				if (j == rhs_idx) {
					CHAR * c = format_rational(get(i, j), buf, false);
					fprintf(h, "%s", c);
				} else {
					CHAR * c = format_rational(get(i, j), buf, true);
					CHAR * n = var_name.get(j);
					if (n == NULL) {
						fprintf(h, "%s%s%d", c, "ig", j);
					} else {
						fprintf(h, "%s%s", c, n);
					}
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}
	}
}
//END ACC_MAT



//
//START ACC_MGR
//
ACC_MGR::ACC_MGR()
{

}


ACC_MGR::~ACC_MGR()
{
	clean_data();
}


void ACC_MGR::clean_data()
{
	INT i;
	for (i = 0; i <= m_write_vec.get_last_idx(); i++) {
		ACC_MAT * q = m_write_vec.get(i);
		if (q != NULL) {
			delete q;
		}
	}
	for (i = 0; i <= m_read_vec.get_last_idx(); i++) {
		ACC_MAT * q = m_read_vec.get(i);
		if (q != NULL) {
			delete q;
		}
	}
	for (i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * q = m_map_arr_base_id2refs.get(i);
		if (q != NULL) {
			delete q;
		}
	}
}


void ACC_MGR::clean()
{
	clean_data();
	m_write_vec.clean();
	m_read_vec.clean();
	m_map_arr_base_id2refs.clean();
}


/* Add or update ACC_MAT to record each array referrences.
Return the ACC_MAT generated. */
ACC_MAT * ACC_MGR::set_ref(ACC_MAT const& acc_mat, bool is_read)
{
	ACC_MAT * p = NULL;
	if (is_read) {
		p = m_read_vec.get(ACC_MAT_id(acc_mat));
	} else {
		p = m_write_vec.get(ACC_MAT_id(acc_mat));
	}
	if (p != NULL) {
		p->copy(acc_mat);
		return p;
	}
	p = new ACC_MAT(acc_mat);
	if (is_read) {
		m_read_vec.set(ACC_MAT_id(*p), p);
	} else {
		m_write_vec.set(ACC_MAT_id(*p), p);
	}

	LIST<ACC_MAT*> * pp =
		m_map_arr_base_id2refs.get(ACC_MAT_arr_id(acc_mat));
	if (pp == NULL) {
		pp = new LIST<ACC_MAT*>();
		m_map_arr_base_id2refs.set(ACC_MAT_arr_id(acc_mat), pp);
	}
	pp->append_tail(p);
	return p;
}


void ACC_MGR::insert_loop_before(UINT iv_idx)
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * p = lst->get_head();
				 p != NULL; p = lst->get_next()) {
				p->insert_loop_before(iv_idx);
			}
		}
	}
}


void ACC_MGR::insert_loop_after(UINT iv_idx)
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * p = lst->get_head();
				 p != NULL; p = lst->get_next()) {
				p->insert_loop_after(iv_idx);
			}
		}
	}
}


void ACC_MGR::remove_loop(UINT iv_idx)
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * p = lst->get_head();
				 p != NULL; p = lst->get_next()) {
				p->remove_loop(iv_idx);
			}
		}
	}
}


void ACC_MGR::surround_acc_by_loop()
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * p = lst->get_head();
				 p != NULL; p = lst->get_next()) {
				p->surround_acc_by_loop();
			}
		}
	}
}


LIST<ACC_MAT*> * ACC_MGR::map_arr_id2refs(UINT arr_id)
{
	return m_map_arr_base_id2refs.get(arr_id);
}


UINT ACC_MGR::map_ref2arr_id(ACC_MAT const* acc_mat) const
{
	return ACC_MAT_arr_id(*acc_mat);
}


void ACC_MGR::copy(ACC_MGR const& am)
{
	clean();
	INT i;
	for (i = 0; i <= am.m_read_vec.get_last_idx(); i++) {
		ACC_MAT const* p = am.m_read_vec.get(i);
		if (p != NULL) {
			this->set_ref(*p, true);
		}
	}
	for (i = 0; i <= am.m_write_vec.get_last_idx(); i++) {
		ACC_MAT const* p = am.m_write_vec.get(i);
		if (p != NULL) {
			this->set_ref(*p, false);
		}
	}
}


void ACC_MGR::privatize(UINT iv_idx)
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * p = lst->get_head();
				 p != NULL; p = lst->get_next()) {
				p->grow_row(1);
				p->set(p->get_row_size() - 1, iv_idx, 1);
			}
		}
	}
}


void ACC_MGR::insert_local_var(UINT rhs_idx)
{
	for (INT i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			for (ACC_MAT * am = lst->get_head();
				 am != NULL; am = lst->get_next()) {
				am->insert_cols_before(rhs_idx, 1);
			}
		}
	}
}


bool ACC_MGR::is_read(IN ACC_MAT const& acc_mat) const
{
	if (m_read_vec.get(ACC_MAT_id(acc_mat)) != NULL) {
		return true;
	}
	return false;
}


bool ACC_MGR::is_write(IN ACC_MAT const& acc_mat) const
{
	if (m_write_vec.get(ACC_MAT_id(acc_mat)) != NULL) {
		return true;
	}
	return false;
}


void ACC_MGR::get_read_refs(OUT LIST<ACC_MAT*> & lst) const
{
	for (INT i = 0; i <= m_read_vec.get_last_idx(); i++) {
		ACC_MAT * a = m_read_vec.get(i);
		if (a != NULL) {
			lst.append_tail(a);
		}
	}
}


void ACC_MGR::get_write_refs(OUT LIST<ACC_MAT*> & lst) const
{
	for (INT i = 0; i <= m_write_vec.get_last_idx(); i++) {
		ACC_MAT * a = m_write_vec.get(i);
		if (a != NULL) {
			lst.append_tail(a);
		}
	}
}


void ACC_MGR::dump(FILE * h, SVECTOR<CHAR*> & var_name, POLY const& p)
{
	INT i;
	bool first = true;
	for (i = 0; i <= m_read_vec.get_last_idx(); i++) {
		ACC_MAT * am = m_read_vec.get(i);
		if (am != NULL) {
			IS_TRUE0(am->get_col_size() ==
				POLY_domain(p)->get_col_size() - p.get_num_of_localvar());
			if (first) {
				fprintf(h, "\n\tREAD : CST=%d :", POLY_domain_rhs_idx(p));
				first = false;
			}
			fprintf(h, " ACC_MAT(%d)", ACC_MAT_id(*am));
		}
	}

	first = true;
	for (i = 0; i <= m_write_vec.get_last_idx(); i++) {
		ACC_MAT * am = m_write_vec.get(i);
		if (am != NULL) {
			IS_TRUE0(am->get_col_size() ==
				POLY_domain(p)->get_col_size() - p.get_num_of_localvar());
			if (first) {
				fprintf(h, "\n\tWRITE : CST=%d :", POLY_domain_rhs_idx(p));
				first = false;
			}
			fprintf(h, " ACC_MAT(%d)", ACC_MAT_id(*am));
		}
	}

	for (i = 0; i <= m_map_arr_base_id2refs.get_last_idx(); i++) {
		LIST<ACC_MAT*> * lst = m_map_arr_base_id2refs.get(i);
		if (lst != NULL) {
			fprintf(h, "\n\tARRAY_BASE(%d) : ", i);
			for (ACC_MAT * am = lst->get_head();
				 am != NULL; am = lst->get_next()) {
				fprintf(h, "\n\t\tACC_MAT(%d) :", ACC_MAT_id(*am));
				am->dump(h, var_name, p, 12);
			}
		}
	}
}
//END ACC_MGR



//
//START SCH_MAT
//
/* Initialize schedule matrix.

'loop_nest_dim': dimension of enclosing loop nests of stmt.
'num_of_cst_sym': number of constant global symbol variable.
e.g:
	for (i=0:N)
	  S1
	S2

	S1's loop_nest_dim is 1
	S2's loop_nest_dim is 0
*/
void SCH_MAT::init(UINT loop_nest_dim, UINT num_of_cst_sym)
{
	reinit(1 + loop_nest_dim * 2, loop_nest_dim + 1 + num_of_cst_sym);
	m_map_iv.reinit(loop_nest_dim + 1, loop_nest_dim);
	m_syn_order_idx = loop_nest_dim;
	m_stmt_depth = m_syn_order_idx;
}


void SCH_MAT::copy(IN SCH_MAT const& s)
{
	RMAT::copy(s);
	m_map_iv.copy(s.m_map_iv);
	m_syn_order_idx = s.m_syn_order_idx;
	m_stmt_depth = s.m_stmt_depth;
}


/* For given loop nest, this function sets LOOP order
and static statement order.
	e.g:
		for (i)
		  S1
		  for (j)
		    S2
		S1: syntactic order at depth 1(inner loop i) is 0
		S2: syntactic order at depth 1(inner loop i) is 1,
			and be 0 at depth 2(innner loop j).

'depth': nested depth, starting with 0.
'order': static statement order, starting with 0.
*/
void SCH_MAT::set_stmt_order(UINT depth, UINT order)
{
	INT row_pos = compute_stmt_row_pos(depth);
	IS_TRUE(row_pos >= 0, ("Not contain the depth"));
	set(row_pos, m_syn_order_idx, order);
}


void SCH_MAT::set_stmt_depth(UINT depth)
{
	IS_TRUE0(depth <= get_max_depth());
	m_stmt_depth = depth;
}


//'depth': nested depth, starting with 0.
INT SCH_MAT::get_stmt_order(UINT depth) const
{
	INT row_pos = compute_stmt_row_pos(depth);
	if (row_pos < 0) {
		//Not contain the depth.
		return -1;
	}
	return get(row_pos, m_syn_order_idx).num();
}


//Return the number of Gamma Variable, namely the column size of Gamma part.
UINT SCH_MAT::get_num_of_gamma() const
{
	return get_col_size() - 1 - m_syn_order_idx;
}


void SCH_MAT::get_iter_mat(OUT RMAT & A)
{
	UINT num_of_iv = get_max_depth();
	A.reinit(num_of_iv, num_of_iv);
	for (UINT d = 1; d <= num_of_iv; d++) {
		INT rowpos = compute_loop_row_pos(d);
		IS_TRUE0(rowpos >= 0);
		for (UINT j = 0; j < num_of_iv; j++) {
			A.set(d - 1, j, this->get(rowpos, j));
		}
	}
}


void SCH_MAT::set_iter_mat(IN RMAT const& A)
{
	UINT num_of_iv = get_max_depth();
	for (UINT d = 1; d <= num_of_iv; d++) {
		INT rowpos = compute_loop_row_pos(d);
		IS_TRUE0(rowpos >= 0);
		for (UINT j = 0; j < num_of_iv; j++) {
			this->set(rowpos, j, A.get(d - 1, j));
		}
	}
}


void SCH_MAT::get_gamma_mat(OUT RMAT & G)
{
	UINT num_of_g = get_num_of_gamma();
	if (num_of_g == 0) {
		G.clean();
		return;
	}
	UINT num_of_iv = get_max_depth();
	INT gidx = get_gamma_idx();
	IS_TRUE0(gidx > 0);
	G.reinit(num_of_iv, num_of_g);
	for (UINT d = 1; d <= num_of_iv; d++) {
		INT rowpos = compute_loop_row_pos(d);
		IS_TRUE0(rowpos >= 0);
		for (UINT j = 0; j < num_of_g; j++) {
			G.set(d - 1, j, this->get(rowpos, gidx + j));
		}
	}
}


void SCH_MAT::set_gamma_mat(IN RMAT const& G)
{
	UINT num_of_g = get_num_of_gamma();
	if (num_of_g == 0) {
		return;
	}
	UINT num_of_iv = get_max_depth();
	INT gidx = get_gamma_idx();
	IS_TRUE0(gidx > 0);
	for (UINT d = 1; d <= num_of_iv; d++) {
		INT rowpos = compute_loop_row_pos(d);
		IS_TRUE0(rowpos >= 0);
		for (UINT j = 0; j < num_of_g; j++) {
			this->set(rowpos, gidx + j, G.get(d - 1, j));
		}
	}
}


void SCH_MAT::surround_stmt_by_loop()
{
	IS_TRUE0(get_max_depth() == 0);
	UINT order = get_stmt_order(0);
	UINT num_of_cst_sym = get_num_of_gamma();
	RMAT lam;

	//Get gamma component.
	if (num_of_cst_sym > 0) {
		inner_col(lam, m_syn_order_idx + 1, get_col_size() - 1);
	}
	init(1, num_of_cst_sym);
	set_stmt_order(0, order);
	set_stmt_order(1, 0);
	set_map_depth2iv(1, 0);

	//Set gamma component.
	if (num_of_cst_sym > 0) {
		lam.grow_row(get_row_size() - lam.get_row_size());
		set_cols(m_syn_order_idx + 1, get_col_size() - 1, lam, 0);
	}
}


INT SCH_MAT::map_depth2iv(UINT depth) const
{
	if (depth == 0 || depth > get_max_depth()) {
		return -1;
	} else {
		for (UINT i = 0; i < get_syn_order_idx(); i++) {
			if (m_map_iv.get(depth, i) != 0) {
				return i;
			}
		}
	}
	IS_TRUE0(0);
	return -1;
}


//Return 'depth' that 'iv_idx' corresponded to. Each iv has unique depth.
INT SCH_MAT::map_iv2depth(UINT iv_idx) const
{
	if (iv_idx >= m_syn_order_idx) {
		return -1;
	}
	for (UINT d = 1; d < get_row_size(); d++) {
		if (m_map_iv.get(d, iv_idx) != 0) {
			return (INT)d;
		}
	}
	return -1;
}


void SCH_MAT::set_map_depth2iv(UINT depth, UINT iv_idx)
{
	IS_TRUE0(depth > 0);
	IS_TRUE0(iv_idx < m_syn_order_idx);
	this->set(compute_loop_row_pos(depth), iv_idx, 1);
	m_map_iv.set(depth, iv_idx, 1);
}


/* Return 'global parameter value' for given 'depth and pv_idx'.
There is no related global parameter value for depth 0.

'depth': static nested order.
'pv_idx': index of given global-parameter variable, starting at 0. */
INT SCH_MAT::map_depth2pv(UINT depth, UINT pv_idx) const
{
	IS_TRUE0(pv_idx > m_syn_order_idx && pv_idx < this->get_col_size());
	IS_TRUE0(this->get_num_of_gamma() > 0);
	if (depth == 0) return 0;
	INT row = this->compute_loop_row_pos(depth);
	IS_TRUE0(row >= 1);
	return this->get(row, get_gamma_idx() + pv_idx).num();
}


/* Set 'global parameter value' by 'depth and pv_idx' referred to.
There is no related global parameter value for depth 0.

'depth': static nested order.
'pv_idx': index of given global-parameter variable, starting at 0. */
void SCH_MAT::set_map_depth2pv(UINT depth, UINT pv_idx, INT pv_val)
{
	IS_TRUE0(pv_idx < this->get_num_of_gamma());
	IS_TRUE0(this->get_num_of_gamma() > 0);
	if (depth == 0) return;
	INT row = this->compute_loop_row_pos(depth);
	IS_TRUE0(row >= 1);
	this->set(row, get_gamma_idx() + pv_idx, pv_val);
}


INT SCH_MAT::compute_stmt_row_pos(UINT depth) const
{
	UINT row_pos = depth * 2;
	if (row_pos >= get_row_size()) {
		return -1;
	}
	return row_pos;
}


INT SCH_MAT::compute_loop_row_pos(UINT depth) const
{
	if (depth == 0) return -1;
	INT row_pos = compute_stmt_row_pos(depth) - 1;
	if (row_pos < 0) {
		return -1;
	}
	return row_pos;
}


/* Insert a new loop before given loop level.
'iv_idx': loop index

NOTICE: Convert iv_idx to depth, because loop interchange will shuffle
	the lexical order of each iv_idx. */
void SCH_MAT::insert_loop_before(UINT iv_idx)
{
	INT depth = map_iv2depth(iv_idx);
	IS_TRUE0(depth >= 0);
	UINT pos = compute_loop_row_pos(depth);
	this->insert_rows_before(pos, 2);
	this->insert_cols_before(iv_idx, 1);
	m_map_iv.insert_rows_before(depth, 1);
	m_map_iv.insert_cols_before(iv_idx, 1);
	m_syn_order_idx++;

	//Original loopnest will be the 0th element within new loopnest.
	set_stmt_order(depth, 0);
	set_map_depth2iv(depth, iv_idx);
}


/* Insert a new loop before given loop.
'iv_idx': index of given loop index variable. */
void SCH_MAT::insert_loop_after(UINT iv_idx)
{
	INT depth = map_iv2depth(iv_idx);
	IS_TRUE0(depth >= 0);
	if (depth == (INT)get_max_depth()) {
		this->grow_row(2);
		this->insert_cols_before(iv_idx + 1, 1);
		m_map_iv.grow_all(1, 1);
	} else {
		UINT pos = compute_loop_row_pos(depth);
		this->insert_rows_before(pos, 2);
		this->insert_cols_before(iv_idx, 1);
		m_map_iv.insert_rows_before(depth, 1);
		m_map_iv.insert_cols_before(iv_idx, 1);
	}
	m_syn_order_idx++;

	//Original loopnest will be the 0th kid within new loopnest.
	set_stmt_order(depth + 1, 0);
	set_map_depth2iv(depth + 1, iv_idx + 1);
}


/* Remove loop.
'iv_idx': index of given loop index variable. */
void SCH_MAT::remove_loop(UINT iv_idx)
{
	INT depth = map_iv2depth(iv_idx);
	IS_TRUE0(depth >= 0);
	UINT pos = compute_loop_row_pos(depth);
	this->del_row(pos, pos + 1);
	this->del_col(iv_idx);
	m_map_iv.del_row(depth);
	m_map_iv.del_col(iv_idx);
	m_syn_order_idx--;
}


void SCH_MAT::inc_stmt_order(UINT depth, UINT n)
{
	INT sorder = get_stmt_order(depth);
	if (sorder < 0) {
		return;
	}
	set_stmt_order(depth, sorder + n);
}


void SCH_MAT::dec_stmt_order(UINT depth, UINT n)
{
	INT sorder = get_stmt_order(depth);
	if (sorder <= 0) {
		return;
	}
	sorder -= n;
	IS_TRUE0(sorder >= 0);
	set_stmt_order(depth, sorder);
}


void SCH_MAT::dump(IN FILE * h, POLY const& p)
{
	UINT i;
	fprintf(h, "\nSTATIC ORDER:[ ");
	for (i = 0; i <= get_stmt_depth(); i++) {
		fprintf(h, "%d ", get_stmt_order(i));
	}
	fprintf(h, "]");

	UINT depth = 0;
	CHAR buf[64];
	for (i = 0; i < get_row_size(); i++) {
		//Print inequlity coeff.
		fprintf(h, "\n");
		UINT j;
		for (j = 0; j < get_syn_order_idx(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}
		fprintf(h, "|");
		fprintf(h, "%s", format_rational(get(i, get_syn_order_idx()),
										buf, false));
		fprintf(h, "|");

		for (j = get_syn_order_idx() + 1; j < get_col_size(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		if ((INT)i == compute_loop_row_pos(depth)) {
			fprintf(h, "  <---- loop iter %d", depth - 1);
		}

		if ((INT)i == compute_stmt_row_pos(depth)) {
			fprintf(h, "  <---- depth %d", depth);
			depth++;
			fprintf(h, "\n");
		}
	}

	fprintf(h, "\nMAP_IV : \n");
	for (i = 0; i < m_map_iv.get_row_size(); i++) {
		for (UINT j = 0; j < m_map_iv.get_col_size(); j++) {
			fprintf(h, "%s", format_rational(m_map_iv.get(i, j),
											buf, false));
		}
		fprintf(h, "\n");
	}
}


/* Perform loop interchange.
'iv_idx1': index-variable, and -1 means moving iv_idx1 to be outermost.
'iv_idx2': index-variable, and -1 means moving iv_idx1 to be outermost.
*/
void SCH_MAT::interchange(INT iv_idx1, INT iv_idx2)
{
	if (iv_idx1 == iv_idx2) return;
	INT d2 = map_iv2depth(iv_idx2);
	IS_TRUE0(d2 >= 1);
	if (iv_idx1 == -1) {
		UINT row_pos2 = this->compute_loop_row_pos(d2);
		RMAT row;
		this->inner_row(row, row_pos2, row_pos2 + 1);
		this->del_row(row_pos2, row_pos2 + 1);
		this->insert_rows_before(1, row, 0, row.get_row_size() - 1);

		//Interchange rows of iv mapping table.
		INTMAT rowi;
		m_map_iv.inner_row(rowi, d2, d2);
		m_map_iv.del_row(d2);
		m_map_iv.insert_rows_before(1, rowi, 0, rowi.get_row_size() - 1);
	} else {
		INT d1 = map_iv2depth(iv_idx1);
		IS_TRUE0(d1 >= 1);
		this->interch_row(compute_loop_row_pos(d1), compute_loop_row_pos(d2));

		//Interchange rows of iv mapping table.
		m_map_iv.interch_row(d1, d2);
	}
}


void SCH_MAT::reverse(UINT iv_idx)
{
	INT d = map_iv2depth(iv_idx);
	IS_TRUE0(d >= 1);
	m_map_iv.reverse(d, iv_idx);
}
//END SCH_MAT


//
//START DOMAIN_MAT
//
//'iv_idx': index of iv.
void DOMAIN_MAT::insert_loop_before(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	insert_cols_before(iv_idx, 1);
	return;
}


//'iv_idx': index of iv.
void DOMAIN_MAT::insert_loop_after(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	insert_cols_before(iv_idx + 1, 1);
	return;
}


//'iv_idx': index of iv.
void DOMAIN_MAT::remove_loop(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	del_col(iv_idx);
	return;
}


/*
'iv_idx1': index-variable, and -1 means moving iv_idx1 to be outermost.
'iv_idx2': index-variable, and -1 means moving iv_idx1 to be outermost.
*/
void DOMAIN_MAT::interchange(INT iv_idx1, INT iv_idx2)
{
	if (iv_idx1 == -1) {
		RMAT col;
		this->inner_col(col, iv_idx2, iv_idx2);
		this->del_col(iv_idx2);
		this->insert_cols_before(0, col, 0, 0);
	} else {
		this->interch_col(iv_idx1, iv_idx2);
	}
}


void DOMAIN_MAT::dump(IN FILE * h,
					  IN SVECTOR<CHAR*> & var_name,
					  POLY const& p)
{
	UINT i;
	CHAR buf[64];
	UINT rhs_idx = POLY_domain_rhs_idx(p);
	UINT nvar = p.get_num_of_var();
	INT loc_idx = POLY_locvar_idx(p);
	for (i = 0; i < get_row_size(); i++) {
		UINT j;
		//Print inequlity coeff.
		fprintf(h, "\n");
		j = 0;
		if (loc_idx >= 0) {
			for (j = 0; (INT)j < loc_idx; j++) {
				fprintf(h, "%s", format_rational(get(i, j), buf, false));
			}
			fprintf(h, "|");
		}

		for (; j < rhs_idx; j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		fprintf(h, " <= ");
		for (j = rhs_idx; j < get_col_size(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		//Print inequality symbol.
		fprintf(h, "  //  ");
		UINT k = 0;
		bool has_prt = false;
		bool first = true;
		for (j = 0; j < nvar; j++, k++) {
			if (get(i, j) != 0) {
				CHAR * c = format_rational(get(i, j), buf, true);
				CHAR * n = var_name.get(j);

				if (!first) {
					fprintf(h, " + ");
				}
				if (first) {
					first = false;
				}

				if (n == NULL) {
					if (get(i, j) != 1 && get(i, j) != -1) {
						fprintf(h, "%s*%s%d", c, "i", k);
					} else {
						fprintf(h, "%s%s%d", c, "i", k);
					}
				} else {
					if (get(i, j) != 1 && get(i, j) != -1) {
						fprintf(h, "%s*%s", c, n);
					} else {
						fprintf(h, "%s%s", c, n);
					}
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}

		has_prt = false;
		fprintf(h, " <= ");

		//Print global constant symbol on RHS.
		k = 0;
		for (j = rhs_idx; j < get_col_size(); j++, k++) {
			if (get(i, j) != 0) {
				if (j == rhs_idx) {
					//Print constant.
					CHAR * c = format_rational(get(i, j), buf, false);
					fprintf(h, "%s", c);
				} else {
					//Print global constant symbol.
					CHAR * c = format_rational(get(i, j), buf, true);
					CHAR * n = var_name.get(j);
					fprintf(h, " + ");
					if (n == NULL) {
						if (get(i, j) != 1 && get(i, j) != -1) {
							fprintf(h, "%s*%s%d", c, "ig", k);
						} else {
							fprintf(h, "%s%s%d", c, "ig", k);
						}
					} else {
						if (get(i, j) != 1 && get(i, j) != -1) {
							fprintf(h, "%s*%s", c, n);
						} else {
							fprintf(h, "%s%s", c, n);
						}
					}
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}
	}
}
//END DOMAIN_MAT


//
//START LOCVAR_MAT
//
void LOCVAR_MAT::insert_loop_before(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	insert_cols_before(iv_idx, 1);
	return;
}


void LOCVAR_MAT::insert_loop_after(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	insert_cols_before(iv_idx + 1, 1);
	return;
}


void LOCVAR_MAT::remove_loop(UINT iv_idx)
{
	//iv_idx is equal to domain_rhs_idx if there is no loop surround stmt.
	del_col(iv_idx);
	return;
}


void LOCVAR_MAT::dump(IN FILE * h, IN SVECTOR<CHAR*> & var_name,
					  POLY const& p)
{
	INT loc_idx = POLY_locvar_idx(p);
	IS_TRUE0(loc_idx >= 0);
	UINT i;
	CHAR buf[64];
	UINT rhs_idx = POLY_domain_rhs_idx(p);
	for (i = 0; i < get_row_size(); i++) {
		UINT j;
		//Print inequlity coeff.
		fprintf(h, "\n");
		for (j = 0; (INT)j < loc_idx; j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}
		fprintf(h, "|");
		for (; j < rhs_idx; j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		fprintf(h, " = ");
		for (j = rhs_idx; j < get_col_size(); j++) {
			fprintf(h, "%s", format_rational(get(i, j), buf, false));
		}

		//Print inequality symbol.
		fprintf(h, "  //  ");
		UINT k = 0;
		bool has_prt = false;
		bool first = true;
		for (j = 0; j < rhs_idx; j++, k++) {
			if (get(i, j) != 0) {
				CHAR * c = format_rational(get(i, j), buf, true);
				if (!first) {
					fprintf(h, " + ");
				}
				if (first) {
					first = false;
				}
				if (get(i, j) != 1 && get(i, j) != -1) {
					fprintf(h, "%s*%s%d",
							   c, j < p.get_num_of_var() ? "i" : "l", k);
				} else {
					fprintf(h, "%s%s%d",
							   c, j < p.get_num_of_var() ? "i" : "l", k);
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}

		has_prt = false;
		fprintf(h, " = ");

		//Print global constatn symbol on RHS.
		k = 0;
		for (j = rhs_idx; j < get_col_size(); j++, k++) {
			if (get(i, j) != 0) {
				if (j == rhs_idx) {
					//Print constant.
					CHAR * c = format_rational(get(i, j), buf, false);
					fprintf(h, "%s", c);
				} else {
					//Print global constant symbol.
					CHAR * c = format_rational(get(i, j), buf, true);
					CHAR * n = var_name.get(j);
					fprintf(h, " + ");
					if (n == NULL) {
						if (get(i, j) != 1 && get(i, j) != -1) {
							fprintf(h, "%s*%s%d", c, "g", k);
						} else {
							fprintf(h, "%s%s%d", c, "g", k);
						}
					} else {
						if (get(i, j) != 1 && get(i, j) != -1) {
							fprintf(h, "%s*%s", c, n);
						} else {
							fprintf(h, "%s%s", c, n);
						}
					}
				}
				has_prt = true;
			}
		}
		if (!has_prt) {
			fprintf(h, "0");
		}
	}
}
//END LOCVAR_MAT


//
//START POLY
//
/* Add one local variable, the column is next to 'rhs_idx'.
and this operation will affect domain, access matrix.
Return column position of new local variable.
NOTICE: constrains to local_var are always equations. */
UINT POLY::insert_local_var()
{
	RMAT * domain = POLY_domain(*this);
	INT locvar_idx = POLY_locvar_idx(*this);
	INT rhs_idx = POLY_domain_rhs_idx(*this);

	//Insert one new local-variable which column is prior to 'rhs_idx'.
	domain->insert_cols_before(rhs_idx, 1);
	UINT new_loc_var_idx = rhs_idx;

	if (POLY_locvar_cs(*this) == NULL) {
		POLY_locvar_cs(*this) = new LOCVAR_MAT();
		POLY_locvar_cs(*this)->reinit(1, domain->get_col_size());
	} else {
		POLY_locvar_cs(*this)->insert_cols_before(rhs_idx, 1);
	}

	//Revise access function. Does it need?
	//POLY_acc_mgr(*this)->insert_local_var(rhs_idx);

	if (locvar_idx == -1) {
		locvar_idx = rhs_idx;
	}
	POLY_domain_rhs_idx(*this) ++;
	POLY_locvar_idx(*this) = locvar_idx;
	return new_loc_var_idx;
}


//There should be no loop nest surrounded stmt.
//Return column index of new generated loop iteration variable.
UINT POLY::surround_stmt_by_loop()
{
	DOMAIN_MAT * domain = POLY_domain(*this);
	IS_TRUE0(get_max_depth() == 0 && domain->get_col_size() == 0);

	//Revise schedul matrix.
	POLY_sche(*this)->surround_stmt_by_loop();

	//Revise domain.
	domain->reinit(1, POLY_sche(*this)->get_col_size());
	POLY_domain_rhs_idx(*this) = 1;

	//Revise access function.
	POLY_acc_mgr(*this)->surround_acc_by_loop();
	return 0;
}


bool POLY::is_same_dim(POLY const& p) const
{
    return get_num_of_var() == p.get_num_of_var() &&
	    domain_rhs_idx == p.domain_rhs_idx &&
	    get_num_of_localvar() == p.get_num_of_localvar() &&
	    get_num_of_param() == p.get_num_of_param();
}


/* Insert loop before loop 'iv_idx', that will affect domain, schedule matrix,
and access matrix.
Return column index of new generated loop iteration variable.

'iv_idx': insertion point of new loop index.
	If there is no loop surround STMT, it must be -1.
'changed_iv_idx': record the new column of 'iv_idx' after the insertion.

NOTICE: Convert depth to iv_idx before invoke this function.
	DO NOT replace 'iv_idx' by 'depth', because there might be a manipulation
	to DOMAIN/SCH_MAT/ACC_MAT, and the column value for index variable
	is needed.
*/
UINT POLY::insert_loop_before(UINT iv_idx, OUT UINT * changed_iv_idx)
{
	IS_TRUE0(iv_idx < get_num_of_var());
	//Revise domain.
	//Insert new loop-index-variable which column is prior to 'iv_idx'
	UINT const nvar = get_num_of_var();
	DOMAIN_MAT * domain = POLY_domain(*this);
	domain->insert_loop_before(iv_idx);
	if (POLY_locvar_cs(*this) != NULL) {
		IS_TRUE0(POLY_locvar_idx(*this) >= 0);
		POLY_locvar_cs(*this)->insert_loop_before(iv_idx);
		POLY_locvar_idx(*this) ++;
	}

	UINT new_var_idx = iv_idx;
	if (changed_iv_idx != NULL) {
		*changed_iv_idx = iv_idx + 1;
	}
	POLY_domain_rhs_idx(*this) ++;

	//Revise access function.
	POLY_acc_mgr(*this)->insert_loop_before(iv_idx);

	//Revise schedul matrix.
	POLY_sche(*this)->insert_loop_before(iv_idx);
	return new_var_idx;
}


/* Insert loop followed 'iv_idx', that will affect domain, schedule matrix,
and access matrix.
Return column index of new generated loop iteration variable.

'iv_idx': insertion point of new loop.
	If there is no loop surround STMT, it must be -1.
*/
UINT POLY::insert_loop_after(UINT iv_idx)
{
	IS_TRUE0(iv_idx < get_num_of_var());
	//Revise domain.
	//Insert new loop-index-variable which column is prior to 'iv_idx'
	UINT nvar = get_num_of_var();
	POLY_domain(*this)->insert_loop_after(iv_idx);
	if (POLY_locvar_cs(*this) != NULL) {
		POLY_locvar_cs(*this)->insert_loop_after(iv_idx);
	}

	UINT new_var_idx = iv_idx + 1;

	//Revise access function.
	POLY_acc_mgr(*this)->insert_loop_after(iv_idx);

	//Revise local variables index
	INT locvar_idx = POLY_locvar_idx(*this);
	if (locvar_idx >= 0) {
		locvar_idx++;
	}
	POLY_locvar_idx(*this) = locvar_idx;

	//Revise schedul matrix.
	POLY_sche(*this)->insert_loop_after(iv_idx);

	//Revise rhs_idx.
	POLY_domain_rhs_idx(*this) ++;
	return new_var_idx;
}


void POLY::init()
{
	POLY_domain(*this) = NULL;
	POLY_context(*this) = NULL;
	POLY_sche(*this) = NULL;
	POLY_acc_mgr(*this) = NULL;
	POLY_domain_rhs_idx(*this) = 0;
	POLY_locvar_idx(*this) = -1;
	POLY_stmt(*this) = NULL;
	locvar_constrains = NULL;
	id = 0xFFFFFFFF;
}


void POLY::destroy()
{
	POLY_domain(*this) = NULL;
	POLY_context(*this) = NULL;
	POLY_sche(*this) = NULL;
	POLY_acc_mgr(*this) = NULL;
	POLY_domain_rhs_idx(*this) = 0;
	POLY_locvar_idx(*this) = -1;
	POLY_stmt(*this) = NULL;
	if (locvar_constrains != NULL) {
		delete locvar_constrains;
		locvar_constrains = NULL;
	}
	id = 0xFFFFFFFF;
}


void POLY::copy(POLY const& p)
{
	IS_TRUE(POLY_domain(*this) != NULL, ("need to be initialized"));
	IS_TRUE(POLY_context(*this) != NULL, ("need to be initialized"));
	IS_TRUE(POLY_sche(*this) != NULL, ("need to be initialized"));

	POLY_id(*this) = POLY_id(p);
	POLY_domain(*this)->copy(*POLY_domain(p));
	POLY_context(*this)->copy(*POLY_context(p));
	POLY_sche(*this)->copy(*POLY_sche(p));
	POLY_acc_mgr(*this)->copy(*POLY_acc_mgr(p));
	POLY_domain_rhs_idx(*this) = POLY_domain_rhs_idx(p);
	POLY_locvar_idx(*this) = POLY_locvar_idx(p);
	POLY_stmt(*this) = POLY_stmt(p);
	if (POLY_locvar_cs(p) != NULL) {
		if (POLY_locvar_cs(*this) == NULL) {
			POLY_locvar_cs(*this) = new LOCVAR_MAT(*POLY_locvar_cs(p));
		} else {
			POLY_locvar_cs(*this)->copy(*POLY_locvar_cs(p));
		}
	} else {
		if (POLY_locvar_cs(*this) != NULL) {
			delete POLY_locvar_cs(*this);
			POLY_locvar_cs(*this) = NULL;
		}
	}
}


void POLY::set_var_name(UINT iv_idx, CHAR * name)
{
	m_var_name.set(iv_idx, name);
}


CHAR * POLY::get_var_name(UINT iv_idx)
{
	return m_var_name.get(iv_idx);
}


void POLY::dump(CHAR * name)
{
	if (name == NULL) {
		name = DUMP_FILE_NAME;
	}
	FILE * h = fopen(name, "a+");
	IS_TRUE(h, ("%s create failed!!!", name));
	fprintf(h, "\n---- POLY %d -------", POLY_id(*this));

	//Dump DOMAIN
	if (POLY_domain(*this) != NULL) {
		fprintf(h, "\nDOMAIN : LOCVAR_IDX=%d : RHS_IDX=%d",
					POLY_locvar_idx(*this),
					POLY_domain_rhs_idx(*this));
		POLY_domain(*this)->dump(h, m_var_name, *this);
	}

	//Dump LOCVAR CONSTRAINS
	if (POLY_locvar_idx(*this) >= 0) {
		IS_TRUE0(POLY_locvar_cs(*this)->get_col_size() ==
				 POLY_domain(*this)->get_col_size());
		fprintf(h, "\nLOCAL VARIABLE : LOCVAR_IDX=%d : RHS_IDX=%d",
				POLY_locvar_idx(*this),
				POLY_domain_rhs_idx(*this));
		IS_TRUE0(POLY_locvar_cs(*this) != NULL);
		POLY_locvar_cs(*this)->dump(h, m_var_name, *this);
	}

	//Dump SCHEDULE_FUNC
	if (POLY_sche(*this) != NULL) {
		IS_TRUE0(POLY_sche(*this)->get_col_size() ==
				POLY_domain(*this)->get_col_size() -
							this->get_num_of_localvar());
		fprintf(h, "\n\nSCHEDUL_FUNC : SYN_ORDER_IDX=%d, STMT_DEPTH=%d",
					POLY_sche(*this)->get_syn_order_idx(),
					POLY_sche(*this)->get_stmt_depth());
		INT so_idx = POLY_locvar_idx(*this) > 0 ?
					POLY_locvar_idx(*this) : POLY_domain_rhs_idx(*this);
		POLY_sche(*this)->dump(h, *this);
	}

	//Dump ACCESS FUNC
	if (POLY_acc_mgr(*this) != NULL) {
		fprintf(h, "\nACCESS_FUNC : ");
		POLY_acc_mgr(*this)->dump(h, m_var_name, *this);
	}

	//END
	fclose(h);
}


/* Grow Stmt Depth by encompassing stmt with loop nests
whose iterations are no more than 1.
'depth': the depth that need grow to.
	e.g: for i=0:N, grow it to loop nest with depth is 3.
	       S
	output loop nest:
		 for i=0:N
		   for j=0:0
		     for k=0:0
			   S
	note that there is only one iteration executed for loop j and loop k.

NOTCIE:
	If STMT is posterior to other STMT, one should be careful to compute the
	domain, because the lexical order must be take into account, e.g:
		Given code:
			for i=0:5
			  for j=0:6
			    S1
			  S2
		domain of S1 is : i=0:5, j=0:6
		domain of S2 is : i=0:5
		then extend domain of S2 to 2-dimension,
		domain of S1 is : i=0:5, j=0:6
		domain of S2 is : i=0:5, j=6:6
			for i=0:5
			  for j=0:6
			    S1
				S2 if(j==6)
*/
bool POLY::grow_depth(UINT depth, IN RMAT const* domain_constrains)
{
	if (depth <= get_max_depth()) return false;
	UINT new_var_idx;
	for (;get_max_depth() < depth;) {
		if (get_max_depth() == 0) {
			new_var_idx = surround_stmt_by_loop();
		} else {
			new_var_idx = insert_loop_after(
				POLY_sche(*this)->map_depth2iv(get_max_depth()));
		}
	}

	//Add contrains for growed dimension.
	if (domain_constrains != NULL) {
		IS_TRUE0(domain_constrains->get_col_size() ==
				POLY_domain(*this)->get_col_size());
		POLY_domain(*this)->grow_row(*domain_constrains,
					0, domain_constrains->get_row_size() - 1);
	}
	return true;
}


bool POLY::remove_loop(UINT iv_idx)
{
	IS_TRUE0(iv_idx < get_num_of_var());
	LINEQ lin((RMAT*)POLY_domain(*this), POLY_domain_rhs_idx(*this));
	RMAT res;
	if (!lin.fme(iv_idx, res, false)) {
		IS_TRUE(0, ("domain is empty(inconsistent!"));
	}
	POLY_domain(*this)->copy(res);

	//Revise domain
	POLY_domain(*this)->remove_loop(iv_idx);
	if (POLY_locvar_cs(*this) != NULL) {
		IS_TRUE0(POLY_locvar_idx(*this) >= 0);
		POLY_locvar_cs(*this)->remove_loop(iv_idx);
		POLY_locvar_idx(*this) --;
	}
	POLY_domain_rhs_idx(*this) --;

	//Revise access function.
	POLY_acc_mgr(*this)->remove_loop(iv_idx);

	//Revise schedul matrix.
	POLY_sche(*this)->remove_loop(iv_idx);
	return true;
}


/* Move STMT into depth.
e.g: S1's depth is 2.
	for i
	  for j
	    S1
	    for k
		  for u
	move S1 to depth 3
	 for i
	  for j
	    for k
		  S1
		  for u
*/
bool POLY::move2depth(UINT depth)
{
	if (depth == get_stmt_depth())
		return false;

	if (depth > get_max_depth()) {
		grow_depth(depth, NULL);
	}

	POLY_sche(*this)->set_stmt_depth(depth);
	return true;
}


void POLY::remove_localvar_cols(IN OUT RMAT & lv_cols)
{
	if (POLY_locvar_idx(*this) == -1) {
		lv_cols.clean();
		return;
	}
	UINT rhs_idx = POLY_domain_rhs_idx(*this);
	UINT lv_idx = POLY_locvar_idx(*this);
	DOMAIN_MAT * dm = POLY_domain(*this);
	dm->inner_col(lv_cols, POLY_locvar_idx(*this), rhs_idx - 1);
	dm->del_col(lv_idx, rhs_idx - 1);
	POLY_locvar_idx(*this) = -1;
	POLY_domain_rhs_idx(*this) = lv_idx;
}


void POLY::insert_localvar_cols(IN RMAT const& lv_cols)
{
	IS_TRUE0(POLY_locvar_idx(*this) == -1);
	UINT rhs_idx = POLY_domain_rhs_idx(*this);
	POLY_domain(*this)->insert_cols_before(rhs_idx,
					lv_cols, 0, lv_cols.get_col_size() - 1);
	POLY_domain_rhs_idx(*this) = rhs_idx + lv_cols.get_col_size();
	POLY_locvar_idx(*this) = rhs_idx;
}
//END POLY



//
//START POLY_MGR
//
DOMAIN_MAT * POLY_MGR::new_domain_mat()
{
	return new DOMAIN_MAT();
}


SCH_MAT * POLY_MGR::new_sch_mat()
{
	return new SCH_MAT();
}


ACC_MGR * POLY_MGR::new_acc_mgr()
{
	return new ACC_MGR();
}


POLY * POLY_MGR::new_poly()
{
	return new POLY();
}


CONT_MAT * POLY_MGR::new_context()
{
	return new CONT_MAT();
}


POLY * POLY_MGR::init_poly()
{
	POLY * p = new_poly();
	POLY_domain(*p) = new_domain_mat();
	POLY_sche(*p) = new_sch_mat();
	POLY_acc_mgr(*p) = new_acc_mgr();
	POLY_context(*p) = new_context();
	return p;
}


void POLY_MGR::destroy_poly(POLY * p)
{
	delete POLY_domain(*p);
	delete POLY_sche(*p);
	delete POLY_acc_mgr(*p);
	delete POLY_context(*p);
	delete p;
}


void POLY_MGR::copy_poly_list(IN LIST<POLY*> & from,
							OUT LIST<POLY*> & to)
{
	if (to.get_elem_count() != 0) {
		free_poly_list(to);
	}
	for (POLY const* p = from.get_head();
		 p != NULL; p = from.get_next()) {
		POLY * pp = init_poly();
		pp->copy(*p);
		to.append_tail(pp);
	}
}


void POLY_MGR::free_poly_list(IN OUT LIST<POLY*> & lst)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		destroy_poly(p);
	}
	lst.clean();
}


void POLY_MGR::grow_max_depth(IN OUT LIST<POLY*> & lst)
{
	UINT depth = 0;
	POLY * p;
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		depth = MAX(depth, p->get_max_depth());
	}
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		p->grow_depth(depth);
	}
}


void POLY_MGR::remove_virtual_depth(IN OUT LIST<POLY*> & lst)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		INT stmt_depth = p->get_stmt_depth();
		INT max_depth = p->get_max_depth();
		IS_TRUE0(stmt_depth <= max_depth);
		for (INT d = max_depth; d > stmt_depth; d--) {
			INT iv_idx = POLY_sche(*p)->map_depth2iv(d);
			IS_TRUE0(iv_idx >= 0);
			p->remove_loop(iv_idx);
		}
	}
}


void POLY_MGR::dump_poly_list(IN LIST<POLY*> & lst)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		p->dump();
	}
}
//END POLY_MGR



//
//START POLY_TREE_MGR
//
POLY_TREE_MGR::POLY_TREE_MGR()
{
	m_pool = smpool_create_handle(16, MEM_COMM);
}


POLY_TREE_MGR::~POLY_TREE_MGR()
{
	smpool_free_handle(m_pool);
	m_pool = NULL;
}


void * POLY_TREE_MGR::xmalloc(ULONG size)
{
	void * p = smpool_malloc_h(size, m_pool);
	if (p == NULL) return NULL;
	memset(p, 0, size);
	return p;
}


POLY_TREE * POLY_TREE_MGR::new_poly_tree()
{
	return (POLY_TREE*)xmalloc(sizeof(POLY_TREE));
}


/* Construct code generation tree.
Place 'p' to approperite position on the tree. Return the new root.
'p': record POLY of a STMT
'root': root of code generation tree. */
POLY_TREE * POLY_TREE_MGR::insert(IN POLY * p, IN OUT POLY_TREE * root)
{
	INT depth = 0;
	SCH_MAT * scc = POLY_sche(*p);
	INT sorder = scc->get_stmt_order(depth);
	IS_TRUE(sorder >= 0, ("depth 0 is inexistent"));
	while (sorder != -1) {
		for (INT i = 0; i <= sorder; i++) {
			IS_TRUE0(0);
		}
		sorder = scc->get_stmt_order(++depth);
	}
	return root;
}
//END POLY_TREE_MGR



//
//START POLY_TRAN
//
POLY_TRAN::POLY_TRAN()
{
	m_is_init = false;
	init();
}


POLY_TRAN::~POLY_TRAN()
{
  	destroy();
}


void * POLY_TRAN::xmalloc(ULONG size)
{
	IS_TRUE(m_is_init, ("not yet initialized."));
	void * p = smpool_malloc_h(size, m_pool);
	if (p == NULL) return NULL;
	memset(p, 0, size);
	return p;
}


void POLY_TRAN::init()
{
	if (m_is_init) return;
	m_pool = smpool_create_handle(16, MEM_COMM);
	m_is_init = true;
}


void POLY_TRAN::destroy()
{
	if (!m_is_init) return;
	smpool_free_handle(m_pool);
	m_pool = NULL;
	m_is_init = false;
}


/* Unroll-and-Jam is strictly equivalent to strip-mining, interchange and full
unrolling. The latter sequence is the best way to implement unroll-andjam
in polyhedral framework, since it does not require statement duplication
in the representation itself but relies on lazy unrolling.
In general, strip-mining leads to confluent paths when combined with fusion
or fission.
*/
bool POLY_TRAN::unroll_and_jam(POLY & poly)
{
	return true;
}


/* Stripmine only modify the ITERATION DOMAIN: the number
of loops or the loop bounds.
It does not affect the order in which statement instances
are executed and the arrays are accessed.

'poly': POLY to handle
'depth': depth level to tile
'B': tile/block size
'changed_depth': record the new level of 'depth' after inserting a loop.
'generated_depth': record level of the generated tile loop. This loop
	is always the loop that be used to walk through tiles.
*/
bool POLY_TRAN::stripmine(IN OUT POLY & poly,
						  UINT depth,
						  UINT B,
						  OUT UINT * changed_depth,
						  OUT UINT * generated_depth)
{
	if (depth == 0 || depth > poly.get_max_depth()) {
		return false;
	}
	DOMAIN_MAT * domain = POLY_domain(poly);
	UINT rhs_idx = POLY_domain_rhs_idx(poly);
	INT locvar_idx = POLY_locvar_idx(poly);
	INT nvar = poly.get_num_of_var();
	INT iv_idx = POLY_sche(poly)->map_depth2iv(depth);
	IS_TRUE0(iv_idx >= 0 && iv_idx < nvar);
	INT sB = B;

	/*
	e.g: stripmine loop j:
		for (i=0:M-1)
		  for (j=0:N-1)
		    ...
	*/

	/* Insert colums to record new loop index jj and local-variable jj2.
	From left to right the index-variable is:
		columns i, jj, j, jj2, CONST, M, N.
	*/
	//Insert new loop index before 'iv_idx'.
	UINT new_iv_idx;
	UINT new_var_idx = poly.insert_loop_before(iv_idx, &new_iv_idx);

	//Insert new local-variable.
	//Adding/removing local variables has no impact on schedule matrix ¦È.
	//Finally, local variables will be substituted into other constrains.
	UINT new_locvar_idx = poly.insert_local_var();
	rhs_idx = POLY_domain_rhs_idx(poly);

	/* Add the relation: jj<=j<=jj+B-1.
		for (i=0:M-1)
		  for (jj<=j<=jj+B-1) <--just to be new constrains
		  						 of j, not new dimension.
		    for (j=0:N-1)
		      ...
	*/
	//Insert rows to express inequalities.
	UINT new_ineq_start_idx = domain->get_row_size();
	domain->grow_row(2);
	//j>=jj
	domain->set(new_ineq_start_idx, new_iv_idx, -1);
	domain->set(new_ineq_start_idx, new_var_idx, 1);

	//j<=jj+B-1
	domain->set(new_ineq_start_idx + 1, new_iv_idx, 1);
	domain->set(new_ineq_start_idx + 1, new_var_idx, -1);
	domain->set(new_ineq_start_idx + 1, rhs_idx, sB - 1);

	//Add local variable equation: jj=B*jj2.
	new_ineq_start_idx = POLY_locvar_cs(poly)->get_row_size();
	POLY_locvar_cs(poly)->grow_row(1);
	//jj=B*jj2
	POLY_locvar_cs(poly)->set(new_ineq_start_idx, new_var_idx, 1);
	POLY_locvar_cs(poly)->set(new_ineq_start_idx, new_locvar_idx, -sB);

	/* How to deal with local variable jj2's constrains?
	Record jj2 as Local Variable, which would be
	handled at Polyhedral Code Generation
	Stage to generate code to compute the initial value of jj2.
		In more generalization form:
			for (i = 0:M-1)
			  for (jj = LOW:UP)
				for (jj=jj2*B && floor(LOW,B) ¡Üjj2 ¡Üfloor(UP,B)-1)
					S(i,j)

		after code generation:

			for (i = 0:M-1)
			  for (jj2 = floor(LOW,B):floor(UP,B)-1)
				for (jj2*B ¡Üj ¡Üjj2*B+B-1 && LOW ¡Üj ¡ÜUP)
				  j=jj
				  S(i,j)

		and further be simplified. The finial code generated like this:

			for (i = 0:M-1)
			  for (jj2 = floor(LOW,B):floor(UP,B)-1)
				for (jj = max(jj2*B, LOW):min(jj2*B+B-1, UP) )
				  j=jj
				  S(i,j)

		In Polyhedral Model, we have to give a method to describe the
		boundaries of 'jj2'. It is a FLOOR division.
		Local Variable required to implement integer division and
		modulo operations via affine projection.
	*/

	{
		/* Affine projection to eliminate jj2.
		UINT row = domain->get_row_size();
		domain->grow_row(2);
		domain->set(row, new_locvar_idx, -1);
		domain->set(row+1, new_locvar_idx, 1);
		domain->set(row+1, rhs_idx, 3);

		//Show constrains for jj in method 1.
		LINEQ l(domain, rhs_idx);
		for (UINT j = nvar - 1; j >= 0; j--) {
			RMAT res;
			if (!l.fme(j, res, false)) {
				IS_TRUE(0, ("system inconsistency!"));
			}
			*domain = res;
		}

		//Show constrains for jj in method 2.
		//LIST<RMAT*> bd;
		//bd.append_tail(new RMAT); bd.append_tail(new RMAT);
		//bd.append_tail(new RMAT); bd.append_tail(new RMAT);
		//bd.append_tail(new RMAT); bd.append_tail(new RMAT);
		//LINEQ l(domain, rhs_idx);
		//l.calc_bound(bd);
		//for (RMAT * r = bd.get_head(); r != NULL; r = bd.get_next()) {
		//	delete r;
		//}
		*/
	}

	if (changed_depth != NULL) {
		*changed_depth = POLY_sche(poly)->map_iv2depth(new_iv_idx);
		IS_TRUE0(((INT)*changed_depth) >= 0);
	}
	if (generated_depth != NULL) {
		*generated_depth = POLY_sche(poly)->map_iv2depth(new_var_idx);
		IS_TRUE0(((INT)*generated_depth) >= 0);
	}
	return true;
}


bool POLY_TRAN::stripmine(IN OUT LIST<POLY*> & lst,
						  UINT iv_idx,
						  UINT B,
						  OUT UINT * changed_iv_idx,
						  OUT UINT * generated_iv_idx)
{
	bool first = true;
	UINT c, g;
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		stripmine(*p, iv_idx, B, changed_iv_idx, generated_iv_idx);
		if (first) {
			c = *changed_iv_idx;
			g = *generated_iv_idx;
			first = false;
		} else {
			IS_TRUE0(c == *changed_iv_idx && g == *generated_iv_idx);
		}
	}
	return true;
}


/* Fuse STMTs in two adjacent loop nests into same loop nest.
Loop Fusion is a schedule transformation with no explicit impact on the
iteration domain and memory access.

NOTICE: Each polyhedron in 'lst' must have been in lexical order!
	e.g: Fuse stmts in depth 1
		for i //d1
		  for x //d2
		    S1
		    for y
		      S2
	  	  for x //d2
		    S3
		    for y
		      S4
		    S5
	=>
		for i
		  for x
		    S1
		    for y
		      S2
		    S3
		    for y
		      S4
		    S5

'lst': STMTs to fuse.
'scop_poly_lst': all STMTs in SCOP.
'depth': indicates depth of SCoP that attempt to merge,
	and fuse depth 0 is permitted. */
bool POLY_TRAN::fusion(IN LIST<POLY*> & lst,
					IN OUT LIST<POLY*> & scop_poly_lst,
					UINT depth)
{
	POLY * head = lst.get_head();
	POLY * p;
	if (depth > 0) {
		for (p = lst.get_next(); p != NULL; p = lst.get_next()) {
			if (!is_lex_eq(*head, *p, depth - 1) ||
				depth > p->get_max_depth()) {
				return false;
			}
		}
	}
	LIST<POLY*> lst_1, * prior_loop_lst;
	LIST<POLY*> lst_2, * post_loop_lst;
	prior_loop_lst = &lst_1;
	post_loop_lst = &lst_2;
	INT prior_loop_so = -1, post_loop_so = -1;
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		SCH_MAT * sm = POLY_sche(*p);
		if (sm->get_stmt_depth() == depth) {
			/* There exist STMT at depth.
			e.g: for x
				   for y
				   S1
				Can not fuse loop y and S1.
			*/
			prior_loop_so = -1;
			post_loop_so = -1;
			break;
		}
		INT so = sm->get_stmt_order(depth);
		if (so < 0) {
			//stmt have no 'depth' dimension correspond to.
			continue;
		}

		if (prior_loop_so == -1) {
			prior_loop_lst->append_tail(p);
			prior_loop_so = so;
		} else if (so == prior_loop_so) {
			prior_loop_lst->append_tail(p);
		} else if (post_loop_so == -1) {
			post_loop_lst->append_tail(p);
			post_loop_so = so;
		} else if (so == post_loop_so) {
			post_loop_lst->append_tail(p);
		} else {
			//Attempt to fusion more than two loop-nests at once.
			return false;
		}
	}

	if (prior_loop_so == -1 || post_loop_so == -1) {
		//All of stmts have already been in the same loop nest.
		return false;
	}
	if (prior_loop_so > post_loop_so) {
		//Exchange syntactic order.
		INT tmp = prior_loop_so;
		prior_loop_so = post_loop_so;
		post_loop_so = tmp;

		LIST<POLY*> * tmpp = prior_loop_lst;
		prior_loop_lst = post_loop_lst;
		post_loop_lst = tmpp;
	}
	if (prior_loop_so + 1 != post_loop_so) {
		//Fused loops which are not adjacent.
		return false;
	}

	//It is only possible to fuse two STMTs in two loops if they are
	//consecutive at the loops depth.
	IS_TRUE0(prior_loop_so + 1 == post_loop_so);

	//Compute the sum of ELEMENTs(either STMT or LOOPNEST)
	//which within 'prior-loop'.
	INT max_stmt_syn_order = 0;
	for (p = prior_loop_lst->get_head();
		 p != NULL; p = prior_loop_lst->get_next()) {
		SCH_MAT * sm = POLY_sche(*p);
		INT stmt_order = sm->get_stmt_order(depth);
		if (stmt_order < 0) {
			continue;
		}
		max_stmt_syn_order = MAX(max_stmt_syn_order, stmt_order);
	}
	UINT start_of_syn_order = max_stmt_syn_order + 1;
	for (p = post_loop_lst->get_head();
		 p != NULL; p = post_loop_lst->get_next()) {
		SCH_MAT * sm = POLY_sche(*p);
		INT so = sm->get_stmt_order(depth + 1);
		IS_TRUE0(so >= 0);
		sm->set_stmt_order(depth, prior_loop_so);
		sm->set_stmt_order(depth + 1, start_of_syn_order + so);
	}

	/* Revise other STMT's parent syntactic-order, which are not in 'lst'.
	e.g: Given followed SCOP, perform fusion for S2,S3.
		for ()
		  S1
		for ()
		  for ()
		    S2
		for ()
		  for ()
		    S3
		for ()
		  for ()
		    S4
		¦Â(S4)={3,0,0}
	After fusing S2, S3 at depth 0, the syntactic
	order of S4 at depth 0 should be 2.
		for ()
		  S1
		for ()
		  for ()
		    S2
		  for ()
			S3
		for ()
		  for ()
		    S4
		¦Â(S4)={2,0,0}
	*/
	for (p = scop_poly_lst.get_head();
		 p != NULL; p = scop_poly_lst.get_next()) {
		INT so = POLY_sche(*p)->get_stmt_order(depth);
		if (so < 0) {
			continue;
		}
		if (so > post_loop_so) {
			POLY_sche(*p)->set_stmt_order(depth, so - 1);
		}
	}
	return true;
}


//Loop Unrolling is a domain transformation.
//It has no impact on the schedule and memory access functions.
bool POLY_TRAN::unroll(IN POLY & poly)
{
	return true;
}


/* Array Privatization is a memory access transformation.
It has impact on memory access function and array declaration.
Consider Z[i]=0, we want to privatize array Z over dimension k.
Besides modifying the declaration of Z, we need to change the
subscripts of references to Z, adding a row to each access
matrix with a 1 in the column corresponding to the new
dimension and zeroes elsewhere.
	  i j k
	Z[1 0 0] => Z[1 0 0]
	             [0 0 1]

'iv_idx': the loop index that the array to be privatized. */
bool POLY_TRAN::privatize(IN POLY & poly, UINT depth)
{
	if (depth > poly.get_max_depth()) {
		return false;
	}
	INT iv_idx = POLY_sche(poly)->map_depth2iv(depth);
	IS_TRUE0(iv_idx >= 0 && iv_idx < (INT)poly.get_num_of_var());
	//Revise access function.
	POLY_acc_mgr(poly)->privatize(iv_idx);
	return true;
}


/* Interchange LOOP d1 and LOOP d2.
Modify SCHEDULE MATRIX and DOMAIN.
'd1': loop level, where -1 means moving d1 to be outermost.
'd2': loop level, where -1 means moving d2 to be outermost. */
bool POLY_TRAN::interchange(POLY & poly, INT d1, INT d2)
{
	if (d1 == d2 || d1 == 0 || d2 == 0 ||
		d1 > (INT)poly.get_max_depth() ||
		d2 > (INT)poly.get_max_depth()) {
		return false;
	}
	INT iv_idx1 = -1;
	INT iv_idx2 = -1;
	if (d1 >= 0) {
		iv_idx1 = POLY_sche(poly)->map_depth2iv(d1);
		IS_TRUE0(iv_idx1 >= 0 && iv_idx1 < (INT)poly.get_num_of_var());
	}
	if (d2 >= 0) {
		iv_idx2 = POLY_sche(poly)->map_depth2iv(d2);
		IS_TRUE0(iv_idx2 >= 0 && iv_idx2 < (INT)poly.get_num_of_var());
	}

#ifdef INTERCH_BY_UNI
	if (d1 >= 0 && d2 >= 0) {
		RMAT locvar_cols;
		if (POLY_locvar_idx(poly) >= 0) {
			IS_TRUE0(POLY_locvar_cs(poly) != NULL);
			poly.remove_localvar_cols(locvar_cols);
		}

		RMAT t(poly.get_num_of_var(), poly.get_num_of_var());
		t.eye(1);
		t.interch_row(iv_idx1, iv_idx2);
		//modify DOMAIN and SCH_MAT, but not impact on LOCVAR_MAT.
		nonsingular(poly, t, NULL, NULL, NULL, NULL, true);

		if (locvar_cols.size() > 0) {
			poly.insert_localvar_cols(locvar_cols);
		}

		//Interchange rows of iv mapping table.
		POLY_sche(poly)->get_map_iv_m()->interchange(d1, d2);
		return true;
	}
#endif
	if (d1 > d2) {
		INT t = d1;
		d1 = d2;
		d2 = t;
	}
	IS_TRUE0(d2 >= 0);
	INT locvar_idx = POLY_locvar_idx(poly);
	IS_TRUE0(locvar_idx < 0 ||
			POLY_sche(poly)->map_depth2iv(d2) < locvar_idx);
	if (d1 >= 0) {
		IS_TRUE0(locvar_idx < 0 ||
			POLY_sche(poly)->map_depth2iv(d1) < locvar_idx);
	}
	//POLY_domain(poly)->interchange(iv_idx1, iv_idx2);
	POLY_sche(poly)->interchange(iv_idx1, iv_idx2);
	return true;
}


bool POLY_TRAN::interchange(LIST<POLY*> & lst, INT d1, INT d2)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!interchange(*p, d1, d2)) {
			return false;
		}
	}
	return true;
}


/* Tiling is a combination of strip-mining and loop-interchange.
This technique breaks each of several loops in a loop
nest into two loops each.
The advantage is that doing so may allow us to work on
small sections (blocks) of
a multidimensional array, one block at a time.

'poly': POLY to handle
'depth': loop level to tile
'B': tile/block size
'changed_depth': record the new level of 'depth' after inserting a loop.
'generated_depth': record the level of the inserted loop.
	This loop is always the loop that be used to walk through tiles. */
bool POLY_TRAN::tiling(IN OUT POLY & poly,
					   UINT depth,
					   UINT B,
					   OUT UINT * changed_depth,
					   OUT UINT * generated_depth)
{
	if (!stripmine(poly, depth, B, changed_depth, generated_depth)) {
		return false;
	}
	if (depth != 0) {
		interchange(poly, -1, *generated_depth);
		*generated_depth = 0;
	}
	return true;
}


/* Tiling for a list of POLY.

'poly': POLY to handle
'iv_idx': loop index to tile
'B': tile/block size
'changed_iv_idx': record the new position of 'iv_idx' after inserting a loop.
'generated_iv_idx': record position of the inserted loop.
	This loop is always the loop that be used to walk through tiles. */
bool POLY_TRAN::tiling(IN OUT LIST<POLY*> & lst,
					   UINT depth,
					   UINT B,
					   OUT UINT * changed_depth,
					   OUT UINT * generated_depth)
{
	bool first = true;
	UINT c, g;
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!tiling(*p, depth, B, changed_depth, generated_depth)) {
			return false;
		}
		#ifdef _DEBUG_
		if (first) {
			c = *changed_depth;
			g = *generated_depth;
			first = false;
		}
		IS_TRUE0(c == *changed_depth && g == *generated_depth);
		#endif
	}
	return true;
}


/* Loop Fission is a schedule transformation with no
explicit impact on the iteration domain and memory access.
Split STMTs at 'depth', and stmts whose syntax-order
less and equal than 'split_p' will be move to a new
adjacent loop nest that is prior to current loop nest at depth.

NOTICE: Each polyhedron in 'lst' must have been in lexical order!

e.g: Split loop nest at depth 2, and the splitting point stmt is S2
		for x //d1
	 	  for y //d2
		    S1
		    for z
		      S2
		    S3
		    for z
		      S4
		    S5
	=>
		for x //d1
		  for y //d2
		    S1
		    for z
		      S2
		  for y
		    S3
		    for z
		      S4
		    S5
'split_p': poly that indicates the split point,
	whereas the poly belong to prior part loop nest.
'red_depth': true if one intend reduce the depth of splitted STMT.
'depth': indicates depth that attempt to split.
*/
bool POLY_TRAN::fission(IN OUT LIST<POLY*> & lst,
						IN OUT LIST<POLY*> & scop_poly_lst,
						IN POLY & split_p,
						UINT depth)
{
	if (depth == 0 || lst.get_elem_count() == 1) return false;
	POLY * p;
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!is_lex_eq(split_p, *p, depth - 1)) {
			return false;
		}
	}
	bool inner_depth_is_same = true;
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!is_lex_eq(split_p, *p, depth)) {
			inner_depth_is_same = false;
			break;
		}
	}
	if (inner_depth_is_same) {
		return false;
	}

	/* Revise other STMT's parent syntactic-order, which are not in 'lst'.
	e.g: Given followed SCOP, perform fission at depth 2,
		and splitting point is S1.
		for x //d1
		  for y //d2
		    S1
		    for z
		      S2
		  for y
		    S3
		    for z
		      S4
		    S5
	After splitting S1, S2 at depth 2, the syntactic order
		of S3,S4,S5 at depth 1 should be 2.
		for x
		  for y
		    S1
		  for y
		    for z
		      S2
		  for y
		    S3
		    for z
		      S4
		    S5
	*/
	SCH_MAT * split_p_sm = POLY_sche(split_p);
	INT parent_split_so = split_p_sm->get_stmt_order(depth - 1);
	for (p = scop_poly_lst.get_head();
		 p != NULL; p = scop_poly_lst.get_next()) {
		if (((INT)depth) - 2 > 0 && !is_lex_eq(split_p, *p, depth - 2)) {
			continue;
		}
		INT so = POLY_sche(*p)->get_stmt_order(depth - 1);
		IS_TRUE0(so >= 0);
		if (so == parent_split_so) {
			continue;
		}
		if (so > parent_split_so) {
			POLY_sche(*p)->inc_stmt_order(depth - 1, 1);
		}
	}

	/* Revise syntactic order for STMTs inter-loop-nest, and find
	STMTs which be in same loop body.
	STMTs must be in lexical order! */
	INT cur_split_so = split_p_sm->get_stmt_order(depth);
	IS_TRUE0(cur_split_so >= 0);
	INT post_loop_so = -1;
	LIST<POLY*> poly_after_split_lst;
	for (p = lst.get_head(); p != NULL; p = lst.get_next()) {
		SCH_MAT * sm = POLY_sche(*p);
		INT sm_so = sm->get_stmt_order(depth);
		IS_TRUE0(sm_so >= 0);
		#ifdef _DEBUG_
		if (post_loop_so == -1) {
			post_loop_so = sm->get_stmt_order(depth - 1);
		}
		IS_TRUE0(post_loop_so == sm->get_stmt_order(depth - 1));
		#endif
		if (sm_so > cur_split_so) {
			//STMTs would be placed at different loop nest to 'split_so'.
			sm->inc_stmt_order(depth - 1);
			poly_after_split_lst.append_tail(p);
		}
	}

	if (poly_after_split_lst.get_elem_count() > 0) {
		UINT new_d = 0;
		//'cur_pos' must be increment number.
		INT cur_pos = POLY_sche(*poly_after_split_lst.get_head())->
											get_stmt_order(depth);
		for (p = poly_after_split_lst.get_head();
			 p != NULL; p = poly_after_split_lst.get_next()) {
			SCH_MAT * sm = POLY_sche(*p);
			INT so = sm->get_stmt_order(depth);
			IS_TRUE0(so >= 0);
			if (so == cur_pos) {
				sm->set_stmt_order(depth, new_d);
			} else if (so > cur_pos) {
				sm->set_stmt_order(depth, ++new_d);
				cur_pos = so;
			} else {
				IS_TRUE(0, ("STMTs must be in lexicographical order"));
			}
		}
	}
	return true;
}


//Nonsingular schedule transformation.
//'t': Nonsingular transformation matrix.
bool POLY_TRAN::nonsingular(IN POLY & poly,
							IN RMAT & t,
							OUT RMAT * pstride,
							OUT RMAT * pidx_map,
							OUT RMAT * pofst,
							OUT RMAT * pmul,
							bool tran_domain)
{
	IS_TRUE0(poly.get_num_of_localvar() == 0);
	if (!t.is_quad() || t.get_row_size() != poly.get_num_of_var()) {
		return false;
	}
	IS_TRUE(t.det() != 0, ("trans-matrix should be nonsingular"));
	RMAT b1, b2, stride, idx_map, ofst, mul;
	if (pstride == NULL) { pstride = &stride; }
	if (pidx_map == NULL) { pidx_map = &idx_map; }
	if (pofst == NULL) { pofst = &ofst; }
	if (pmul == NULL) { pmul = &mul; }

	//Modify ACC_MAT
	//ACC=ACC*T
	//Does it necessary?

	if (tran_domain) {
		LOOP_TRAN lt(POLY_domain(poly), POLY_domain_rhs_idx(poly));
		RMAT trdomain; //transformed domain.
		LIST<RMAT*> new_bounds;
		INT dim = poly.get_num_of_var();
		for (; dim > 0; dim--) {
			RMAT * bd = (RMAT*)xmalloc(sizeof(RMAT));
			bd->init();
			new_bounds.append_tail(bd);
		}
		/*
		If gamma is empty, one could invoke func like:
		lt.tran_iter_space(..., x, ...);
		*/
		lt.tran_iter_space(t, *pstride, *pidx_map,
						new_bounds, *pofst, *pmul, &trdomain);
		POLY_domain(poly)->copy(trdomain);

		#define _DEBUG_TRAN_DOMAIN_
		#ifdef _DEBUG_TRAN_DOMAIN_
		//CHAR * newvar[] = {"u","v","w","x","y","z",};
		CHAR * arr_orgvar[128] = {0};
		for (UINT n = 0; n < poly.get_num_of_var(); n++) {
			CHAR * orgvar = poly.get_var_name(n);
			if (orgvar == NULL) {
				break;
			}
			arr_orgvar[n] = orgvar;
		}
		GEN_C gc((RMAT*)POLY_domain(poly), POLY_domain_rhs_idx(poly));
		gc.set_sym(NULL, arr_orgvar, NULL);
		gc.genlimits(new_bounds, pstride, pidx_map);
		#endif

		//Destroy local variables.
		for (RMAT * r = new_bounds.get_head();
			 r != NULL; r = new_bounds.get_next()) {
			r->destroy();
		}
	} else {
		IS_TRUE(0,
			("Why the transformed effect can not be acting in domain?"));
	}

	//For SCH_MAT, A and ¦£ , A=A*T.
	RMAT x;
	POLY_sche(poly)->get_iter_mat(x);
	IS_TRUE0(x.is_quad() && x.get_col_size() == t.get_row_size());
	//x = x**pidx_map;
	//x = x*t;
	x = t*x;
	POLY_sche(poly)->set_iter_mat(x);
	if (POLY_sche(poly)->get_num_of_gamma() > 0) {
		POLY_sche(poly)->get_gamma_mat(x);
		IS_TRUE0(x.get_col_size() == t.get_row_size());
		//x = x**pidx_map;
		//x = x*t;
		x = t*x;
		POLY_sche(poly)->set_gamma_mat(x);
	}
	return true;
}


/* Singular schedule transformation.
't': singular transformation matrix.
	rows of 't' must be mutually independent. */
bool POLY_TRAN::singular(IN POLY & poly,
						IN RMAT & t,
						OUT RMAT * pstride,
						OUT RMAT * pidx_map,
						OUT RMAT * pofst,
						OUT RMAT * pmul,
						bool tran_domain)
{
	if (t.is_nonsig()) {
		return nonsingular(poly, t, pstride,
				pidx_map, pofst, pmul, tran_domain);
	} else {
		//Padding to invertible matrix.
		IS_TRUE(t.rank() == t.get_row_size(), ("rows should be part of basis"));
		RMAT res(t);
		res.padding();
		return nonsingular(poly, res, pstride,
				pidx_map, pofst, pmul, tran_domain);
	}
	return true;
}


/* Modify DOMAIN, As, ¦£s.
e.g:
	for (i=0,99)
	  S(i)
	=>
	for (ii=-99,0)
	  S(-ii)
*/
bool POLY_TRAN::reverse(IN POLY & poly, UINT depth)
{
	if (depth == 0 || depth > poly.get_max_depth()) {
		return false;
	}
	INT iv_idx = POLY_sche(poly)->map_depth2iv(depth);
	IS_TRUE0(iv_idx >= 0 && iv_idx < (INT)poly.get_num_of_var());
	RMAT locvar_cols;
	if (POLY_locvar_idx(poly) >= 0) {
		IS_TRUE0(POLY_locvar_cs(poly) != NULL);
		poly.remove_localvar_cols(locvar_cols);
	}

	RMAT t(poly.get_num_of_var(), poly.get_num_of_var());
	t.eye(1);
	t.set(iv_idx, iv_idx, -1);
	//modify DOMAIN and SCH_MAT, but not impact on LOCVAR_MAT.
	nonsingular(poly, t, NULL, NULL, NULL, NULL, true);
	if (locvar_cols.size() > 0) {
		poly.insert_localvar_cols(locvar_cols);
	}
	POLY_sche(poly)->reverse(iv_idx);
	return true;
}


bool POLY_TRAN::reverse(IN OUT LIST<POLY*> & lst, UINT depth)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!reverse(*p, depth)) {
			return false;
		}
	}
	return true;
}


/* Return true if poly skewed at 'iv_idx' relative to coodinated iv_idx.
'd_iv': depth to skew.
'd_co': it is the coordinate variable for d_iv.
	And its depth should less than 'd_iv'.
	e.g:
		for j
		  for i
		    for k
			  S(i,j,k)
	=>
		d_iv is i, d_co is j.
		for j
		  for j+i
		    for k
			  S(i,j,k)
*/
bool POLY_TRAN::skew(IN OUT POLY & poly, UINT d_iv, UINT d_co, UINT factor)
{
	if (d_co >= d_iv || d_iv == 0 || d_co == 0) {
		return false;
	}
	INT iv_idx = POLY_sche(poly)->map_depth2iv(d_iv);
	INT co = POLY_sche(poly)->map_depth2iv(d_co);
	if (iv_idx < 0 || co < 0) {
		return false;
	}
	RMAT locvar_cols;
	if (POLY_locvar_idx(poly) >= 0) {
		IS_TRUE0(POLY_locvar_cs(poly) != NULL);
		poly.remove_localvar_cols(locvar_cols);
	}

	RMAT t(poly.get_num_of_var(), poly.get_num_of_var());
	t.eye(1);
	t.set(iv_idx, co, factor);
	//modify DOMAIN and SCH_MAT, but not impact on LOCVAR_MAT.
	nonsingular(poly, t, NULL, NULL, NULL, NULL, true);
	if (locvar_cols.size() > 0) {
		poly.insert_localvar_cols(locvar_cols);
	}
	return true;
}


bool POLY_TRAN::skew(IN OUT LIST<POLY*> & lst,
					UINT d_iv, UINT d_co, UINT factor)
{
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		if (!skew(*p, d_iv, d_co, factor)) {
			return false;
		}
	}
	return true;
}


//Cutting Domain.
//'c': vector that expresses an inequlity to constrain domain.
bool POLY_TRAN::cutdomain(IN POLY & poly, IN RMAT & c)
{
	IS_TRUE0(c.is_vec());
	RMAT * domain = POLY_domain(poly);
	IS_TRUE0(c.get_col_size() == domain->get_col_size());
	domain->grow_row(c);
	return true;
}


/* Shift implements a kind of hierachical software pipelining on the
source code with parametric iteraion shifts.
e.g: Delay STMT by N iterations.

't': transformation matrix. It must have same dimension as constant
part of domain, including the constant-symbols-column. */
bool POLY_TRAN::shift(IN POLY & poly, IN UINT depth,
					IN UINT pv_idx, IN INT shift_val)
{
	SCH_MAT * sch = POLY_sche(poly);
	sch->set_map_depth2pv(depth, pv_idx, shift_val);
	return true;
}


void POLY_TRAN::dump_poly_tree(POLY_TREE * t, INT indent)
{
	CHAR buf[256];
	FILE * h = fopen(DUMP_FILE_NAME, "a+");
	while (t != NULL) {
		fprintf(h, "\n");
		INT i = indent;
		while (i > 0) { fprintf(h, "  "); i--; }
		switch (POLY_TREE_type(t)) {
		case POLY_TREE_UNDEF:
			IS_TRUE0(0);
			break;
		case POLY_TREE_LOOP:
			{
				fprintf(h, "LOOP");
				dump_poly_tree(POLY_TREE_body(t), indent + 1);
			}
			break;
		case POLY_TREE_STMT:
			{
				fprintf(h, "STMT:%s", POLY_TREE_poly(t)->dumpbuf(buf));
			}
			break;
		}
		t = POLY_TREE_next(t);
	}
	fclose(h);
}


POLY_TREE * POLY_TRAN::_scan(IN LIST<POLY*> & plst,
						POLY_TREE_MGR & ptmgr, INT depth)
{
	SVECTOR<LIST<POLY*>*> kid_poly_lst;

	//For local utility of POLY TREE vectorizing accessing.
	SVECTOR<POLY_TREE*> tmpvec;
	//Find maximum static order.
	INT sorder = -1;
	POLY * p;
	for (p = plst.get_head(); p != NULL; p = plst.get_next()) {
		sorder = MAX(POLY_sche(*p)->get_stmt_order(depth), sorder);
	}
	if (sorder == -1) {
		//There is no any stmt at depth.
		return NULL;
	}

	INT i;
	for (i = 0; i <= sorder; i++) {
		POLY_TREE  * pt = ptmgr.new_poly_tree();
		tmpvec.set(i, pt);
	}

	//Collect the information of which STMT owns kids at next depth.
	for (p = plst.get_head(); p != NULL; p = plst.get_next()) {
		INT so = POLY_sche(*p)->get_stmt_order(depth);
		INT kid_so = POLY_sche(*p)->get_stmt_order(depth + 1);
		if (kid_so == -1) {
			continue;
		}
		LIST<POLY*> * kid_lst = kid_poly_lst.get(so);
		if (kid_lst == NULL) {
			kid_lst = (LIST<POLY*>*)ptmgr.xmalloc(sizeof(LIST<POLY*>));
			kid_lst->init();
			kid_poly_lst.set(so, kid_lst);
		}
		kid_lst->append_tail(p);
	}

	//Fill POLY TREE.
	for (p = plst.get_head(); p != NULL; p = plst.get_next()) {
		INT so = POLY_sche(*p)->get_stmt_order(depth);
		POLY_TREE * pt = tmpvec.get(so);
		IS_TRUE0(pt != NULL);
		if (depth != (INT)POLY_sche(*p)->get_max_depth()) {
			POLY_TREE_type(pt) = POLY_TREE_LOOP;
		} else {
			POLY_TREE_type(pt) = POLY_TREE_STMT;
			POLY_TREE_poly(pt) = p;
		}
	}

	//Scan kid to construct poly tree.
	INT kid_depth = depth + 1;
	for (i = 0; i <= kid_poly_lst.get_last_idx(); i++) {
		LIST<POLY*> * kid_lst = kid_poly_lst.get(i);
		if (kid_lst == NULL) {
			continue;
		}
		POLY_TREE * body = _scan(*kid_lst, ptmgr, kid_depth);
		POLY_TREE * parent = tmpvec.get(i);
		IS_TRUE0(parent != NULL);
		POLY_TREE_body(parent) = body;
	}

	//Construct poly tree of the depth refer to.
	POLY_TREE * head = NULL;
	for (i = 0; i <= tmpvec.get_last_idx(); i++) {
		POLY_TREE * p =  tmpvec.get(i);
		insertbefore_one(&head, head, p);
	}
	head = reverse_list(head);

	//Destroy local used variable.
	for (i = 0; i <= kid_poly_lst.get_last_idx(); i++) {
		LIST<POLY*> * kid_lst = kid_poly_lst.get(i);
		if (kid_lst != NULL) {
			kid_lst->destroy();
		}
	}
	return head;
}


void POLY_TRAN::scan(IN LIST<POLY*> & plst)
{
	POLY_TREE_MGR ptmgr;
	POLY_TREE * root = _scan(plst, ptmgr, 0);
	dump_poly_tree(root, 0);
}


//Assign unique id to each dep-poly.
void POLY_TRAN::step_0(IN OUT DG & g)
{
	UINT count = 0;
	INT c;
	for (EDGE * e = g.get_first_edge(c); e != NULL; e = g.get_next_edge(c)) {
		DGEINFO const* ei = (DGEINFO*)EDGE_info(e);
		DEP_POLY_LIST * dpl = DGEINFO_dpvec(ei)->get_innermost();
		IS_TRUE0(dpl != NULL && dpl->get_elem_count() == 1);
		DEP_POLY * dp = dpl->get_head();
		IS_TRUE0(dp != NULL);
		DEP_POLY_id(*dp) = count++;
	}
}


/* Record start, end idx of u-var.
e.g:
	u-var for S1 are u0, u1, u2; u-var for S2 are u3, u4, u5, u6;
	start,end idx of S1 are 0,2, and start,end idx of S2 are 3,6.
	It is similar for lambda-var.
*/
void POLY_TRAN::step_1(IN DG & g,
					IN OUT SVECTOR<UINT> & start_u_idx,
					IN OUT SVECTOR<UINT> & end_u_idx,
					IN OUT SVECTOR<UINT> & start_lam_idx,
					IN OUT SVECTOR<UINT> & end_lam_idx,
					IN OUT SVECTOR<POLY*> & poly_vec,
					IN OUT UINT * u_count,
					IN OUT UINT * lam_count)
{
	*u_count = 0;
	*lam_count = 0;
	SVECTOR<bool> is_u_record, is_lam_record;
	INT c;
	for (EDGE * e = g.get_first_edge(c); e != NULL; e = g.get_next_edge(c)) {
		VERTEX const* fromv = EDGE_from(e);
		VERTEX const* tov = EDGE_to(e);
		POLY * from = (POLY*)VERTEX_info(fromv);
		POLY * to = (POLY*)VERTEX_info(tov);
		IS_TRUE0(from != NULL && to != NULL &&
				 from->get_num_of_localvar() == 0 && to->get_num_of_localvar() == 0);
		DGEINFO const* ei = (DGEINFO*)EDGE_info(e);
		DEP_POLY_LIST * dpl = DGEINFO_dpvec(ei)->get_innermost();
		IS_TRUE0(dpl != NULL && dpl->get_elem_count() == 1);
		DEP_POLY const* dp = dpl->get_head();
		IS_TRUE0(dp != NULL);

		//from
		UINT num_u_var = 1/*u0*/ + POLY_domain(*from)->get_row_size()/*u1~uk*/;
		UINT id = POLY_id(*from);
		if (!is_u_record.get(id)) {
			is_u_record.set(id, true);
			start_u_idx.set(id, *u_count);
			end_u_idx.set(id, *u_count + num_u_var - 1);
			poly_vec.set(id, from);
			*u_count += num_u_var;
		}

		//to
		num_u_var = 1/*u0*/ + POLY_domain(*to)->get_row_size()/*u1~uk*/;
		id = POLY_id(*to);
		if (!is_u_record.get(id)) {
			is_u_record.set(id, true);
			start_u_idx.set(id, *u_count);
			end_u_idx.set(id, *u_count + num_u_var - 1);
			poly_vec.set(id, to);
			*u_count += num_u_var;
		}

		//lambda
		UINT num_lam_var = 1/*¦Ë0*/ + dp->get_row_size()/*¦Ë1~¦Ëk*/;
		id = DEP_POLY_id(*dp);
		if (!is_lam_record.get(id)) {
			is_lam_record.set(id, true);
			start_lam_idx.set(id, *lam_count);
			end_lam_idx.set(id, *lam_count + num_lam_var - 1);
			*lam_count += num_lam_var;
		}
	}
}


//Construct formal equations which variable is u-variable and ¦Ë-variable.
void POLY_TRAN::step_2(IN DG & g,
					IN OUT RMAT & sys,
					IN OUT SVECTOR<RMAT*> & theta_vec,
					IN OUT SVECTOR<RMAT*> & lam_vec,
					IN SVECTOR<UINT> const& start_u_idx,
					IN SVECTOR<UINT> const& end_u_idx,
					IN SVECTOR<UINT> const& start_lam_idx,
					IN SVECTOR<UINT> const& end_lam_idx,
					IN UINT u_count,
					IN UINT lam_count)
{
	INT num_iv = -1; /*num of i,j,k... CST, N,M...*/
	INT c;
	for (EDGE const* e = g.get_first_edge(c);
		 e != NULL; e = g.get_next_edge(c)) {
		VERTEX const* fromv = EDGE_from(e);
		VERTEX const* tov = EDGE_to(e);
		POLY const* from = (POLY*)VERTEX_info(fromv);
		POLY const* to = (POLY*)VERTEX_info(tov);
		DGEINFO const* ei = (DGEINFO*)EDGE_info(e);
		DEP_POLY_LIST * dpl = DGEINFO_dpvec(ei)->get_innermost();
		IS_TRUE0(dpl != NULL && dpl->get_elem_count() == 1);
		DEP_POLY const* dp = dpl->get_head();
		IS_TRUE0(dp != NULL);

		/* Mapping between u-var and iteration-var.
		e.g:
			i   >=0
			-i+N>=0
			j   >=0
			-j+N>=0
			u1,1 is coeff of (i),
			u1,2 is coeff of (-i+N),
			u1,3 is coeff of (j),
			u1,4 is coeff of (-j+N),

				u1,0  u1,1  u1,2  u1,3  u1,4
			i	0     1     -1    0      0
			j   0     0      0    1     -1
			CST 1     0      0    0      0
			N   0     0      1    0      1

		*/
		RMAT u_of_from, u_of_to, lam;
		if (num_iv == -1) {
			//num of i,j,k... CST, N,M...
			num_iv = POLY_domain(*from)->get_col_size();
		}

		//num of i,j,k... CST, N,M...
		IS_TRUE0((UINT)num_iv == POLY_domain(*from)->get_col_size());

		{//Construct u for 'from' STMT.
			DOMAIN_MAT const* d = POLY_domain(*from);
			UINT rhs_idx = POLY_domain_rhs_idx(*from);
			UINT num_u_var = 1/*u1,0*/ + d->get_row_size()/*u1,1~u1,k*/;
			IS_TRUE0((UINT)num_iv == d->get_col_size());

			u_of_from.reinit(num_iv, num_u_var);
			RMAT td(*d);
			/*
			Orinal ineq:
				-i   <=-1
				i    <=N
				-j   <=0
				j    <=N
			formats to:
				i -1 >=0
				-i+N >=0
				j    >=0
				-j+N >=0
			*/
			//Consider 'quasi affine function'.
			RMAT const* quasi = DGEINFO_from_quasi_func(ei);
			if (quasi != NULL) {
				IS_TRUE0(quasi->get_col_size() == td.get_col_size());

				LINEQ l(NULL);
				for (UINT i = 0; i < quasi->get_row_size(); i++) {
					//each row indicates affine func of iteration variable.
					RMAT q;
					quasi->inner_row(q, i, i);
					l.substi_and_expand(td, rhs_idx, q, i);
				}
			}

			//Convert compare-relation from '<=' to '>='.
			td.mul_of_cols(0, rhs_idx - 1, -1);

			UINT k = 1;
			u_of_from.set(rhs_idx, 0, 1); //indicate u1,0
			for (UINT i = 0; i < td.get_row_size(); i++, k++) {
				for (UINT j = 0; j < td.get_col_size(); j++) {
					u_of_from.set(j, k, td.get(i, j));
				}
			}
			theta_vec.set(POLY_id(*from), new RMAT(u_of_from));
		}

		{ //Construct u for 'to' STMT.
			DOMAIN_MAT const* d = POLY_domain(*to);
			UINT rhs_idx = POLY_domain_rhs_idx(*to);
			IS_TRUE0((UINT)num_iv == d->get_col_size());
			UINT num_u_var =  1/*u1,0*/ + d->get_row_size()/*u1,1~u1,k*/;

			u_of_to.reinit(num_iv, num_u_var);
			RMAT td(*d);

			//Consider 'quasi affine function'.
			RMAT const* quasi = DGEINFO_to_quasi_func(ei);
			if (quasi != NULL) {
				IS_TRUE0(quasi->get_col_size() == td.get_col_size());
				LINEQ l(NULL);
				for (UINT i = 0; i < quasi->get_row_size(); i++) {
					//each row indicates affine func of iteration variable.
					RMAT q;
					quasi->inner_row(q, i, i);
					l.substi_and_expand(td, rhs_idx, q, i);
				}
			}

			//Convert compare-relation from '<=' to '>='
			td.mul_of_cols(0, rhs_idx - 1, -1);

			UINT k = 1;
			u_of_to.set(rhs_idx, 0, 1); //indicate u1,0
			for (UINT i = 0; i < td.get_row_size(); i++, k++) {
				for (UINT j = 0; j < td.get_col_size(); j++) {
					u_of_to.set(j, k, td.get(i, j));
				}
			}
			theta_vec.set(POLY_id(*to), new RMAT(u_of_to));
		}

		{ //Construct lambda-variable for dependence polyhedron
			UINT rhs_idx = DEP_POLY_rhs_idx(*dp);
			IS_TRUE0((UINT)num_iv == dp->get_col_size());
			UINT num_lam_var =  1/*¦Ë1,0*/ + dp->get_row_size()/*¦Ë1,1~¦Ë1,k*/;

			lam.reinit(num_iv, num_lam_var);
			RMAT td(*dp);
			td.mul_of_cols(0, rhs_idx - 1, -1);

			UINT k = 1;
			lam.set(rhs_idx, 0, 1); //indicate ¦Ë1,0
			for (UINT i = 0; i < td.get_row_size(); i++, k++) {
				for (UINT j = 0; j < td.get_col_size(); j++) {
					lam.set(j, k, td.get(i, j));
				}
			}
			IS_TRUE0(lam_vec.get(DEP_POLY_id(*dp)) == NULL);
			lam_vec.set(DEP_POLY_id(*dp), new RMAT(lam));
		}

		/* Construct equations which format be:
			-(u1,0 ... u1,k) + (u2,0 ... u2,k) - 1 = ¦Ë1,0 ... ¦Ë1,m
		*/
		{
			//Compute column index.
			UINT ustart_from = start_u_idx.get(POLY_id(*from));
			UINT uend_from = end_u_idx.get(POLY_id(*from));
			UINT ustart_to = start_u_idx.get(POLY_id(*to));
			UINT uend_to = end_u_idx.get(POLY_id(*to));
			UINT lstart = start_lam_idx.get(DEP_POLY_id(*dp));
			UINT lend = end_lam_idx.get(DEP_POLY_id(*dp));

			IS_TRUE0(uend_from - ustart_from + 1 == u_of_from.get_col_size());
			IS_TRUE0(uend_to - ustart_to + 1 == u_of_to.get_col_size());
			IS_TRUE0(lend - lstart + 1 == lam.get_col_size());

			//
			//Format equation as: (u0...uk) - (¦Ë0 ... ¦Ëm) = -CST
			//
			RMAT tsys(num_iv, u_count + lam_count + 1);

			//-CST is 1, set CST first.
			tsys.set(POLY_domain_rhs_idx(*from), tsys.get_col_size() -  1, 1);

			//Construct u-var: (u0...uk) = -(u1,0 ... u1,k) + (u2,0 ... u2,k)
			u_of_from.mul(-1);

			if (from == to) {
				//'from' and 'to' are same STMT, thus u-vars are identical for both.
				//(u0...uk) = -(u2,0 ... u2,k) + (u2,0 ... u2,k)
				for (UINT z = 0; z < u_of_to.get_row_size(); z++) {
					u_of_to.add_row_to_row(u_of_from, z, z);
				}
			} else {
				tsys.set_cols(ustart_from, uend_from, u_of_from, 0);
			}
			tsys.set_cols(ustart_to, uend_to, u_of_to, 0);

			//Construct lam-var: - (¦Ë0 ... ¦Ëm)
			lam.mul(-1);
			tsys.set_cols(u_count + lstart, u_count + lend, lam, 0);

			if (sys.get_row_size() == 0) {
				sys.copy(tsys);
			} else {
				sys.grow_row(tsys, 0, tsys.get_row_size() - 1);
			}
		}
	}
}


void POLY_TRAN::step_3_1(IN OUT DG & g,
						POLY const* p,
						RMAT const& sol,
						SVECTOR<RMAT*> const& theta_vec,
						SVECTOR<UINT> const& start_u_idx,
						SVECTOR<UINT> const& end_u_idx)
{
	INT i = POLY_id(*p), j;
	INT rhs_idx = POLY_domain_rhs_idx(*p);
	INT nvar = p->get_num_of_var();
	RMAT * sch = g.get_sch_mat(p);
	IS_TRUE0(sch != NULL);
	RMAT const* theta = theta_vec.get(i);
	IS_TRUE0(theta->get_row_size() == POLY_domain(*p)->get_col_size());
	UINT start = start_u_idx.get(i);
	UINT end = end_u_idx.get(i);

	RATIONAL v = 0;
	//Compute coefficient of index variables.
	for (j = 0; j < nvar; j++) {
		v = 0;
		for (UINT k = 0; k <= end - start; k++) {
			if (theta->get(j, k) == 0) {
				continue;
			}
			v = v + sol.get(0, start + k) * theta->get(j, k);
		}
		sch->set(0, j, v);
	}

	{//Compute CST
		v = 0;
		j = rhs_idx;
		for (UINT k = 0; k <= end - start; k++) {
			RATIONAL kv;
			if ((kv = theta->get(j, k)) == 0) {
				continue;
			}
			v = v + sol.get(0, start + k) * kv;
		}
		sch->set(0, j, v);

	}

	//Compute coefficient of global symbol parameter.
	for (j = rhs_idx + 1; j < (INT)theta->get_row_size(); j++) {
		v = 0;
		for (UINT k = 0; k <= end - start; k++) {
			RATIONAL kv;
			if ((kv = theta->get(j, k)) == 0) {
				continue;
			}
			v = v + sol.get(0, start + k) * kv;
		}
		sch->set(0, j, v);
	}
}


//Compute schedule matrix for each POLY.
void POLY_TRAN::step_3(IN OUT DG & g,
					  RMAT const& sol,
					  SVECTOR<RMAT*> const& theta_vec,
					  SVECTOR<UINT> const& start_u_idx,
					  SVECTOR<UINT> const& end_u_idx)
{
	INT c;
	for (VERTEX * v = g.get_first_vertex(c);
		 v != NULL; v = g.get_next_vertex(c)) {
		POLY const* p = (POLY const*)VERTEX_info(v);
		if (p == NULL) { continue; }
		step_3_1(g, p, sol, theta_vec, start_u_idx, end_u_idx);
	}
}


/* Compute upper bound of time dimension. The lower bound must be 0.
	e.g: Given loop nest,
		for (i=0:99) {
		  s[i]=0 //S1
		  for (j=0:99)
		    s[i]=s[i]+... //S2
		}
	output:
		for (t=0:100) {
		  for (i=0:99) {
		    s[i]=0, if (t==0) exec
		    for (j=0:99)
		      s[i]=s[i]+... , if (t==j+1) exec
		  }
		}
*/
void POLY_TRAN::step_4(IN DG & g, OUT RMAT & ub)
{
	ub.clean();
	RMAT lub;
	INT rhs_idx = -1;
	VERTEX * v;
	INT c;
	for (v = g.get_first_vertex(c); v != NULL; v = g.get_next_vertex(c)) {
		POLY const* p = (POLY const*)VERTEX_info(v);
		if (p == NULL) { continue; }
		if (rhs_idx == -1) {
			rhs_idx = POLY_domain_rhs_idx(*p);
		}
		IS_TRUE0(rhs_idx == (INT)POLY_domain_rhs_idx(*p));
		if (lub.get_row_size() == 0) {
			lub.copy(*POLY_domain(*p));
		} else {
			lub.grow_row(*POLY_domain(*p), 0,
						POLY_domain(*p)->get_row_size() - 1);
		}
	}

	if (lub.get_row_size() == 0) {
		return;
	}

	//Insert time dimension variable 't','i','j'.
	lub.insert_col_before(0);
	lub.grow_row(1);
	lub.set(lub.get_row_size() - 1, 0, -1); //append t>=0

	//Append equation relation between 't' and other iteration variables.
	INT new_rhs_idx = rhs_idx + 1;
	for (v = g.get_first_vertex(c); v != NULL; v = g.get_next_vertex(c)) {
		POLY const* p = (POLY const*)VERTEX_info(v);
		if (p == NULL) { continue; }
		RMAT * sch = g.get_sch_mat(p);
		IS_TRUE0(sch != NULL);
		RMAT eq(sch->get_row_size(), lub.get_col_size());
		eq.set_col(0, 1); //mark 't' var.

		//Construct equations.
		//e.g: sch mat is j+1, append t=j+1
		UINT i;
		for (i = 0; i < sch->get_row_size(); i++) {
			INT j;
			for (j = 0; j < rhs_idx; j++) {
				eq.set(i, j+1, -sch->get(0, j));
			}
			for (j = rhs_idx; j < (INT)sch->get_col_size(); j++) {
				eq.set(i, j+1, sch->get(0, j));
			}
		}

		//Append equations to inequality system.
		RMAT tub(lub);
		LINEQ lin(&tub, new_rhs_idx);
		lin.append_eq(eq);

		//Compute boundary of variables.
		for (i = new_rhs_idx - 1; i > 0; i--) {
			RMAT res;
			if (!lin.fme(i, res, false)) {
				IS_TRUE(0, ("system is inconsistency!"));
			}
			tub = res;
		}
		if (ub.get_row_size() == 0) { ub.copy(tub); }
		else { ub.grow_row(tub, 0, tub.get_row_size() - 1); }
		//
	}

	//Remove redundant constrains.
	LINEQ lin(NULL);
	if (!lin.reduce(ub, new_rhs_idx, false)) {
		IS_TRUE0(0);
	}
}


void POLY_TRAN::dump_lambda_info(IN DEP_POLY const* dp,
								 IN POLY const* from,
								 IN POLY const* to,
								 IN SVECTOR<UINT> const& start_lam_idx,
								 IN SVECTOR<UINT> const& end_lam_idx,
				   				 IN SVECTOR<RMAT*> const& lam_vec,
								 IN FILE * h)
{
	IS_TRUE0(dp != NULL);
	INT i = DEP_POLY_id(*dp);

	//All dependence polyhedra should be same dimension.
	INT rhs_idx = DEP_POLY_rhs_idx(*dp);
	RMAT const* lam = lam_vec.get(i);
	CHAR buf[64];

	IS_TRUE0(lam != NULL);
	fprintf(h, "\n----- LAMBDA%d ------- POLY%d->POLY%d -----------------",
			i, POLY_id(*from), POLY_id(*to));

	/* Mapping between ¦Ë-var and iteration-var.
	e.g:
		i   >=0
		-2i+N>=0
		3j   >=0
		-j+N>=0
		¦Ë1,1 is coeff of (i),
		¦Ë1,2 is coeff of (-i+N),
		¦Ë1,3 is coeff of (j),
		¦Ë1,4 is coeff of (-j+N),

			¦Ë1,0  ¦Ë1,1  ¦Ë1,2  ¦Ë1,3  ¦Ë1,4
		i	0      1      -2     0      0
		j   0      0      0      3     -1
		CST 1      0      0      0      0
		N   0      0      1      0      1

	Print as:
		¦È(from,h(e),N)-¦È(to,h(e),N)-1=
			¦Ë1,0 +
			(¦Ë1,1+¦Ë1,2*(-2))i +
			(¦Ë1,3*3-¦Ë1,4)j +
			(¦Ë1,2+¦Ë1,4)N + ¦Ë1,0
	*/
	UINT start = start_lam_idx.get(i);
	UINT end = end_lam_idx.get(i);
	{
		//Dump lambda matrix
		UINT w;
		fprintf(h, "\n¦Ë matrix is : \n");
		for (w = 0; w <= end - start; w++) {
			fprintf(h, "       ¦Ë%d,%d", i, w);
		}
		for (w = 0; w < (UINT)rhs_idx; w++) {
			fprintf(h, "\n i%d", w);
			for (UINT j = 0; j < lam->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(lam->get(w,j), buf, false));
			}
		}
		{
			fprintf(h, "\nCST");
			w = rhs_idx;
			for (UINT j = 0; j < lam->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(lam->get(w,j), buf, false));
			}
		}
		for (w = rhs_idx + 1; w < lam->get_row_size(); w++) {
			fprintf(h, "\n N%d", w - rhs_idx - 1);
			for (UINT j = 0; j < lam->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(lam->get(w,j), buf, false));
			}
		}
	}
	fflush(h);
}


void POLY_TRAN::dump_poly_info(IN RMAT const& sol,
							   IN POLY const* p,
							   IN SVECTOR<UINT> const& start_u_idx,
							   IN SVECTOR<UINT> const& end_u_idx,
							   IN SVECTOR<POLY*> const& poly_vec,
							   IN SVECTOR<RMAT*> const& theta_vec,
							   IN FILE * h)
{
	IS_TRUE0(p != NULL);
	INT i = POLY_id(*p);

	//All polyhedra should be same dimension.
	INT rhs_idx = POLY_domain_rhs_idx(*p);
	RMAT const* theta = theta_vec.get(i);
	CHAR buf[64];

	IS_TRUE0(theta != NULL);
	fprintf(h, "\n--------POLY%d-------------------", i);

	/* Mapping between u-var and iteration-var.
	e.g:
		i   >=0
		-2i+N>=0
		3j   >=0
		-j+N>=0
		u1,1 is coeff of (i),
		u1,2 is coeff of (-i+N),
		u1,3 is coeff of (j),
		u1,4 is coeff of (-j+N),

			u1,0  u1,1  u1,2  u1,3  u1,4
		i	0     1     -2    0      0
		j   0     0      0    3     -1
		CST 1     0      0    0      0
		N   0     0      1    0      1

	Print as:
		¦È(S)= (u1,1*1 + U1,2*(-2))i  +
			(u1,3*3 + u1,4*(-1))j +
			(u1,2 + u1,4)N + (u1,0)
	*/
	UINT start = start_u_idx.get(i);
	UINT end = end_u_idx.get(i);
	{
		//Dump theta matrix
		UINT w;
		fprintf(h, "\n¦È matrix is : \n");
		for (w = 0; w <= end - start; w++) {
			fprintf(h, "       u%d,%d", i, w);
		}
		for (w = 0; w < (UINT)rhs_idx; w++) {
			fprintf(h, "\n i%d", w);
			for (UINT j = 0; j < theta->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(theta->get(w,j), buf, false));
			}
		}
		{
			fprintf(h, "\nCST");
			w = rhs_idx;
			for (UINT j = 0; j < theta->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(theta->get(w,j), buf, false));
			}
		}
		for (w = rhs_idx + 1; w < theta->get_row_size(); w++) {
			fprintf(h, "\n N%d", w - rhs_idx - 1);
			for (UINT j = 0; j < theta->get_col_size(); j++) {
				fprintf(h, "%s", format_rational(theta->get(w,j), buf, false));
			}
		}
	}

	//
	fprintf(h, "\nSolution of u-var(u%d,0~u%d,%d) : ", i, i, end - start);
	INT j;
	for (j = start; j <= (INT)end; j++) {
		IS_TRUE0(sol.get(0, j).den() == 1);
		fprintf(h, "%d, ", sol.get(0, j).num());
	}
	fprintf(h, "\n¦È(S)=");
	RATIONAL v1 = 0, v2 = 0, v3 = 0;
	for (j = 0; j < rhs_idx; j++) {
		RATIONAL v = 0;
		for (UINT k = 0; k <= end - start; k++) {
			if (theta->get(j, k) == 0) {
				continue;
			}
			v = v + sol.get(0, start + k) * theta->get(j, k);
		}
		if (v != 0) {
			if (v == 1) {
				fprintf(h, "+i%d", j);
			} else if (v == -1) {
				fprintf(h, "-i%d", j);
			} else {
				fprintf(h, "+%s*i%d", format_rational(v, buf, true), j);
			}
		}
		v1 = v1 + v;
	}
	//

	{//CST
		j = rhs_idx;
		for (UINT k = 0; k <= end - start; k++) {
			RATIONAL kv;
			if ((kv = theta->get(j, k)) == 0) {
				continue;
			}
			v2 = v2 + sol.get(0, start + k) * kv;
		}
		if (v2 != 0) {
			if (v1 != 0) { fprintf(h, "+"); }
			fprintf(h, "%s", format_rational(v2, buf, false));
		}
	}

	for (j = rhs_idx + 1; j < (INT)theta->get_row_size(); j++) {
		RATIONAL v = 0;
		for (UINT k = 0; k <= end - start; k++) {
			RATIONAL kv;
			if ((kv = theta->get(j, k)) == 0) {
				continue;
			}
			v = v + sol.get(0, start + k) * kv;
		}
		if (v != 0) {
			if (j == rhs_idx + 1 && v1 + v2 != 0) { fprintf(h, " + "); }
			if (v == 1) {
				fprintf(h, "+N%d", j);
			} else if (v == -1) {
				fprintf(h, "-N%d", j);
			} else {
				fprintf(h, "+%s*N%d", format_rational(v, buf, true), j);
			}
		}
		v3 = v3 + v;
	}

	if (v1 + v2 + v3 == 0) {
		fprintf(h, "0"); //execution time is 0
	}
	fflush(h);
}


void POLY_TRAN::fea_dump(IN DG & g,
						 IN RMAT const& sol,
						 IN SVECTOR<UINT> const& start_u_idx,
						 IN SVECTOR<UINT> const& end_u_idx,
						 IN SVECTOR<UINT> const& start_lam_idx,
						 IN SVECTOR<UINT> const& end_lam_idx,
						 IN SVECTOR<POLY*> const& poly_vec,
						 IN SVECTOR<RMAT*> const& theta_vec,
						 IN SVECTOR<RMAT*> const& lam_vec,
						 IN FILE * h)
{
	for (INT i = 0; i <= poly_vec.get_last_idx(); i++) {
		POLY const* p = poly_vec.get(i);
		if (p == NULL) { continue; }
		dump_poly_info(sol, p, start_u_idx,
					   end_u_idx, poly_vec, theta_vec, h);
	}
	INT c;
	for (EDGE const* e = g.get_first_edge(c);
		 e != NULL; e = g.get_next_edge(c)) {
		POLY const* from = (POLY*)VERTEX_info(EDGE_from(e));
		POLY const* to = (POLY*)VERTEX_info(EDGE_to(e));
		DEP_POLY_LIST * dpl =
			DGEINFO_dpvec((DGEINFO*)EDGE_info(e))->get_innermost();
		IS_TRUE0(dpl != NULL && dpl->get_elem_count() == 1);
		DEP_POLY const* dp = dpl->get_head();
		IS_TRUE0(dp != NULL);
		dump_lambda_info(dp, from, to,
						 start_lam_idx, end_lam_idx,
						 lam_vec, h);
	 }
}


/* Find a Schedule for all STMT of DG.
Return true if there is a schedule, otherwise return false. The
Schedule that computed for each STMT is recorded at vertex of 'g'.

'g': generalized dependence graph
'ub: bound of outermost (time-dimension) loop.

NOTICE: All variables must be positive.
	e.g: If the index variable's domain is i>=-10 and i<=0,
	the result is illegal!
*/
bool POLY_TRAN::fea_schedule(IN OUT DG & g, OUT RMAT & ub)
{
	SVECTOR<UINT> start_u_idx, end_u_idx, start_lam_idx, end_lam_idx;
	SVECTOR<POLY*> poly_vec;
	SVECTOR<RMAT*> theta_vec, lam_vec;
	UINT u_count = 0, lam_count = 0;
	step_0(g);
	step_1(g, start_u_idx, 	end_u_idx,
		   start_lam_idx, end_lam_idx,
		   poly_vec, &u_count, &lam_count);

	RMAT sys;
	step_2(g, sys, theta_vec,
		   lam_vec, start_u_idx,
		   end_u_idx, start_lam_idx,
		   end_lam_idx, u_count, lam_count);

	//Prepare data for SIX solver.
	UINT num_of_var = sys.get_col_size() - 1;
	IS_TRUE0(num_of_var == u_count + lam_count);
	RMAT tgtf(1, sys.get_col_size());
	UINT i;
	for (i = 0; i < u_count; i++) {
		tgtf.set(0, i, 1);
	}
	RMAT leq, sol;
	RMAT vc(num_of_var, sys.get_col_size());
	for (i = 0; i < num_of_var; i++) {
		vc.set(i, i, -1);
	}

	FILE * h;
	MIP<RMAT, RATIONAL> six;
	six.revise_target_func(tgtf, sys, leq, num_of_var);
	RATIONAL v;
	bool st;
	if (SIX_SUCC == six.maxm(v, sol, tgtf, vc, sys, leq)) {
		printf("maxv is %d/%d\n", v.num(), v.den());
		st = true;
	} else if (SIX_SUCC == six.minm(v, sol, tgtf, vc, sys, leq)) {
		printf("minv is %d/%d\n", v.num(), v.den());
		st = true;
	} else {
		printf("target function is unbound");
		st = false;
		goto FAIL;
	}
	step_3(g, sol, theta_vec, start_u_idx, end_u_idx);
	step_4(g, ub);

	h = fopen(DUMP_FILE_NAME, "a+");
	IS_TRUE0(h != NULL);
	fea_dump(g, sol, start_u_idx, end_u_idx,
			 start_lam_idx, end_lam_idx,
			 poly_vec, theta_vec,
			 lam_vec, h);
	fclose(h);

FAIL:
	INT j;
	for (j = 0; j <= theta_vec.get_last_idx(); j++) {
		RMAT * t;
		if ((t = theta_vec.get(j)) != NULL) {
			delete t;
		}
	}
	for (j = 0; j <= lam_vec.get_last_idx(); j++) {
		RMAT * t;
		if ((t = lam_vec.get(j)) != NULL) {
			delete t;
		}
	}
	return st;
}


//Return true if p1 and p2 have same syntax order till 'depth'.
bool POLY_TRAN::is_lex_eq(POLY const& p1, POLY const& p2, UINT depth)
{
	IS_TRUE0(POLY_sche(p1)->get_stmt_order(depth) >= 0 ||
			POLY_sche(p2)->get_stmt_order(depth) >= 0);
	if (depth <= MIN(p1.get_stmt_depth(), p2.get_stmt_depth())) {
		SCH_MAT const* sm1 = POLY_sche(p1);
		SCH_MAT const* sm2 = POLY_sche(p2);
		for (UINT i = 0; i <= depth; i++) {
			if (sm1->get_stmt_order(i) != sm2->get_stmt_order(i)) {
				return false;
			}
		}
		return true;
	}
	return false;
}


//Return true if p1's lexicographical order less than p2 till 'depth'.
//'diff': record the depth that result in the difference.
bool POLY_TRAN::is_lex_lt(POLY const& p1, POLY const& p2, OUT INT * diff)
{
	INT depth = MIN(p1.get_stmt_depth(), p2.get_stmt_depth());
	SCH_MAT const* sm1 = POLY_sche(p1);
	SCH_MAT const* sm2 = POLY_sche(p2);
	for (INT i = 0; i <= depth; i++) {
		INT so_1 = sm1->get_stmt_order(i);
		INT so_2 = sm2->get_stmt_order(i);
		IS_TRUE0(so_1 >= 0 && so_2 >= 0);
		if (so_1 < so_2) {
			if (diff != NULL) { *diff = i; }
			return true;
		} else if (so_1 > so_2) {
			if (diff != NULL) { *diff = i; }
			return false;
		}
	}
	IS_TRUE0(&p1 == &p2);
	return false;
}


//Sort POLY within list in lexical order.
void POLY_TRAN::sort_in_lexical_order(IN OUT LIST<POLY*> & lst)
{
	LIST<POLY*> tlst;
	for (POLY * p = lst.get_head(); p != NULL; p = lst.get_next()) {
		C<POLY*> * tct;
		bool doit = false;
		for (POLY * t = tlst.get_head(&tct);
			 t != NULL; t = tlst.get_next(&tct)) {
			if (is_lex_lt(*p, *t)) {
				tlst.insert_before(p, tct);
				doit = true;
				break;
			}
		}
		if (!doit) {
			tlst.append_tail(p);
		}
	}
	lst.copy(tlst);
}
//END POLY_TRAN
