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
#include "comf.h"
#include "smempool.h"
#include "rational.h"
#include "flty.h"
#include "sstl.h"
#include "matt.h"
#include "bs.h"
#include "sgraph.h"
#include "xmat.h"
#include "depvecs.h"
#include "linsys.h"
#include "ldtran.h"

//
//START LOOP_TRAN
//
LOOP_TRAN::LOOP_TRAN(RMAT * m, INT rhs_idx)
{
	m_is_init = false;
	m_rhs_idx = -1;
	m_a = NULL;
	init(m, rhs_idx);
}


LOOP_TRAN::~LOOP_TRAN()
{
  	destroy();
}


void * LOOP_TRAN::xmalloc(ULONG size)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	void * p = smpool_malloc_h(size,m_pool);
	IS_TRUE0(p);
	memset(p,0,size);
	return p;
}


void LOOP_TRAN::init(RMAT * m, INT rhs_idx)
{
	if (m_is_init) return;
	m_pool = smpool_create_handle(16, MEM_COMM);
	if (m != NULL) {
		set_param(m, rhs_idx);
	}
	m_is_init = true;
}


void LOOP_TRAN::destroy()
{
	if (!m_is_init) return;
	m_a = NULL;
	m_rhs_idx = -1;
	smpool_free_handle(m_pool);
	m_pool = NULL;
	m_is_init = false;
}


//Set coeff matrix and index of start column of constant term.
void LOOP_TRAN::set_param(RMAT * m, INT rhs_idx)
{
	IS_TRUE(m && m->get_col_size() > 0, ("coeff mat is empty"));
	m_a = m;
	if (rhs_idx == -1) {
		m_rhs_idx = m->get_col_size() -1;
		return;
	}
	IS_TRUE(rhs_idx < (INT)m->get_col_size() && rhs_idx >= 1,
			("out of bound"));
	m_rhs_idx = rhs_idx;
}


/* Nonsingular Transformation Model is a framework that allows transformations
of loops using non-singular matrix based transformations of the iteration
space and loop bounds. This allows compositions of skewing, scaling,
interchange, and reversal transformations. These transformations are often
used to improve cache behavior or remove inner loop dependencies to allow
parallelization and vectorization to take place.
The function transform original loop bounds to new loop bounds.
Return true if transformation is unimodular, otherwise return false.

't': transforming matrix, must be nonsingular.
'stride': row vector, elements from first to last
	indicates new strides for each loop index variables.
	e.g: If the stride is [1,2,4,1], that means
	do i1... by 1
	  do i2 ... by 2
	    do i3 ... by 4
	      do i4 ... by 1
'idx_map': matrix(nvar,nvar), the relation between original
	index variable and new index variable.
	And following code generation will subject to the
	represetation of 'idx_map'.
	e.g: idx_map is [1, 2]
	                [0, -1]
			assuming that original index is (i,j),
			new index is (x, y), that will generated new mapping
			code and it should be inserted in original loop body:
				i = 1*x + 2*y;
				j = 0*x + -1*y;
				...
'aux_limits': New loop bound that represent limits of each loop
	index variable in auxiliary iteration space. Head node shows
	limits of outermost loop, tail node	shows the innermost.
'ofst': Offset vectors of new iteration space is corresponding to
	'auxiliary iteration space'. Since the first variable does not
	need offset, the first row will be zero. Each row indicates the
	relevant offset vector of loop index. So 'ofst' is low trapezoid
	matrix.

	e.g: u, v, w are loop indices of iter-space.
		x, y, z are loop indices of auxiliary iter-space.
		Assuming 'ofst' is 3*3 rational matrix as followed:
			[0, 0, 0]
			[-2, 0, 0]
			[2, 1/3, 0]
		That means the offset of u, v, w are:
			offset(u) = 0
			offset(v) = -2*u
			offset(w) = 2*u + (1/3)*v
'mul': If 't' is nonunimodular matrix, but nonsingular, loop scaling
	would be performed, auxiliary iteration space would be stretched.

	e.g: Given 'mul' is [2,3],  and loop limits of auxiliary iter-space is
					L<=u<=U
					f(u)<=v<=g(u),
		then new loop limits will be:
					2*L<=u<=2*U
					3*f(u)<=v<=3*g(u),
'trA': record the full-dimension transformed iteration space.

NOTICE:
	If 't' is not unimodular(nonsingular) matrix, new iteration
	space may include some points which not in original iteration
	space, we need to find the points within the limits that are
	in the lattice generated by 't', and the relevant 'stride' as
	well to keep the injection from points in new space to points
	in original space.
*/
bool LOOP_TRAN::tran_iter_space(IN RMAT & t,
								OUT RMAT & stride,
								OUT RMAT & idx_map,
								OUT LIST<RMAT*> & aux_limits,
								OUT RMAT & ofst,
								OUT RMAT & mul,
								OUT RMAT * trA)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	IS_TRUE(aux_limits.get_elem_count() == (UINT)m_rhs_idx,
					("unmatch coeff matrix info"));
	RMAT * A, tmpA, C, Ui, invt;
	if (trA != NULL) {
		A = trA;
	} else {
		A = &tmpA;
	}

	RATIONAL det = t.det();
	IS_TRUE(det != 0, ("T is singular!!"));
	UINT vars = m_rhs_idx; //number of variables
	IS_TRUE(vars == t.get_row_size(), ("loop nest only %d indices",vars));
	bool is_uni;
	if (t.abs(det) == 1) { //unimodular tran
		ofst.reinit(0,0);
		mul.reinit(0,0);
		/*
		Given A*i <= C, j = T*i, further in the new inequality derivable,
		that is	(A*T^(-1))*j <= C.
		Appling fme to new system of inequalities to generate target limit.
		*/
		t.inv(invt);
		//m_a->inner_col(A, 0, 0, m_a->get_row_size() - 1, m_rhs_idx - 1);
		m_a->inner_col(*A, 0, m_rhs_idx - 1);
		*A = *A * invt;

		INT i;
		//The stride of result loop limits always be one in unimodular tran.
		stride.reinit(1, m_rhs_idx);
		for (i = 0; i < m_rhs_idx; i++) {
			stride.set(0, i, 1);
		}
		m_a->inner(C, 0, m_rhs_idx,
					m_a->get_row_size() - 1,
					m_a->get_col_size() - 1);
		A->grow_col(C, 0, C.get_col_size() -1);

		//Computes new loop limits
		LINEQ lineq(A, m_rhs_idx);
		RMAT * newb = aux_limits.get_tail();
		RMAT res;

		//Eliminating each variable from inner most loop to outer loop,
		//except the outer most loop.
		for (i = m_rhs_idx - 1; i > 0; i--) {
			*newb = *A;
			if (!lineq.fme(i, res, false)) {
				IS_TRUE(0, ("system inconsistency!"));
			}
			*A = res;
			newb = aux_limits.get_prev();
			IS_TRUE(newb != NULL, ("miss buf to hold transformed "
									"boundary of dimension %d", i));
		}
		//Record outermost loop bound.
		*newb = *A;
		if (A == trA) {
			//return the transformed iteration space.
			*A = *aux_limits.get_tail();
		}
		aux_limits.get_tail();
		is_uni = true;
	} else { //Nonsingular trans
		RMAT H, Hi;
		INTMAT tmph,tmpu;
		INTMAT it; //HNF is one method of INTMAT.
		it.copy(t);
		it.hnf(tmph, tmpu); //tmph = it * tmpu
		Ui.copy(tmpu);
		H.copy(tmph);

		///for test
		{
			RMAT U;
			Ui.inv(U); // it = tmph * Ui;
			U = H * U;
			IS_TRUE(t==U, ("illegal inv"));
		}
		H.getdiag(stride);
		mul.copy(stride);
		H.inv(Hi);
		invt = Ui * Hi;
		#ifdef _DEBUG_
		RMAT invt,e(t.get_row_size(), t.get_col_size());
		e.eye(1);
		t.inv(invt);
		IS_TRUE(e==t*invt, ("illegal inv"));
		#endif

		//A*i <= C, k = U*i  => A*U^(-1)*k <= C
		m_a->inner(*A, 0, 0, m_a->get_row_size() - 1, m_rhs_idx - 1);
		*A = *A * Ui;

		//Compute loop limits for auxiliary iteration space.
		m_a->inner(C, 0,
					m_rhs_idx, m_a->get_row_size() - 1,
					m_a->get_col_size() - 1);
		A->grow_col(C, 0, C.get_col_size() -1);
		LINEQ lineq(A, m_rhs_idx);
		RMAT * newb = aux_limits.get_tail();
		INT i;

		//Eliminating each variable from inner most loop to outer loop,
		//except the outer most loop.
		for (i = m_rhs_idx - 1; i > 0; i--) {
			*newb = *A;
			RMAT res;
			if (!lineq.fme(i, res, false)) {
				IS_TRUE(0, ("system inconsistency!"));
			}
			*A = res;
			newb = aux_limits.get_prev();
		}

		//Record outermost loop bound.
		*newb = *A;
		if (A == trA) {
			//return the transformed iteration space.
			*A = *aux_limits.get_tail();
		}

		/*
		J = H*K => K = H^(-1)*J
		In the sake of H is hnf, H^(-1) also be low triangular, hence,
		k1 = hi1*J, k2 = hi2 * J, k3 = hi3 * J, ...,
		where hi indicate row of H^(-1), it means that we can replace kp by
		H^(-1)[p]*J, the result as following:
			A * U^(-1) * K <= C
		becomes
			K = H^(-1) * J
		*/
		ofst.reinit(1, vars); //Ofst of first var is zero.
		ofst.set_row(0, (RATIONAL)0);
		for (i = 1; i < (INT)vars; i++) {
			//Backward subsititutes new index variable for orig index variable.
			RMAT newofst;
			for (UINT j = 0; j < (UINT)i; j++) {
				RATIONAL t = H.get(i, j);
				RMAT hirow;
				Hi.inner_row(hirow, j, j);
				hirow.mul(t);
				if (j == 0)  {
					newofst.grow_row(hirow);
				} else {
					//'newofst' always be vector.
					newofst.add_row_to_row(hirow, 0, 0);
				}
			}
			ofst.grow_row(newofst);
		}
		is_uni = false;
	} //end else
	if (idx_map.size() > 0) {
		IS_TRUE0(idx_map.get_col_size() == invt.get_col_size());
		idx_map = idx_map * invt;
	} else {
		idx_map.copy(invt);
	}
	return is_uni;
}


/* Generate loop trans matrix, and return true if success.
Using delta-multiplier.

't': loop transforming matrix generated.
'dvec': dependence vector matrix.

NOTICE:
	This function generates transforming matrix in order to
	parallel innermost loop of DO loop nest.
	ONLY supports distance dependence so far. */
bool LOOP_TRAN::parallel_inner_loops(OUT RMAT & t,
									IN DVECS const& dvec,
									UINT dep_level, UINT option)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	IS_TRUE(dep_level < dvec.get_row_size(), ("out of rowsize"));
	if (!fully_permutable(t, dvec)) {
		return false;
	}
	IS_TRUE(is_fully_permutable(t * dvec), ("illegal func"));
	if (is_innermost_loop_parallelizable(t * dvec)) {
		return true;
	}
	/* Premultiplication by matrix DELTA to make all of outermost dep
	entries(first row) positive, or each of column elements should be zero.
	CASE:Given dvec as:
			[0, 1, 0]
			[0, -2, 0]
			[0, 3, 4]
		The first dependent vector only has zero entry.
	*/
	if (ONLY_HAVE_FLAG(option, OP_DELTA)) { //Premultipling delta.
		RMAT delta(t.get_row_size(), t.get_col_size());
		delta.eye(1);
		delta.set_row(dep_level, 1);
		t = delta * t;
		return true;
	} else if (ONLY_HAVE_FLAG(option, OP_PERM)) { //Permuation
		RMAT perm(t.get_row_size(), t.get_col_size());
		perm.eye(1);
		INT cand_row = dvec.get_row_size() - 1;

		/* Interchange as many as zero row to inner to obtain maximum inner
		loop parallism. */
		for (UINT i = 0; i < dvec.get_row_size(); i++) {
			if (i >= (UINT)cand_row) {
				break;
			}

			//Find zero row to interchange
			if (dvec.is_rowequ(i, DD(0))) {
				perm.interch_row(i, cand_row);
				cand_row--;
			}
		}

		//Not any of row be interchanged.
		if (cand_row == (INT)dvec.get_row_size() - 1) {
			return false;
		}
		t = perm * t;
		return true;
	} else {
		//Attempt to find innermost parallism by applying  permuation and
		//delta transformation.
		RMAT perm(t.get_row_size(), t.get_col_size());
		perm.eye(1);

		/* First try to permutate.
		Interchange as many as zero row to inner to obtain maximum inner
		loop parallism. */
		INT cand_perm_row = dvec.get_row_size() - 1;
		for (UINT i = 0; i < dvec.get_row_size(); i++) {
			if (i >= (UINT)cand_perm_row) {
				break;
			}

			//Find zero row to interchange
			if (dvec.is_rowequ(i, DD(0))) {
				perm.interch_row(i, cand_perm_row);
				cand_perm_row--;
			}
		}

		//Not any of row be interchanged. Try DELTA transformation.
		if (cand_perm_row == (INT)dvec.get_row_size() - 1) {
			//Build DELTA mulplifier.
			perm.set_row(dep_level, 1);
		}
		t = perm * t;
		return true;
	}
	return false;
}


/* Generating transforming matrix to parallel outer loops.
Maximum degree of parallelism of outer loops could be
'dvec.rowsize - rank(dvec)'.

't': nonsingular transforming matrix.
'd': dependence matrix, that uses column convention.
	Each column represented dependence vector.

The method generates trans-matrix that reducing the rows of 'd' be zero as
much as possible.
	e.g: Given nested loops as:
		for L1
		  for L2
		    for L3
	Pretending dependence matrix d(3*4) whose rank is 1 as follwing:
			[a1,b1,c1,d1] //for L1
			[a2,b2,c2,d2] //for L2
			[a3,b3,c3,d3] //for L3
	after transformation, the new depdence matrix could be
			[0,0,0,0] //for L1
			[0,0,0,0] //for L2
			[w,x,y,z] //for L3
	That illustates two outer of loops L1, L2 are parallelled.

NOTICE:
	The case that only can be handled is that 'dvec' is singular!
	This function also can be used to transform loop nest to gain the
	most spacial locality since all dependencies are represented by
	inner loops. */
bool LOOP_TRAN::parallel_outer_loops(OUT RMAT & t, IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	UINT i;
	//1. Fully permutability. 'dvec' should be column convention.
	if (!fully_permutable(t, dvec)) {
		return false;
	}
	DVECS tdvec = t * dvec;
	IS_TRUE(is_fully_permutable(tdvec), ("illegal func"));
	RMAT d;
	if (!tdvec.cvt_to(d)) {
		return false;
	}
	if (d.rank() == d.get_row_size()) {
		return false;
	}

	/* 2. Computs null space of trans(d) that be row convention.
	Each column of 'x' with nonzero elements represents a basis of null
	space of 'd'. */
	d.trans();
	RMAT x;
	d.null(x);

	//For test
	//RMAT d2;
	//d2 = d * x; //Dx=0
	//

	//3. Extracting columns with nonzero elements.
	RMAT tt;
	for (i = 0; i < x.get_col_size(); i++) {
		if (!x.is_colequ(i, 0)) {
			RMAT tmp;
			x.inner_col(tmp, i, i);
			tt.grow_row(tmp);
		}
	}
	tt.intliz(); //Scaling rational number to integer.

	//For test
	//tt.trans();
	//d2 = d * tt;
	//tt.trans();
	//

	// 4. Completion to make trans-matrix nonsingluar.
	//	'tt' must be row convention.	
	tt.padding();

	//5. Permuting rows with only zero ones to prior.
	RMAT perm;
	d.trans();

	//Transforming 'd' that outer loop deps being zero.
	RMAT trd = tt * d;
	if (perm_out_zero_rows(perm, trd)) {
		tt = perm * tt;
	}
	t = tt * t;
	return true;
}


//Paralleling outer and inner loops as much as possible.
//Algorithm to maximize degrees of parallelism.
bool LOOP_TRAN::parallel_most_loops(OUT RMAT & t, IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	UINT dep_level = 0;
	DVECS const * pdvec = &dvec;
	DVECS tdvec; //'tdvec' for temp use
	bool res = false;
	if (parallel_outer_loops(t, dvec)) {
		res = true;
		tdvec = t * dvec;
		pdvec = &tdvec;

		RMAT rd;
 		tdvec.cvt_to(rd);
		dep_level = dvec.get_row_size() - rd.rank();
	}

	if (res == false) {
		t.reinit(dvec.get_row_size(), dvec.get_row_size());
		t.eye(1);
	}

	//Parallel inner nested loop
	RMAT t2;
	if (parallel_inner_loops(t2, *pdvec, dep_level)) {
		res = true;
	}
	if (res == true) {
		t = t2 * t;
	}
	return res;
}


/* Generating transforming matrix in order to permute zero row out from
inner.
	e.g: Given row vector matrix:
			[2,0,0]
			[0,0,0]
			[0,1,1]
		t * m will be:
			[0,0,0]
			[2,0,0]
			[0,1,1]
Return true if permutation is necessary, otherwise return false.

't': matrix that right by 'm' in order to permute zero dep level from the
	inside out.
'm': dependence matrix, that columns indicate depedence vector.
*/
bool LOOP_TRAN::perm_out_zero_rows(OUT RMAT & t, IN RMAT const& m)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	BMAT zerorow(m.get_row_size(), 1); //column vector
	UINT i,j;
	bool has_nonzero = false;
	for (i = 0; i < m.get_row_size(); i++) {
		if (m.is_rowequ(i, 0)) {
			zerorow.set(i, 0, true);
		} else {
			has_nonzero = true;
		}
	}
	if (!has_nonzero) {
		//All elements be zero.
		return false;
	}

	t.reinit(m.get_row_size(), m.get_row_size());
	t.eye(1);

	//Bubble sorting like method
	bool is_swap = false;
	for (i = 0; i < zerorow.get_row_size() - 1; i++) {
		bool do_perm = false;
		if (zerorow.get(i, 0)) {
			continue;
		}
		UINT tmpi = i;
		//row tmpi has nonzero elements.
		for (j = i + 1; j < zerorow.get_row_size(); j++) {
			if (!zerorow.get(j, 0)) {
				continue;
			}

			/*
			Elements of  row j all be zero.
			Do permtation between tmpi and j.
			*/
			t.interch_row(tmpi, j);
			zerorow.interch_row(tmpi, j);
			tmpi = j;
			do_perm = true;
		}
		if (!do_perm) {
			goto FIN;
		}
		is_swap = true;
	}
FIN:
	return is_swap;
}


/* Generate matrix to perform fully permutable transformation.
Return true if the transforming matrix has found, otherwise return false.

'dvec': dependence matrix, each column indicates dependence vector, and
	each row represents nested loops.
't': transforming matrix generated.

NOTICE:
	'dvec' use column convention. */
bool LOOP_TRAN::fully_permutable(OUT RMAT & t, IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	UINT i,j,k;
	t.reinit(dvec.get_row_size(), dvec.get_row_size());
	if (is_fully_permutable(dvec)) {
		t.eye(1);
		return true;
	}

	bool first = true;
	bool change = false;
	RMAT *pt = &t;
	RMAT tmpres; //Accumulating transforming matrix has generated.
	DVECS const* pdvec = &dvec;
	DVECS tmpt;
AGAIN:
	pt->eye(1);
	for (i = 0; i < pdvec->get_row_size(); i++) {
		for (j = 0; j < pdvec->get_col_size(); j++) {
			DD dd_inner_loop = pdvec->get(i,j);
			if (dd_inner_loop.dir == DT_NEG || dd_inner_loop.dir == DT_MISC) {
				//Cannot handle these case.
				t.reinit(0,0);
				return false;
			}

			//Attempting work out skewing factor to make 'dd' is positive.
			//At the present method, we can only handle constant elements.
			if (dd_inner_loop.dir == DT_DIS && dd_inner_loop.dis < 0) {
				bool done = false;
				for (k = 0; k < i; k++) {
					DD dd_outer_loop = pdvec->get(k,j);

					/*
					CASE1. Outer loop dependence is constant distance
					Computs factor = Ceil( abs(inner's distance) ,
									       outer's distance ),
					to make inner distance nonnegative.
					*/
					if (dd_outer_loop.dir == DT_DIS) {
						IS_TRUE(dd_outer_loop.dis >= 0,
								("miss one negative candidate"));
						if (dd_outer_loop.dis > 0) {
							INT factor = xceiling(-dd_inner_loop.dis,
													dd_outer_loop.dis);

							pt->set(i, k, MAX(t.getr(i, k), factor));
							done = true;
							break;
						} else {
							//dis may be zero!
						}
					}

					/* CASE2. Outer loop dependence is positive
					direction, assuming that the least distance
					is d(d>0), then outer direction is '>=d'.
					Although it is not constant distance, the
					skewing factor is computed by d.
					e.g: [>=1, -2] */
					if (dd_outer_loop.dir == DT_POS && dd_outer_loop.dis > 0) {
						INT factor = xceiling(-dd_inner_loop.dis,
											  dd_outer_loop.dis);
						if ((factor * dd_outer_loop.dis + dd_inner_loop.dis)
							== 0) {
							/* Here we are preferred to generate factor that
							make inner loop dependence positive, 
							scince positive direction may privode an 
							opportunity of computing nonnegative entry 
							for succedent negative elements. */
							factor++;
						}
						pt->set(i, k, MAX(t.getr(i, k), factor));
						done = true;
						break;
					}
				}
				if (!done) {
					//Could not find a skewing factor to skew this dependence
					//to positive or zero.
					t.reinit(0,0);
					return false;
				}
				change = true;
			}//end if
		}//end for
	}//end for

	bool neg_dis = false;

	if (false == change) {
		goto FIN;
	}
	
	//Generate new temporal Dependent Vectors Matrix.
	tmpt = *pt * *pdvec;

	//Checking for the product of T*D if there are new negative distant entries.
	for (i = 0; i < tmpt.get_row_size(); i++) {
		for (j = 0; j < tmpt.get_col_size(); j++) {
			DD dd = tmpt.get(i,j);
			if (dd.dir == DT_NEG ||	dd.dir == DT_MISC) {
				//Cannot handle these case.
				t.reinit(0,0);
				return false;
			}
			if (dd.dir == DT_DIS && dd.dis < 0) {
				neg_dis = true;
				goto OUT_OF_LOOP;
			}
		}//end for
	}//end for
	
OUT_OF_LOOP:
	if (neg_dis) {
		/* We need do processing iteratively. Method applied:
			res = E;
			AGAIN:
			Computs T from D;
			D = T*D;
			res = T * res;
			if (D has negative dis)
				goto AGAIN;
			T = res;
			return T
		*/
		neg_dis = false;
		pdvec = &tmpt;
		if (first) {
			first = false;
			tmpres.reinit(dvec.get_row_size(), dvec.get_row_size());
			pt = &tmpres;
		} else {
			t = *pt * t;
		}
		goto AGAIN;
	}
FIN:
	if (pt != &t) {
		t = *pt * t;
	}
	return true;
}


/*
Return true if all elements are greater than or equals 0.

'dvec': dependence matrix, each column indicate dependence vector.
*/
bool LOOP_TRAN::is_fully_permutable(IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	UINT i,j;
	for (i = 0; i < dvec.get_row_size(); i++) {
		for (j = 0; j < dvec.get_col_size(); j++) {
			DD dd = dvec.get(i,j);
			if (!((dd.dir == DT_DIS && dd.dis >= 0) || dd.dir == DT_POS)) {
				return false;
			}
		}//end for
	}//end for
	return true;
}


//Check dependence vectors if innermost loop parallelizable.
bool LOOP_TRAN::is_innermost_loop_parallelizable(IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	INT i,j;
	for (j = 0; j < (INT)dvec.get_col_size(); j++) {
		DD dd = dvec.get(dvec.get_row_size() - 1,j);
		if (dd.dir == DT_DIS && dd.dis == 0) {
			continue;
		}
		INT dep_level = dvec.get_row_size() - 1;
		for (i = dvec.get_row_size()- 2; i >= 0; i--) {
			DD dd = dvec.get(i,j);
			if ((dd.dir == DT_DIS && dd.dis > 0) ||
				(dd.dir == DT_POS && dd.dis > 0)) {
				dep_level = i;
				break;
			}
		}//end for
		if (dep_level == (INT)dvec.get_row_size() - 1) {
			return false;
		}
	}//end for
	return true;
}


/*
Return true if dependence matrix is legal in which elements is
lexicographically positive.

'dvec': dependence matrix, each column indicate dependence vector.
*/
bool LOOP_TRAN::is_legal(IN DVECS const& dvec)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	UINT i,j;
	for (j = 0; j < dvec.get_col_size(); j++) {
		for (i = 0; i < dvec.get_row_size(); i++) {
			DD dd = dvec.get(i,j);
			if ((dd.dir == DT_DIS && dd.dis < 0) ||
				 dd.dir == DT_NEG ||
				 dd.dir == DT_MISC) {
				return false;
			}
			if ((dd.dir == DT_DIS && dd.dis > 0) ||
				 dd.dir == DT_POS) {
				break;
			}
		}//end for
	}//end for
	return true;
}
//END LOOP_TRAN



//
//START Generate C Code
//
GEN_C::GEN_C(RMAT * m, INT rhs_idx)
{
	m_is_init = false;
	m_rhs_idx = -1;
	m_a = NULL;
	init(m, rhs_idx);
}


GEN_C::~GEN_C()
{
  	destroy();
}


void * GEN_C::xmalloc(ULONG size)
{
	IS_TRUE(m_is_init == true, ("not yet initialized."));
	void * p = smpool_malloc_h(size,m_pool);
	IS_TRUE0(p);
	memset(p,0,size);
	return p;
}


void GEN_C::init(RMAT * m, INT rhs_idx)
{
	if (m_is_init) return;
	m_pool = smpool_create_handle(16, MEM_COMM);

	///
	m_cst_sym = NULL;
	m_var_sym = NULL;
	m_org_sym = NULL;
	if (m != NULL) {
		set_param(m, rhs_idx);
	}
	///

	m_is_init = true;
}


void GEN_C::destroy()
{
	if (!m_is_init) return;

	///
	m_a = NULL;
	m_rhs_idx = -1;
	m_cst_sym = NULL;
	m_var_sym = NULL;
	m_org_sym = NULL;
	///

	smpool_free_handle(m_pool);
	m_pool = NULL;
	m_is_init = false;
}


/*
Set coeff matrix and index of start column of constant term.
*/
void GEN_C::set_param(RMAT * m, INT rhs_idx)
{
	IS_TRUE(m && m->get_col_size() > 0, ("coeff mat is empty"));
	m_a = m;
	if (rhs_idx == -1) {
		m_rhs_idx = m->get_col_size() -1;
		return;
	}
	IS_TRUE(rhs_idx < (INT)m->get_col_size() && rhs_idx >= 1,
			("out of bound"));
	m_rhs_idx = rhs_idx;
}


//Set customised symbol for symbolic constant-variable and general variable.
void GEN_C::set_sym(CHAR ** tgtvar_sym,
					CHAR ** orgvar_sym,
					CHAR ** cst_sym)
{
	m_cst_sym = cst_sym;
	m_var_sym = tgtvar_sym;
	m_org_sym = orgvar_sym;
}


/*
Prints placeholer into buf.
*/
void GEN_C::gen_ppl(OUT CHAR sbuf[], INT num)
{
	for (INT k = 0; k < num; k++) {
		xstrcat(sbuf, m_sbufl, "    ");
	}
}


CHAR * GEN_C::get_orgvar_sym(OUT CHAR * sbuf, INT varid)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (m_org_sym != NULL && m_org_sym[varid] != NULL) {
		sprintf(sbuf, "%s", m_org_sym[varid]);
	} else {
		sprintf(sbuf, "%s%d", ORG_VAR_PREFIX, varid);
	}
	return sbuf;
}


CHAR * GEN_C::get_cst_sym(OUT CHAR * sbuf, INT cstid)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (m_cst_sym != NULL && m_cst_sym[cstid] != NULL) {
		sprintf(sbuf, "%s", m_cst_sym[cstid]);
	} else {
		sprintf(sbuf, "%s%d", CST_SYM_PREFIX, cstid);
	}
	return sbuf;
}


CHAR * GEN_C::get_newvar_sym(OUT CHAR * sbuf, INT varid)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (m_var_sym != NULL && m_var_sym[varid] != NULL) {
		sprintf(sbuf, "%s", m_var_sym[varid]);
	} else {
		sprintf(sbuf, "%s%d", TGT_VAR_PREFIX, varid);
	}
	return sbuf;
}


/*
Generate linear expression
'is_lb': it is true was said that the expression contained in lower bound,
	or false is in the upper bound.
'num_sc': the number of symbolic constants
'sym_start_cl': the start column of constant symbol in right hand
	side of expression.
	Given i < 1 + 2*M + 3*N
	First column indicate the unknown 'i', second column indicate
	constant value, namely the literal '1'. So the column of constant
	symbol start is the third one.
*/
void GEN_C::genlinexp(OUT CHAR sbuf[], IN RMAT & coeff_vec, INT ivar,
					INT comden, bool is_lb, UINT sym_start_cl, UINT num_sc)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	CHAR tmpbuf[TMP_BUF_LEN];

	//Constant value column
	bool hasv = false;
	INT n = coeff_vec.get(0, 1).num();
	if (is_lb) {
		//expression is : -i <= -10 + ..., the output will be
		//i >= 10 - ...
		n = -n;
	}
	if (n != 0) {
		xstrcat(sbuf, m_sbufl, "%d", n);
		hasv = true;
	} else {
		//Not has any of constant value
	}

	//Prints others loop index variable name.
	for (UINT j = sym_start_cl; j < coeff_vec.get_col_size(); j++) {
		IS_TRUE(comden == coeff_vec.get(0, j).den(),
				("should be reduced to common denominator at first"));
		INT coeff = coeff_vec.get(0, j).num();
		if (coeff == 0) {
			continue;
		}

		if (is_lb) {
			//expression is : -i <= -10 + -M + ..., the output will be
			//i >= 10 + M - ...
			coeff = -coeff;
		}

		//Choose symbol to print
		CHAR * sym = NULL;
		if (num_sc > 0 && j >= sym_start_cl && j < sym_start_cl + num_sc) {
			//Prints symbolic constant
			sym = get_cst_sym(tmpbuf, j - sym_start_cl);
		} else {
			//Prints symbol of other index variables
			INT tmpj = j - (sym_start_cl + num_sc);
			IS_TRUE0(tmpj < m_rhs_idx);
			if (tmpj != ivar) {
				sym = get_newvar_sym(tmpbuf, tmpj);
			} else {
				sym = get_newvar_sym(tmpbuf, tmpj + 1);
			}
		}
		//

		if (hasv) {
			xstrcat(sbuf, m_sbufl, "+");
		}

		if (coeff == 1) {
			xstrcat(sbuf, m_sbufl, "%s", sym);
		} else if (coeff == -1) {
			xstrcat(sbuf, m_sbufl, "(-%s)", sym);
		} else {
			xstrcat(sbuf, m_sbufl, "(%d*%s)", coeff, sym);
		}
		hasv = true;
	}//end for

	/*
	CASE: bound is zero!
		e.g: Given upper bound is [1 0 1 -1], variable index is 2,
			and there are 3 loop index variable x0,x1,x2,
			the upper bound will be x2 <= 0 + x0 - x1

			If all elements of the row 'ub' be zero, that means
			the upper bound is zero.
	*/
	if (!hasv) {
		xstrcat(sbuf, m_sbufl, "0 ");
	}
}


void GEN_C::genub(OUT CHAR sbuf[], IN RMAT * limits, INT ub, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	IS_TRUE(m_a && m_rhs_idx >= 0, ("not yet initialized"));

	/*
	Given i < 1 + 2*M + 3*N
	First column indicate the unknown 'i', second column indicate
	constant value, namely the '1'. So the column of constant
	symbol start is the third one.
	*/
	UINT sym_start_cl = 2;

	//The number of symbolic constants
	UINT sc_count = 0;
	if (m_rhs_idx != (INT)m_a->get_col_size() - 1) {
		sc_count = m_a->get_col_size() - m_rhs_idx - 1;
	}

	INT comden = limits->get(ub, sym_start_cl).den();
	IS_TRUE(comden > 0, ("denominator must larger than zero"));
	if (comden != 1) {
		xstrcat(sbuf, m_sbufl, "%s(", TGT_FLOOR);
	}

	RMAT coeff_vec;
	limits->inner_row(coeff_vec, ub, ub);
	genlinexp(sbuf, coeff_vec, ivar, comden, false, sym_start_cl, sc_count);

	if (comden != 1) {
		xstrcat(sbuf, m_sbufl, ", %d) ", comden);
	}
}


/*
Prints low bound of loop index variable 'ivar'.

'limits': represent loop limit.
'lb': row index of loop limit, and that row describing low bound.
	e.g:
		[-1 0] means -x <= 0
'ivar': variable index
*/
void GEN_C::genlb(OUT CHAR sbuf[], IN RMAT * limits, INT lb, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	IS_TRUE(m_a && m_rhs_idx >= 0, ("not yet initialized"));

	/*
	Given i < 1 + 2*M + 3*N
	First column indicate the unknown 'i', second column indicate
	constant value, namely the '1'. So the column of constant
	symbol start is the third one.
	*/
	UINT sym_start_cl = 2;

	//The number of symbolic constants
	UINT sc_count = 0;
	if (m_rhs_idx != (INT)m_a->get_col_size() - 1) {
		sc_count = m_a->get_col_size() - m_rhs_idx - 1;
	}

	INT comden = limits->get(lb, sym_start_cl).den();
	IS_TRUE(comden > 0, ("denominator must larger than zero"));
	if (comden != 1) {
		//Generate CEIL operation. Constant value is rational.
		xstrcat(sbuf, m_sbufl, "%s(", TGT_CEIL);
	}

	RMAT coeff_vec;
	limits->inner_row(coeff_vec, lb, lb);
	genlinexp(sbuf, coeff_vec, ivar, comden, true, sym_start_cl, sc_count);

	if (comden != 1) {
		xstrcat(sbuf, m_sbufl, ", %d) ", comden);
	}
}


//Generate for max(a,b) that operation with two operands.
void GEN_C::genmin(OUT CHAR sbuf[], IN RMAT * limits,
					INT ub1, INT ub2, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	xstrcat(sbuf, m_sbufl, "min( ");
	genub(sbuf, limits, ub1, ivar);
	xstrcat(sbuf, m_sbufl, ", ");
	genub(sbuf, limits, ub2, ivar);
	xstrcat(sbuf, m_sbufl, " )");
}


//Generate for max(a,b) that operation with two operands.
void GEN_C::genmax(OUT CHAR sbuf[], IN RMAT * limits,
					INT lb1, INT lb2, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	xstrcat(sbuf, m_sbufl, "max( ");
	genlb(sbuf, limits, lb1, ivar);
	xstrcat(sbuf, m_sbufl, ", ");
	genlb(sbuf, limits, lb2, ivar);
	xstrcat(sbuf, m_sbufl, " )");
}


//Generate for max(a,b,c...) that operation with multiple operands.
void GEN_C::genmaxs(OUT CHAR sbuf[], IN RMAT * limits,
					INT lbnum,	INT * lb, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (lbnum > 2) {
		CHAR locbuf[MAX_LOC_BUF_LEN];
		locbuf[0] = 0;

		genmaxs(locbuf, limits, lbnum-1, lb+1, ivar);
		IS_TRUE(strlen(locbuf)<=MAX_LOC_BUF_LEN, ("overflow"));
		xstrcat(sbuf, m_sbufl, "max( ");

		genlb(sbuf, limits, lb[0], ivar);
		xstrcat(sbuf, m_sbufl, ", %s)", locbuf);
	} else {
		IS_TRUE(lbnum == 2, ("at least two elems"));
		genmax(sbuf, limits, lb[0], lb[1], ivar);
	}
}


//Generate for min(a,b,c...) that operation with multiple operands.
void GEN_C::genmins(OUT CHAR sbuf[], IN RMAT * limits,
							INT ubnum, INT * ub, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (ubnum > 2) {
		CHAR locbuf[MAX_LOC_BUF_LEN];
		locbuf[0] = 0;

		genmins(locbuf, limits, ubnum-1, ub+1, ivar);
		IS_TRUE(strlen(locbuf)<=MAX_LOC_BUF_LEN, ("overflow"));
		xstrcat(sbuf, m_sbufl, "min(");

		genub(sbuf, limits, ub[0], ivar);
		xstrcat(sbuf, m_sbufl, ", %s)", locbuf);
	} else {
		IS_TRUE(ubnum == 2, ("at least two elems"));
		genmin(sbuf, limits, ub[0], ub[1], ivar);
	}
}


//Generate offset of bound
bool GEN_C::genofst(OUT CHAR sbuf[], IN RMAT & ofst)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (ofst.size() == 0 || ofst.is_rowequ(0, 0)) {
		return false;
	}
	IS_TRUE(ofst.is_rowvec(),
			("should be only one-dimension for each of loop level"));
	CHAR tmpbuf[TMP_BUF_LEN];

	/*
	Common low denominator to reduce division
	e.g: Given expression is i + (3/2)*j + (1/2)*k, then transformed to
		(2*i + 3*j + k) / 2

	CASE: The method may incur integer overflow exception.
	e.g: i is a larger number, and 1/2*i + 1/30*j will be transformed to
		(15*i + j)/30, notes that 15*i may cause integer overflow but the
		old code is not.
	*/
	ofst.comden(0, 0);

	INT comden = ofst.get(0,0).den();
	IS_TRUE(comden > 0, ("unnormalized"));
	if (comden != 1) {
		xstrcat(sbuf, m_sbufl, "(");
	}

	bool hasv = false;
	for (UINT j = 0; j < ofst.get_col_size(); j++) {
		RATIONAL o = ofst.get(0, j);
		if (o == 0) {
			continue;
		}
		IS_TRUE(comden == o.den() && o.den() > 0, ("should be equal"));
		if (hasv) {
			xstrcat(sbuf, m_sbufl, "+");
		}

		if (o.num() == 1) {
			xstrcat(sbuf, m_sbufl, "%s", get_newvar_sym(tmpbuf, j));
		} else if (o.num() == -1) {
			xstrcat(sbuf, m_sbufl, "(-%s)", get_newvar_sym(tmpbuf, j));
		} else {
			xstrcat(sbuf, m_sbufl, "(%d*%s)", o.num(),
					get_newvar_sym(tmpbuf, j));
		}
		hasv = true;
	}

	if (comden != 1) {
		xstrcat(sbuf, m_sbufl, ")/%d", comden);
	}
	return hasv;
}


void GEN_C::genidxm(OUT CHAR sbuf[], IN RMAT & idx_map)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	if (idx_map.size() == 0) {
		return;
	}
	UINT i;
	CHAR tmpbuf[TMP_BUF_LEN];

	/*
	Common low denominator to reduce division
	e.g: Given expression is i + (3/2)*j + (1/2)*k, then transformed to
		(2*i + 3*j + k) / 2
	*/
	bool allzero = true;
	for (i = 0; i < idx_map.get_row_size(); i++) {
		idx_map.comden(i, 0);
		if (!idx_map.is_rowequ(i, 0)) {
			allzero = false;
		}
	}
	IS_TRUE(!allzero, ("idx mapping is NULL"));

	//Walk through each of level loop nest
	for (i = 0; i < idx_map.get_row_size(); i++) {
		if (idx_map.is_rowequ(i, 0)) {
			continue;
		}

		gen_ppl(sbuf, idx_map.get_row_size());

		xstrcat(sbuf, m_sbufl, "%s = ", get_orgvar_sym(tmpbuf, i));

		INT comden = idx_map.get(i,0).den();
		IS_TRUE(comden > 0, ("unnormalized"));
		if (comden != 1) {
			xstrcat(sbuf, m_sbufl, "(");
		}

		bool hasv = false;
		for (UINT j = 0; j < idx_map.get_col_size(); j++) {
			INT num = idx_map.get(i,j).num();
			if (num == 0) {
				continue;
			}
			IS_TRUE(comden == idx_map.get(i,j).den(), ("should be equal"));
			if (hasv) {
				xstrcat(sbuf, m_sbufl, "+");
			}

			if (num == 1) {
				xstrcat(sbuf, m_sbufl, "%s", get_newvar_sym(tmpbuf, j));
			} else if (num == -1) {
				xstrcat(sbuf, m_sbufl, "(-%s)", get_newvar_sym(tmpbuf, j));
			} else {
				xstrcat(sbuf, m_sbufl, "(%d*%s)", num,
						get_newvar_sym(tmpbuf, j));
			}

			hasv = true;
		}//for each of column
		if (comden != 1) {
			xstrcat(sbuf, m_sbufl, ")/%d", comden);
		}
		xstrcat(sbuf, m_sbufl, ";\n");
	}
}


//Generate low bound
void GEN_C::gen_loop_start(OUT CHAR sbuf[], INT stride,
						IN RMAT * limits, IN RMAT & ofst, INT mul, INT ivar,
						INT * lb, INT lbnum)
{
	//Generate ofst of low bound
	if (genofst(sbuf, ofst) != false) {
		xstrcat(sbuf, m_sbufl, " + ");
	}

	//Generate multiple of low bound of aux-limit
	if (mul != 1) {
		IS_TRUE(mul > 0, ("illegal mul"));
		xstrcat(sbuf, m_sbufl, "%d*(", mul);
	}

	if (lbnum > 1) { //low bound need max operations
		genmaxs(sbuf, limits, lbnum, lb, ivar);
	} else {
		genlb(sbuf, limits, lb[0], ivar);
	}

	if (mul != 1) {
		xstrcat(sbuf, m_sbufl, ")");
	}
}


//Generate uppper bound
void GEN_C::gen_loop_end(OUT CHAR sbuf[], INT stride,
						IN RMAT * limits, IN RMAT & ofst, INT mul, INT ivar,
						INT * ub, INT ubnum)
{
	CHAR tmpbuf[TMP_BUF_LEN];
	xstrcat(sbuf, m_sbufl, "; %s <= ", get_newvar_sym(tmpbuf, ivar));

	//Generate ofst of upper bound
	if (genofst(sbuf, ofst) != false) {
		xstrcat(sbuf, m_sbufl, " + ");
	}

	//Generate multiple of upper bound of aux-limit
	if (mul != 1) {
		xstrcat(sbuf, m_sbufl, "%d*(", mul);
	}

	if (ubnum > 1) { //upper bound need min operations
		genmins(sbuf, limits, ubnum, ub, ivar);
	} else {
		genub(sbuf, limits, ub[0], ivar);
	}

	if (mul != 1) {
		xstrcat(sbuf, m_sbufl, ")");
	}

}


//Generate loop step
void GEN_C::gen_loop_step(OUT CHAR sbuf[], INT stride, IN RMAT * limits,
							IN RMAT & ofst, INT mul, INT ivar)
{
	CHAR tmpbuf[TMP_BUF_LEN];
	IS_TRUE(stride >= 1, ("illegal stride"));
	if (stride == 1) {
		xstrcat(sbuf, m_sbufl, "; %s++", get_newvar_sym(tmpbuf, ivar));
	} else {
		xstrcat(sbuf, m_sbufl, "; %s+=%d",
				get_newvar_sym(tmpbuf, ivar), stride);
	}
	xstrcat(sbuf, m_sbufl, ")"); //end loop limit
}


//Generate loop limit of target iteration space.
void GEN_C::genlimit(OUT CHAR sbuf[], INT stride, IN RMAT * limits,
					IN RMAT & ofst, INT mul, INT ivar)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	CHAR var[256];
	get_newvar_sym(var, ivar);
	xstrcat(sbuf, m_sbufl, "for (%s = ", var); //start of loop
	INT lb[256], lbnum = 0;
	INT ub[256], ubnum = 0;

	//Record number of inequations of low and upper bound.
	for (UINT i = 0; i < limits->get_row_size(); i++) {
		if (limits->get(i, 0) == 1) {
			ub[ubnum++] = i;
		} else {
			IS_TRUE(limits->get(i, 0) == -1, ("unmatch info"));
			lb[lbnum++] = i;
		}
	}
	gen_loop_start(sbuf, stride, limits, ofst, mul, ivar, lb, lbnum);
	gen_loop_end(sbuf, stride, limits, ofst, mul, ivar, ub, ubnum);
	gen_loop_step(sbuf, stride, limits, ofst, mul, ivar);
}


/*
Prints out C codes

'stride','idx_map','limits',ofst','mul' see details in manual of
	tran_iter_space().
'name': file name to dump.
'is_del': creates new dump file
*/
void GEN_C::genlimits(IN LIST<RMAT*> & limits,
						IN RMAT * pstride,
						IN RMAT * pidx_map,
						IN RMAT * pofst,
						IN RMAT * pmul,
						IN CHAR * name,
						IN bool is_del)
{
	IS_TRUE(m_is_init == true, ("not yet initialized"));
	IS_TRUE(limits.get_elem_count() > 0, ("unmatch coeff matrix info"));
	static UINT g_count = 0;
	CHAR tmpbuf[TMP_BUF_LEN];
	bool is_uni = true;
	UINT const varnum = limits.get_elem_count();
	RMAT stride, idx_map, ofst, mul;
	if (pstride != NULL) {
		stride = *pstride;
	} else {
		stride.reinit(1, varnum);
		stride.set_all(1);
	}
	if (pidx_map != NULL) {
		idx_map = *pidx_map;
	}
	if (pofst != NULL) {
		ofst = *pofst;
	}
	if (pmul != NULL) {
		mul = *pmul;
	}

	if (mul.size() != 0) {
		is_uni = false;
		IS_TRUE(ofst.is_quad() && idx_map.is_quad(),
				("ofst and idx_map must be square"));
		IS_TRUE(varnum == mul.get_col_size() &&
				varnum == ofst.get_row_size() &&
				varnum == stride.get_col_size() &&
				varnum == idx_map.get_col_size(), ("unmatch matrix info"));
	}

	//Open a dump file for trace purpose
	if (name == NULL) {
		name = TGT_LP;
	}
	if (is_del) {
		unlink(name);
	}
	FILE * h = fopen(name, "a+");
	IS_TRUE(h, ("%s create failed!!!", name));
	fprintf(h, "\nTarget loop nest id:%u\n", g_count++);

	/*
	Print new loop index initializing code.
	That may be dispensible during
	code generation of compiler intermedia language.
	*/
	m_sbufl = 4096;
	m_sbuf = (CHAR*)::malloc(m_sbufl);
	sprintf(m_sbuf, "int ");
	for (UINT u = 0; u < varnum; u++) {
		xstrcat(m_sbuf, m_sbufl, "%s", get_newvar_sym(tmpbuf, u));
		if (u != varnum - 1) {
			xstrcat(m_sbuf, m_sbufl, ", ");
		}
	}
	fprintf(h, "%s;\n", m_sbuf);

	//Generate loop bound from outer most to inner loop.
	LINEQ lineq(NULL);
	INT ivar = 0;
	for (RMAT * ineq = limits.get_head();
		 ineq != NULL; ineq = limits.get_next(), ivar++) {
		if (ineq->size() == 0) {
			continue;
		}
		RMAT o;
		m_sbuf[0] = 0;
		gen_ppl(m_sbuf, ivar);
		lineq.set_param(ineq, m_rhs_idx);

		/*
		Format form of code such that it observe to engine require
		e.g original bound is i + j < 100, transformed to i < 100 + (-j)
		*/
		RMAT formed;
		lineq.format_bound(ivar, formed);

		//The condition is not meet if there is not ivar in ineqalities.
		if (formed.size() > 0) {
			if (ofst.size() != 0) {
				//What one needs to pay attention is that 'mul' may not be one
				//iff 'ofst' is zero.
				ofst.inner_row(o, ivar, ivar);
				IS_TRUE(stride.get(0, ivar).den() == 1 &&
						mul.get(0, ivar).den() == 1,
						("stride and mul is rational"));
				genlimit(m_sbuf, stride.get(0, ivar).num(), &formed, o,
						 mul.get(0, ivar).num(), ivar);
			} else {
				genlimit(m_sbuf, stride.get(0, ivar).num(), &formed, o, 1, ivar);
			}
			fprintf(h, "%s\n", m_sbuf);
		}
	}

	//Generate index mapping from new loop index to original ones.
	m_sbuf[0] = 0;
	genidxm(m_sbuf, idx_map);
	fprintf(h, "%s\n", m_sbuf);

	fprintf(h, "\n");
	fclose(h);
	::free(m_sbuf);
	m_sbuf = NULL;
	m_sbufl = 0;
}
//END Generate C Code

