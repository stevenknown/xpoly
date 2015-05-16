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
#ifndef __POLY_H_
#define __POLY_H_
class POLY;
class ACC_MAT;
class DEP_POLY;
class DPVEC;
class VC_MAT;
class DEP_POLY_HASH;
class DEP_POLY_MGR;


//
//START DEP_POLY
//
#define DEP_LOOP_CARRIED		1
#define DEP_LOOP_INDEP			2
#define DEP_POLY_id(d)			((d).id)
#define DEP_POLY_flag(d)		((d).flag)
#define DEP_POLY_rhs_idx(d)		((d).rhs_idx)
class DEP_POLY : public RMAT {
public:
	UINT id; //each dep-poly has an unique id.
	UINT flag; //record dependence-type: LOOP_CARRIED, LOOP_INDEPENDENT
	UINT rhs_idx;

	DEP_POLY()
	{
		id = 0;
		flag = 0;
		rhs_idx = 0;
	}

	DEP_POLY(UINT row, UINT col) : RMAT(row, col)
	{
		id = 0;
		flag = 0;
		rhs_idx = 0;
	}

	DEP_POLY(RMAT const& r, UINT rhs_idx) : RMAT(r)
	{
		id = 0;
		flag = 0;
		this->rhs_idx = rhs_idx;
	}

	~DEP_POLY() {}

	void copy(IN DEP_POLY const& dp);
	void copy(IN RMAT const& r, UINT rhs_idx);

	void dump();
	void dump(FILE * h, UINT indent);

	inline UINT get_from_iv_idx_start() const { return 0; }
	inline UINT get_to_iv_idx_start() const { return rhs_idx / 2; }
	inline UINT get_num_of_from_iv() const { return get_to_iv_idx_start(); }
	inline UINT get_num_of_to_iv() const { return get_num_of_from_iv(); }

	void intersect(IN RMAT const& r);
	void intersect(IN DEP_POLY const& dp);
	bool is_empty(bool keepit, VC_MAT const* vc);
	inline bool is_loop_carried() const
	{ return HAVE_FLAG(DEP_POLY_flag(*this), DEP_LOOP_CARRIED); }
	inline bool is_loop_indep() const
	{ return HAVE_FLAG(DEP_POLY_flag(*this), DEP_LOOP_INDEP); }

	void insert_loop_before(UINT iv_idx);
	void insert_local_var(OUT UINT * lv1_idx, OUT UINT * lv2_idx);

	void elim_aux_var(IN POLY const& from, IN POLY const& to);

	void remove_local_var();
	void remove_loop(UINT iv_idx);
};
//END DEP_POLY


class DEP_POLY_LIST : public LIST<DEP_POLY*> {
public:
	~DEP_POLY_LIST()
	{
		free_elem();
	}

	void free_elem()
	{
		for (DEP_POLY * p = get_head(); p != NULL; p = get_next()) {
			delete p;
		}
	}
	void intersect(IN DEP_POLY_LIST & dpl);
	bool is_intersect_empty(IN DEP_POLY_LIST & dpl);
	bool is_empty(bool keepit, VC_MAT const* vc);
};


#define DPVEC_from_id(d)		((d).from_acc_mat_id)
#define DPVEC_to_id(d)			((d).to_acc_mat_id)
class DPVEC : public SVECTOR<DEP_POLY_LIST*> {
public:
	UINT from_acc_mat_id;
	UINT to_acc_mat_id;

	DPVEC(UINT from_id, UINT to_id);
	~DPVEC();
	bool is_intersect_empty(DPVEC const& dpvec,
							bool is_cross_depth = false) const;
	void free_elem();
	void copy(DPVEC const& d);
	DEP_POLY_LIST * get_innermost() const;
	void dump(FILE * h, UINT indent);
	void dump();
};


#define REF_HASH_from_id(d)		((d).from_stmt_id)
#define REF_HASH_to_id(d)		((d).to_stmt_id)
#define MAKE_REF_ID(d)			(DPVEC_from_id(d) | DPVEC_to_id(d))

class DPVEC_HF {
public:
	UINT get_hash_value(DPVEC * d, UINT bucket_size) const
	{ return MAKE_REF_ID(*d) % bucket_size; }

	bool compare(DPVEC * d1, DPVEC * d2) const
	{
		return DPVEC_from_id(*d1) == DPVEC_from_id(*d2) &&
			   DPVEC_to_id(*d1) == DPVEC_to_id(*d2);
	}
};


class REF_HASH : public SHASH<DPVEC*, DPVEC_HF> {
public:
	UINT from_stmt_id;
	UINT to_stmt_id;

	REF_HASH(UINT from_id, UINT to_id)
	{
		from_stmt_id = from_id;
		to_stmt_id = to_id;
	}
	~REF_HASH() { free_elem(); }

	void free_elem()
	{
		INT c;
		for (DPVEC * d = get_first(c); d != NULL; d = get_next(c)) {
			delete d;
		}
	}
};


#define MAKE_STMT_ID(d)		(REF_HASH_from_id(d) | REF_HASH_to_id(d))

class REF_HASH_HF {
public:
	UINT get_hash_value(REF_HASH * d, UINT bucket_size) const
	{ return MAKE_STMT_ID(*d) % bucket_size; }

	bool compare(REF_HASH * d1, REF_HASH * d2) const
	{
		return REF_HASH_from_id(*d1) == REF_HASH_from_id(*d2) &&
			   REF_HASH_to_id(*d1) == REF_HASH_to_id(*d2);
	}
};


class STMT_HASH : public SHASH<REF_HASH*, REF_HASH_HF> {
public:
	~STMT_HASH() { free_elem();	}
	void free_elem()
	{
		INT c;
		for (REF_HASH * r = get_first(c); r != NULL; r = get_next(c)) {
			delete r;
		}
	}
};


class DEP_POLY_HASH : public STMT_HASH {
public:
	void clean()
	{
		free_elem();
		STMT_HASH::clean();
	}

	DPVEC * find(POLY const& from, POLY const& to,
				 ACC_MAT const& am1, ACC_MAT const& am2);
	DPVEC * append(POLY const& from, POLY const& to,
				   ACC_MAT const& am1, ACC_MAT const& am2);
};


//
//START DEP_POLY_MGR
//
class DEP_POLY_MGR {
	DEP_POLY_HASH m_dh;
	void build_common_equation(POLY const& from, POLY const& to,
								INT depth, bool include_depth,
								OUT RMAT & res);
	void build_domain_exec_cond(POLY const& from, POLY const& to,
								OUT RMAT & res);
	void build_acc_exec_cond(POLY const& from, POLY const& to,
							ACC_MAT const& from_acc, ACC_MAT const& to_acc,
							OUT RMAT & res);
	void build_context_relation(POLY const& from, POLY const& to,
								OUT RMAT & res);
public:
	DEP_POLY_MGR();
	~DEP_POLY_MGR();
	void clean();

	DEP_POLY_LIST * conjoin(DEP_POLY const& c1,	DEP_POLY const& c2,
							VC_MAT const* vc);
	DPVEC * get_dpvec(POLY const& from, POLY const& to,
					ACC_MAT const& am1, ACC_MAT const& am2);

	void get_all_dep_poly(IN OUT LIST<DEP_POLY*> & lst);
	void insert_local_var(OUT UINT * lv1_idx = NULL,
						OUT UINT * lv2_idx = NULL);
	void insert_loop_before(UINT iv_idx);
	void remove_loop(UINT iv_idx);
	void remove_local_var();
	void revise_neg_iv_cs(POLY const& from, POLY const& to,
						IN OUT DEP_POLY & cs);
	VC_MAT * build_vc(POLY const& from, POLY const& to, OUT VC_MAT & vc);
	void build_map_iv_coeff(POLY const& from, POLY const& to,
							OUT SVECTOR<INT> & coeff);
	void build_loop_independent(POLY const& from, POLY const& to,
								bool is_reverse, UINT depth,
								OUT RMAT & res);
	void build_loop_carried(POLY const& from, POLY const& to,
							bool is_reverse, UINT depth,
							OUT RMAT & res);
	void build_syn_order_relation(POLY const& from, POLY const& to,
								bool is_reverse, UINT depth,
								OUT RMAT & res);
	void build(POLY const& from, POLY const& to,
			   ACC_MAT const& from_acc, ACC_MAT const& to_acc,
			   VC_MAT const* vc, OUT DPVEC & dpvec,
			   bool is_reverse);
	DPVEC * build_dep_poly(POLY const& from, POLY const& to,
						ACC_MAT const& from_acc, ACC_MAT const& to_acc,
						VC_MAT const* vc, bool is_reverse);
	void build_dep_poly(POLY const& from, POLY const& to,
						ACC_MAT const& from_acc, ACC_MAT const& to_acc,
						VC_MAT const* vc, OUT DPVEC & dpvec,
						bool is_reverse);
	void dump(IN LIST<POLY*> & lst);
};
//END DEP_POLY_MGR



//
//START DG (Dependence Graph)
//
#define DGEINFO_dpvec(e)				((e)->dpvec)
#define DGEINFO_from_quasi_func(e)		((e)->from_quasi_func)
#define DGEINFO_to_quasi_func(e)		((e)->to_quasi_func)
class DGEINFO {
public:
	DPVEC const* dpvec;
	RMAT * from_quasi_func;
	RMAT * to_quasi_func;
	DGEINFO() { dpvec = NULL; from_quasi_func = NULL; to_quasi_func = NULL; }
};


//Dependence Graph.
class DG : public GRAPH {
protected:
	//True if one intends building graph at dependence analysis.
	bool m_is_build_graph;
	SVECTOR<RMAT*> m_sch_mat; //record schedule matrix for each POLY.
	DEP_POLY_MGR m_orig_dpmgr; //record original dependencn polyhedra.
	SMEM_POOL * m_pool;

	void * xmalloc(ULONG size)
	{
		IS_TRUE0(m_pool);
		void * p = smpool_malloc_h(size, m_pool);
		IS_TRUE0(p);
		memset(p, 0, size);
		return p;
	}
public:
	DG(IN LIST<POLY*> & lst, bool is_build_graph = false);
	virtual ~DG();
	virtual bool is_red_stmt(POLY const& p);
	virtual bool is_red_pair(POLY const& p1, POLY const& p2,
							 ACC_MAT const& am1, ACC_MAT const& am2);
	bool is_build_graph() const { return m_is_build_graph; }
	bool is_legal(IN LIST<POLY*> & lst);

	//Get the dependence polyhedron.
	DPVEC const* get_dep_poly(EDGE const* e) const;

	//Get the polyhedron correspond to v.
	POLY const* get_poly(VERTEX const* v) const;
	RMAT * get_from_quasi_func(IN EDGE const* e) const;
	RMAT * get_to_quasi_func(IN EDGE const* e) const;
	RMAT * get_sch_mat(IN POLY const* p);
	inline DEP_POLY_MGR * get_orig_dep_mgr() { return &m_orig_dpmgr; }

	void rebuild(IN LIST<POLY*> & lst, bool is_build_graph = false);

	void set_dep_poly(VERTEX const* from, VERTEX const* to, DPVEC const* dp);
	void set_dep_poly(IN EDGE * e, IN DPVEC const* dp);
	void set_poly(IN VERTEX * v, IN POLY * p);
	void set_from_quasi_func(IN EDGE * e, IN RMAT * quasi);
	void set_to_quasi_func(IN EDGE * e, IN RMAT * quasi);

	bool verify(IN LIST<POLY*> & lst, IN DEP_POLY_HASH & dh);
};
//END DG



//
//START ACC_MAT
//
/* The designation of artifical array which can be privatized.
  General_Reduction
  Close_Phi
  Cross_BB_scalar_dependence
  Commutative_Associative_Reduction */
#define ACC_MAT_id(a)			((a).id)
#define ACC_MAT_arr_id(a)		((a).array_base_id)
class ACC_MAT : public RMAT {
public:
	UINT id; //unique identifier
	UINT array_base_id;

	ACC_MAT() { id = 0; array_base_id = 0; }
	ACC_MAT(ACC_MAT const& a) : RMAT(a)
	{ id = a.id; array_base_id = a.array_base_id; }
	void insert_loop_before(UINT iv_idx);
	void insert_loop_after(UINT iv_idx);
	void surround_acc_by_loop();
	void remove_loop(UINT iv_idx);
	void dump(IN FILE * h, IN SVECTOR<CHAR*> & var_name,
			  POLY const& p, UINT indent);
};


//
//START ACC_MGR
//
class ACC_MGR {
protected:
	SVECTOR<ACC_MAT*> m_read_vec; //list to READ access matrix.
	SVECTOR<ACC_MAT*> m_write_vec; //list to WRITE access matrix.

	//Map from array-base-id to its entirely references.
	SVECTOR<LIST<ACC_MAT*>*> m_map_arr_base_id2refs;
public:
	ACC_MGR();
	~ACC_MGR();
	void clean_data();
	void clean();
	ACC_MAT * set_ref(IN ACC_MAT const& acc_mat, bool is_read);
	bool is_read(IN ACC_MAT const& acc_mat) const;
	bool is_write(IN ACC_MAT const& acc_mat) const;
	void insert_local_var(UINT rhs_idx);
	void insert_loop_before(UINT iv_idx);
	void insert_loop_after(UINT iv_idx);
	void surround_acc_by_loop();
	void remove_loop(UINT iv_idx);
	LIST<ACC_MAT*> * map_arr_id2refs(UINT arr_id);
	INT get_max_arr_base_id() const
	{ return m_map_arr_base_id2refs.get_last_idx(); }
	void get_read_refs(OUT LIST<ACC_MAT*> & lst) const;
	void get_write_refs(OUT LIST<ACC_MAT*> & lst) const;
	UINT map_ref2arr_id(ACC_MAT const* acc_mat) const;
	void privatize(UINT iv_idx);
	void dump(FILE * h, SVECTOR<CHAR*> & var_name, POLY const& p);
	void copy(ACC_MGR const& am);
};
//END ACC_MGR


class VC_MAT : public INTMAT {
public:
	void interchange(UINT d1, UINT d2)
	{
		interch_row(d1, d2);
	}

	void reverse(UINT d, UINT iv_idx)
	{
		set(d, iv_idx, -get(d, iv_idx));
	}

	INT get_val(UINT depth, UINT iv_idx) const
	{
		IS_TRUE0(depth >= 1 && iv_idx < get_col_size());
		return get(depth, iv_idx);
	}
};


//
//START SCH_MAT
//
//Before any polyhedral transformations,
//A is identity, ¦£ is 0, and ¦Â is vector.
class SCH_MAT : public RMAT {
protected:
	/*
	Record iv_idx for each depth level.
	*/
	VC_MAT m_map_iv; //rows indicate depth, cols indicate iv_idx.

	/* Index of column of static statment/loop syntactic
	order, and starting with 0.
	Columns from m_syn_order_idx to
	get_col_size() - 1 composes the Gamma(¦£) matrix. */
	UINT m_syn_order_idx;

	/*
	Record the depth of STMT. It less than or equal
	get_max_depth() if there exists 'virtual' depth.
	*/
	UINT m_stmt_depth;
public:
	void init(UINT loop_nest_dim, UINT num_of_cst_sym);
	void copy(IN SCH_MAT const& s);
	inline UINT get_max_depth() const { return m_syn_order_idx; }
	inline UINT get_syn_order_idx() const { return m_syn_order_idx; }
	void set_stmt_order(UINT depth, UINT order);
	INT get_stmt_order(UINT depth) const;
	void set_stmt_depth(UINT depth);
	inline UINT get_stmt_depth() const { return m_stmt_depth; }
	UINT get_num_of_gamma() const;
	inline UINT get_num_of_var() const { return get_syn_order_idx(); }
	inline INT get_gamma_idx() const
	{ return get_num_of_gamma() > 0 ? m_syn_order_idx + 1 : -1; }
	void get_iter_mat(OUT RMAT & A);
	void set_iter_mat(IN RMAT const& A);
	void get_gamma_mat(OUT RMAT & G);
	void set_gamma_mat(IN RMAT const& G);
	inline VC_MAT const* get_map_iv() const { return &m_map_iv; }
	inline VC_MAT * get_map_iv_m() { return &m_map_iv; }

	INT map_depth2iv(UINT depth) const;
	INT map_iv2depth(UINT iv_idx) const;
	void set_map_depth2iv(UINT depth, UINT iv_idx);

	INT map_depth2pv(UINT depth, UINT pv_idx) const;
	void set_map_depth2pv(UINT depth, UINT pv_idx, INT pv_val);

	INT compute_stmt_row_pos(UINT depth) const;
	INT compute_loop_row_pos(UINT depth) const;
	void insert_loop_before(UINT iv_idx);
	void insert_loop_after(UINT iv_idx);
	void remove_loop(UINT iv_idx);
	void inc_stmt_order(UINT depth, UINT n = 1);
	void dec_stmt_order(UINT depth, UINT n = 1);
	void surround_stmt_by_loop();
	void interchange(INT iv_idx1, INT iv_idx2);
	void reverse(UINT iv_idx);
	void dump(IN FILE * h, IN POLY const& p);
};


//
//START DOMAIN_MAT
//
class DOMAIN_MAT : public RMAT {
public:
	DOMAIN_MAT() {}
	DOMAIN_MAT(INTMAT & i):RMAT(i) {}
	DOMAIN_MAT(RMAT & r):RMAT(r) {}
	DOMAIN_MAT(DOMAIN_MAT & r):RMAT(r) {}
	void insert_loop_before(UINT iv_idx);
	void insert_loop_after(UINT iv_idx);
	void remove_loop(UINT iv_idx);
	void interchange(INT iv_idx1, INT iv_idx2);
	void dump(IN FILE * h, IN SVECTOR<CHAR*> & var_name, IN POLY const& p);
};
//END DOMAIN_MAT


//
//START LOCVAR_MAT
//
class LOCVAR_MAT : public RMAT {
public:
	void insert_loop_before(UINT iv_idx);
	void insert_loop_after(UINT iv_idx);
	void remove_loop(UINT iv_idx);
	void dump(IN FILE * h, IN SVECTOR<CHAR*> & var_name, IN POLY const& p);
};
//END LOCVAR_MAT


//
//START CONT_MAT
//
class CONT_MAT : public RMAT {
public:
};
//END CONT_MAT



//
//START POLY
//
/* POLY correspond to individual statement.
It describe various polyhedral information, such as:
CONTEXT, DOMAIN, ACCESS FUNCTION, SCHEDULING FUNCTION.
The 'rhs_idx' of ACC_MAT and CONTEXT must have same value
as 'domain_rhs_idx'. */
#define POLY_id(p)						((p).id)
#define POLY_domain(p)					((p).domain)
#define POLY_domain_rhs_idx(p)			((p).domain_rhs_idx)
#define POLY_locvar_cs(p)				((p).locvar_constrains)
#define POLY_locvar_idx(p)				((p).local_variable_idx)
#define POLY_context(p)					((p).context)
#define POLY_acc_mgr(p)					((p).acc_mgr)
#define POLY_sche(p)					((p).scheduling_function)
#define POLY_stmt(p)					((p).stmt)
class POLY {
protected:
	SVECTOR<CHAR*> m_var_name; //record variable name, used for dump.
public:
	UINT id; //unique id.
	/* The context describes known restrictions concerning the parameters
	and relations in between the parameters.

		void f(char a, unsigned short b)
		{
			c = 2*a + b;
			A[c] = ...
		}

	Here we can add these restrictions to the context:

		-128 <= a <= 127
		0 <= b <= 65535
		c = 2*a + b
	*/
	RMAT * context;
	LOCVAR_MAT * locvar_constrains; //record local variable constrains
	DOMAIN_MAT * domain;
	UINT domain_rhs_idx;
	INT local_variable_idx; //initial value is -1
	ACC_MGR * acc_mgr;
	SCH_MAT * scheduling_function;
	SVECTOR<bool> is_local_var_vec;
	void * stmt; //correspond to IR STMT.

	POLY() { init(); }
	virtual ~POLY() { destroy(); }
	bool is_same_dim(POLY const& p) const;
	UINT insert_loop_before(UINT iv_idx, OUT UINT * changed_iv_idx = NULL);
	UINT insert_loop_after(UINT iv_idx);
	UINT surround_stmt_by_loop();
	UINT insert_local_var();
	void insert_localvar_cols(IN RMAT const& lv_cols);
	void remove_localvar_cols(IN OUT RMAT & lv_cols);
	bool remove_loop(UINT iv_idx);
	void init();
	void destroy();
	void copy(POLY const& p);
	bool grow_depth(UINT depth, IN RMAT const* domain_constrains = NULL);
	inline UINT get_max_depth() const
	{ return scheduling_function->get_max_depth(); }
	inline UINT get_stmt_depth() const
	{ return scheduling_function->get_stmt_depth(); }
	inline UINT get_num_of_param() const
	{ return domain->get_col_size() - domain_rhs_idx - 1; }
	inline UINT get_num_of_localvar() const
	{ return local_variable_idx==-1 ? 0:domain_rhs_idx - local_variable_idx; }
	inline UINT get_num_of_var() const
	{ return local_variable_idx==-1 ? domain_rhs_idx:local_variable_idx; }
	void set_var_name(UINT iv_idx, IN CHAR * name);
	CHAR * get_var_name(UINT iv_idx);
	bool move2depth(UINT depth);
	virtual void dump(IN CHAR * name = NULL);
	CHAR * dumpbuf(IN OUT CHAR * buf) { sprintf(buf, "..."); return buf; }
};
//END POLY



//
//START POLY_MGR
//
class POLY_MGR {
public:
	virtual ~POLY_MGR() {}

	virtual DOMAIN_MAT * new_domain_mat() { return new DOMAIN_MAT(); }
	virtual SCH_MAT * new_sch_mat() { return new SCH_MAT(); }
	virtual ACC_MGR * new_acc_mgr() { return new ACC_MGR(); }
	virtual POLY * new_poly() { return new POLY(); }
	virtual CONT_MAT * new_context() { return new CONT_MAT(); }

	//Create a polyhedron represetation.
	POLY * create_poly()
	{
		POLY * p = new_poly();
		POLY_domain(*p) = new_domain_mat();
		POLY_sche(*p) = new_sch_mat();
		POLY_acc_mgr(*p) = new_acc_mgr();
		POLY_context(*p) = new_context();
		return p;
	}

	//Destroy polyhedron represetation.
	void destroy_poly(POLY * p)
	{
		delete POLY_domain(*p);
		delete POLY_sche(*p);
		delete POLY_acc_mgr(*p);
		delete POLY_context(*p);
		delete p;
	}

	//Dump a list of polyhedrons.
	void dump_poly_list(IN LIST<POLY*> & lst);

	//Given a list of polyhedrons with different dimension,
	//this function find the maximum dimension and make all
	//polyhedrons to grow up to the maximum dimension.
	void grow_max_depth(IN OUT LIST<POLY*> & lst);

	//Copy a list of POLY from 'from' to 'to'.
	void copy_poly_list(IN LIST<POLY*> & from, OUT LIST<POLY*> & to);

	//Copy a list of POLY.
	void free_poly_list(LIST<POLY*> & lst);

	//Remove virtual depth for each polyhedron in list.
	void remove_virtual_depth(IN OUT LIST<POLY*> & lst);
};
//END POLY_MGR



//
//POLY TREE
//
//Record Abstract Tree Node during code generation.
#define POLY_TREE_UNDEF		0
#define POLY_TREE_LOOP		1
#define POLY_TREE_STMT		2
#define POLY_TREE_type(p)		(p)->type
#define POLY_TREE_poly(p)		(p)->poly
#define POLY_TREE_next(p)		(p)->next
#define POLY_TREE_prev(p)		(p)->prev
#define POLY_TREE_body(p)		(p)->body
class POLY_TREE {
public:
	INT type;
	POLY * poly;
	POLY_TREE * next;
	POLY_TREE * prev;
	POLY_TREE * body;
};


//Operations of POLY_TREE.
class POLY_TREE_MGR {
	SMEM_POOL * m_pool;
public:
	POLY_TREE_MGR();
	~POLY_TREE_MGR();
	void * xmalloc(ULONG size);
	POLY_TREE * new_poly_tree();
	POLY_TREE * insert(IN POLY * p, IN OUT POLY_TREE * root);
};


//
//START POLY_TRAN
//
/* Polytope, formed as Ax<=b, where A is an integer coefficient
matrix, vector x belongs to Z(n).
POLY defines a group of convex integer polyhedron.

Polyhedral information consists of three components:
iteration domains, schedules, and data accesses,
and the domains are defined by the loop bounds.
The translation from any compiler's IR to POLY builds
the iteration domains and schedule for each statement.

Scattering Polyhedra:
	A transformation function that is a transform in
	the polyhedral model that maps, for each statement,
	the original dynamic and static time to a new execution order.
	These transformation functions are also called scattering polyhedra.

The iteration domain for statement does not describe
the order in which the iterations are executed.
The execution order, or dynamic time, is defined by
the scattering dimensions of the scattering polyhedra. */
class POLY_TRAN {
	bool m_is_init;
	SMEM_POOL * m_pool;
	void * xmalloc(ULONG size);
	POLY_TREE * _scan(IN LIST<POLY*> & plst,
					POLY_TREE_MGR & ptmgr, INT depth);
	void step_0(IN OUT DG & g);
	void step_1(IN DG & g,
				IN OUT SVECTOR<UINT> & start_u_idx,
				IN OUT SVECTOR<UINT> & end_u_idx,
				IN OUT SVECTOR<UINT> & start_lam_idx,
				IN OUT SVECTOR<UINT> & end_lam_idx,
				IN OUT SVECTOR<POLY*> & poly_vec,
				IN OUT UINT * u_count,
				IN OUT UINT * lam_count);
	void step_2(IN DG & g,
				IN OUT RMAT & sys,
				IN OUT SVECTOR<RMAT*> & theta_vec,
				IN OUT SVECTOR<RMAT*> & lam_vec,
				IN SVECTOR<UINT> const& start_u_idx,
				IN SVECTOR<UINT> const& end_u_idx,
				IN SVECTOR<UINT> const& start_lam_idx,
				IN SVECTOR<UINT> const& end_lam_idx,
				IN UINT u_count,
				IN UINT lam_count);
	void step_3_1(IN OUT DG & g,
				  IN POLY const* p,
				  IN RMAT const& sol,
				  IN SVECTOR<RMAT*> const& theta_vec,
				  IN SVECTOR<UINT> const& start_u_idx,
			      IN SVECTOR<UINT> const& end_u_idx);
	void step_3(IN OUT DG & g,
				IN RMAT const& sol,
				IN SVECTOR<RMAT*> const& theta_vec,
				IN SVECTOR<UINT> const& start_u_idx,
				IN SVECTOR<UINT> const& end_u_idx);
	void step_4(IN DG & g,
				OUT RMAT & ub);
	void dump_lambda_info(IN DEP_POLY const* dp,
						  IN POLY const* from,
						  IN POLY const* to,
						  IN SVECTOR<UINT> const& start_lam_idx,
						  IN SVECTOR<UINT> const& end_lam_idx,
		   				  IN SVECTOR<RMAT*> const& lam_vec,
						  IN FILE * h);
	void dump_poly_info(IN RMAT const& sol,
						IN POLY const* p,
						IN SVECTOR<UINT> const& start_u_idx,
						IN SVECTOR<UINT> const& end_u_idx,
						IN SVECTOR<POLY*> const& poly_vec,
						IN SVECTOR<RMAT*> const& theta_vec,
						IN FILE * h);
	void fea_dump(IN DG & g,
				  IN RMAT const& sol,
				  IN SVECTOR<UINT> const& start_u_idx,
				  IN SVECTOR<UINT> const& end_u_idx,
				  IN SVECTOR<UINT> const& start_lam_idx,
				  IN SVECTOR<UINT> const& end_lam_idx,
				  IN SVECTOR<POLY*> const& poly_vec,
				  IN SVECTOR<RMAT*> const& theta_vec,
				  IN SVECTOR<RMAT*> const& lam_vec,
				  IN FILE * h);
public:
	POLY_TRAN();
	~POLY_TRAN();
	void init();

	bool cutdomain(IN POLY & poly, IN RMAT & c);

	void dump_poly_tree(POLY_TREE * t, INT indent);
	void destroy();

	bool fea_schedule(IN OUT DG & g, OUT RMAT & ub);
	bool fusion(IN LIST<POLY*> & lst,
				IN OUT LIST<POLY*> & scop_poly_lst,
				UINT depth);
	bool fission(IN OUT LIST<POLY*> & lst,
				IN OUT LIST<POLY*> & scop_poly_lst,
				IN POLY & split_p,
				UINT depth);

	bool is_lex_eq(POLY const& p1, POLY const& p2, UINT depth);
	bool is_lex_lt(POLY const& p1, POLY const& p2, OUT INT * diff = NULL);
	bool interchange(IN POLY & poly, INT d1, INT d2);
	bool interchange(LIST<POLY*> & lst, INT d1, INT d2);

	//Primitive polyhedra transformations
	bool unroll(IN POLY & poly);

	bool peel(IN POLY & poly);
	bool privatize(IN POLY & poly, UINT depth);

	bool nonsingular(IN POLY & poly, IN RMAT & t,
					OUT RMAT * pstride, OUT RMAT * pidx_map,
					OUT RMAT * pofst, OUT RMAT * pmul,
					bool tran_domain);

	bool tiling(IN OUT POLY & poly,
				UINT depth, UINT B,
				OUT UINT * changed_depth,
				OUT UINT * generated_depth);
	bool tiling(IN OUT LIST<POLY*> & lst,
				UINT depth, UINT B,
				OUT UINT * changed_depth,
				OUT UINT * generated_depth);

	bool shift(IN POLY & poly, IN UINT depth,
				IN UINT pv_idx, IN INT shift_val);
	bool stripmine(IN POLY & poly, UINT depth, UINT B,
					OUT UINT * changed_depth,
					OUT UINT * generated_depth);
	bool stripmine(IN OUT LIST<POLY*> & lst, UINT depth,
					UINT B, OUT UINT * changed_depth,
					OUT UINT * generated_depth);
	bool skew(IN OUT POLY & poly, UINT d_iv, UINT d_co, UINT factor);
	bool skew(IN OUT LIST<POLY*> & lst, UINT d_iv, UINT d_co, UINT factor);
	bool singular(IN POLY & poly, IN RMAT & t,
				OUT RMAT * pstride, OUT RMAT * pidx_map,
				OUT RMAT * pofst, OUT RMAT * pmul,
				bool tran_domain);
	bool scale(IN POLY & poly);

	//Code Generation
	void sort_in_lexical_order(IN OUT LIST<POLY*> & lst);
	void scan(IN LIST<POLY*> & plst);

	bool reverse(IN POLY & poly, UINT depth);
	bool reverse(IN OUT LIST<POLY*> & lst, UINT depth);

	//Composite polytope transformations
	bool unroll_and_jam(IN POLY & poly);
};
//END POLY_TRAN
#endif
