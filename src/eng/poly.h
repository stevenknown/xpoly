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
class Poly;
class AccMat;
class DepPoly;
class DepVec;
class VarConstraintMat;
class DepPolyHash;
class DepPolyMgr;


//
//START DepPoly
//
#define DEP_LOOP_CARRIED		1
#define DEP_LOOP_INDEP			2
#define DEP_POLY_id(d)			((d).id)
#define DEP_POLY_flag(d)		((d).flag)
#define DEP_POLY_rhs_idx(d)		((d).rhs_idx)
class DepPoly : public RMat {
public:
	UINT id; //each dep-poly has an unique id.
	UINT flag; //record dependence-type: LOOP_CARRIED, LOOP_INDEPENDENT
	UINT rhs_idx;

	DepPoly()
	{
		id = 0;
		flag = 0;
		rhs_idx = 0;
	}

	DepPoly(UINT row, UINT col) : RMat(row, col)
	{
		id = 0;
		flag = 0;
		rhs_idx = 0;
	}

	DepPoly(RMat const& r, UINT rhs_idx) : RMat(r)
	{
		id = 0;
		flag = 0;
		this->rhs_idx = rhs_idx;
	}

	~DepPoly() {}

	void copy(IN DepPoly const& dp);
	void copy(IN RMat const& r, UINT rhs_idx);

	void dump();
	void dump(FILE * h, UINT indent);

	inline UINT get_from_iv_idx_start() const { return 0; }
	inline UINT get_to_iv_idx_start() const { return rhs_idx / 2; }
	inline UINT get_num_of_from_iv() const { return get_to_iv_idx_start(); }
	inline UINT get_num_of_to_iv() const { return get_num_of_from_iv(); }

	void intersect(IN RMat const& r);
	void intersect(IN DepPoly const& dp);
	bool is_empty(bool keepit, VarConstraintMat const* vc);
	inline bool is_loop_carried() const
	{ return HAVE_FLAG(DEP_POLY_flag(*this), DEP_LOOP_CARRIED); }
	inline bool is_loop_indep() const
	{ return HAVE_FLAG(DEP_POLY_flag(*this), DEP_LOOP_INDEP); }

	void insertLoopBefore(UINT iv_idx);
	void insertLocalVar(OUT UINT * lv1_idx, OUT UINT * lv2_idx);

	void eliminateAuxVar(IN Poly const& from, IN Poly const& to);

	void removeLocalVar();
	void removeLoop(UINT iv_idx);
};
//END DepPoly


class DepPolyList : public List<DepPoly*> {
public:
	~DepPolyList()
	{
		freeElement();
	}

	void freeElement()
	{
		for (DepPoly * p = get_head(); p != NULL; p = get_next()) {
			delete p;
		}
	}
	void intersect(IN DepPolyList & dpl);
	bool is_intersect_empty(IN DepPolyList & dpl);
	bool is_empty(bool keepit, VarConstraintMat const* vc);
};


#define DPVEC_from_id(d)		((d).from_acc_mat_id)
#define DPVEC_to_id(d)			((d).to_acc_mat_id)
class DepVec : public Vector<DepPolyList*> {
public:
	UINT from_acc_mat_id;
	UINT to_acc_mat_id;

	DepVec(UINT from_id, UINT to_id);
	~DepVec();
	bool is_intersect_empty(DepVec const& dpvec,
							bool is_cross_depth = false) const;
	void freeElement();
	void copy(DepVec const& d);
	DepPolyList * get_innermost() const;
	void dump(FILE * h, UINT indent);
	void dump();
};


#define REF_HASH_from_id(d)		((d).from_stmt_id)
#define REF_HASH_to_id(d)		((d).to_stmt_id)
#define MAKE_REF_ID(d)			(DPVEC_from_id(d) | DPVEC_to_id(d))

class DepVecHashFunc {
public:
	UINT get_hash_value(DepVec * d, UINT bucket_size) const
	{ return MAKE_REF_ID(*d) % bucket_size; }

	bool compare(DepVec * d1, DepVec * d2) const
	{
		return DPVEC_from_id(*d1) == DPVEC_from_id(*d2) &&
			   DPVEC_to_id(*d1) == DPVEC_to_id(*d2);
	}
};


class RefHash : public Hash<DepVec*, DepVecHashFunc> {
public:
	UINT from_stmt_id;
	UINT to_stmt_id;

	RefHash(UINT from_id, UINT to_id)
	{
		from_stmt_id = from_id;
		to_stmt_id = to_id;
	}
	~RefHash() { freeElement(); }

	void freeElement()
	{
		INT c;
		for (DepVec * d = get_first(c); d != NULL; d = get_next(c)) {
			delete d;
		}
	}
};


#define MAKE_STMT_ID(d)		(REF_HASH_from_id(d) | REF_HASH_to_id(d))

class RefHashFunc {
public:
	UINT get_hash_value(RefHash * d, UINT bucket_size) const
	{ return MAKE_STMT_ID(*d) % bucket_size; }

	bool compare(RefHash * d1, RefHash * d2) const
	{
		return REF_HASH_from_id(*d1) == REF_HASH_from_id(*d2) &&
			   REF_HASH_to_id(*d1) == REF_HASH_to_id(*d2);
	}
};


class StmtHash : public Hash<RefHash*, RefHashFunc> {
public:
	~StmtHash() { freeElement();	}
	void freeElement()
	{
		INT c;
		for (RefHash * r = get_first(c); r != NULL; r = get_next(c)) {
			delete r;
		}
	}
};


class DepPolyHash : public StmtHash {
public:
	void clean()
	{
		freeElement();
		StmtHash::clean();
	}

	DepVec * find(Poly const& from, Poly const& to,
				 AccMat const& am1, AccMat const& am2);
	DepVec * append(Poly const& from, Poly const& to,
				   AccMat const& am1, AccMat const& am2);
};


//
//START DepPolyMgr
//
class DepPolyMgr {
	DepPolyHash m_dh;
	void buildCommonEquation(Poly const& from, Poly const& to,
								INT depth, bool include_depth,
								OUT RMat & res);
	void buildDomainExecCond(Poly const& from, Poly const& to,
								OUT RMat & res);
	void buildAccExecCond(Poly const& from, Poly const& to,
							AccMat const& from_acc, AccMat const& to_acc,
							OUT RMat & res);
	void buildContextRelation(Poly const& from, Poly const& to,
								OUT RMat & res);
public:
	DepPolyMgr();
	~DepPolyMgr();
	void clean();

	DepPolyList * conjoin(DepPoly const& c1,	DepPoly const& c2,
							VarConstraintMat const* vc);
	DepVec * get_dpvec(Poly const& from, Poly const& to,
					AccMat const& am1, AccMat const& am2);

	void get_all_dep_poly(IN OUT List<DepPoly*> & lst);
	void insertLocalVar(OUT UINT * lv1_idx = NULL,
						OUT UINT * lv2_idx = NULL);
	void insertLoopBefore(UINT iv_idx);
	void removeLoop(UINT iv_idx);
	void removeLocalVar();
	void reviseNegIVConstraint(Poly const& from, Poly const& to,
						IN OUT DepPoly & cs);
	VarConstraintMat * buildVarConstraint(Poly const& from, Poly const& to, OUT VarConstraintMat & vc);
	void buildMapIVCoeff(Poly const& from, Poly const& to,
							OUT Vector<INT> & coeff);
	void buildLoopIndependent(Poly const& from, Poly const& to,
								bool is_reverse, UINT depth,
								OUT RMat & res);
	void buildLoopCarried(Poly const& from, Poly const& to,
							bool is_reverse, UINT depth,
							OUT RMat & res);
	void buildSynOrderRelation(Poly const& from, Poly const& to,
								bool is_reverse, UINT depth,
								OUT RMat & res);
	void build(Poly const& from, Poly const& to,
			   AccMat const& from_acc, AccMat const& to_acc,
			   VarConstraintMat const* vc, OUT DepVec & dpvec,
			   bool is_reverse);
	DepVec * buildDepPoly(Poly const& from, Poly const& to,
						AccMat const& from_acc, AccMat const& to_acc,
						VarConstraintMat const* vc, bool is_reverse);
	void buildDepPoly(Poly const& from, Poly const& to,
						AccMat const& from_acc, AccMat const& to_acc,
						VarConstraintMat const* vc, OUT DepVec & dpvec,
						bool is_reverse);
	void dump(IN List<Poly*> & lst);
};
//END DepPolyMgr



//
//START DepGraph (Dependence Graph)
//
#define DGEINFO_dpvec(e)				((e)->dpvec)
#define DGEINFO_from_quasi_func(e)		((e)->from_quasi_func)
#define DGEINFO_to_quasi_func(e)		((e)->to_quasi_func)
class DepGraphInfo {
public:
	DepVec const* dpvec;
	RMat * from_quasi_func;
	RMat * to_quasi_func;
	DepGraphInfo() { dpvec = NULL; from_quasi_func = NULL; to_quasi_func = NULL; }
};


//Dependence Graph.
class DepGraph : public Graph {
protected:
	//True if one intends building graph at dependence analysis.
	bool m_is_build_graph;
	Vector<RMat*> m_sch_mat; //record schedule matrix for each Poly.
	DepPolyMgr m_orig_dpmgr; //record original dependencn polyhedra.
	SMemPool * m_pool;

	void * xmalloc(size_t size)
	{
		ASSERT0(m_pool);
		void * p = smpoolMalloc(size, m_pool);
		ASSERT0(p);
		memset(p, 0, size);
		return p;
	}
public:
	DepGraph(IN List<Poly*> & lst, bool is_build_graph = false);
	virtual ~DepGraph();
	virtual bool is_red_stmt(Poly const& p);
	virtual bool is_red_pair(Poly const& p1, Poly const& p2,
							 AccMat const& am1, AccMat const& am2);
	bool is_build_graph() const { return m_is_build_graph; }
	bool is_legal(IN List<Poly*> & lst);

	//Get the dependence polyhedron.
	DepVec const* get_dep_poly(Edge const* e) const;

	//Get the polyhedron correspond to v.
	Poly const* get_poly(Vertex const* v) const;
	RMat * get_from_quasi_func(IN Edge const* e) const;
	RMat * get_to_quasi_func(IN Edge const* e) const;
	RMat * get_sch_mat(IN Poly const* p);
	inline DepPolyMgr * get_orig_dep_mgr() { return &m_orig_dpmgr; }

	void rebuild(IN List<Poly*> & lst, bool is_build_graph = false);

	void set_dep_poly(Vertex const* from, Vertex const* to, DepVec const* dp);
	void set_dep_poly(IN Edge * e, IN DepVec const* dp);
	void set_poly(IN Vertex * v, IN Poly * p);
	void set_from_quasi_func(IN Edge * e, IN RMat * quasi);
	void set_to_quasi_func(IN Edge * e, IN RMat * quasi);

	bool verify(IN List<Poly*> & lst, IN DepPolyHash & dh);
};
//END DepGraph



//
//START AccMat
//
/* The designation of artifical array which can be privatized.
  General_Reduction
  Close_Phi
  Cross_BB_scalar_dependence
  Commutative_Associative_Reduction */
#define ACC_MAT_id(a)			((a).id)
#define ACC_MAT_arr_id(a)		((a).array_base_id)
class AccMat : public RMat {
public:
	UINT id; //unique identifier
	UINT array_base_id;

	AccMat() { id = 0; array_base_id = 0; }
	AccMat(AccMat const& a) : RMat(a)
	{ id = a.id; array_base_id = a.array_base_id; }
	void insertLoopBefore(UINT iv_idx);
	void insertLoopAfter(UINT iv_idx);
	void surroundAccByLoop();
	void removeLoop(UINT iv_idx);
	void dump(IN FILE * h, IN Vector<CHAR*> & var_name,
			  Poly const& p, UINT indent);
};


//
//START AccMgr
//
class AccMgr {
protected:
	Vector<AccMat*> m_read_vec; //list to READ access matrix.
	Vector<AccMat*> m_write_vec; //list to WRITE access matrix.

	//Map from array-base-id to its entirely references.
	Vector<List<AccMat*>*> m_map_arr_base_id2refs;
public:
	AccMgr();
	~AccMgr();
	void cleanData();
	void clean();
	void copy(AccMgr const& am);

	void dump(FILE * h, Vector<CHAR*> & var_name, Poly const& p);

	bool is_read(IN AccMat const& acc_mat) const;
	bool is_write(IN AccMat const& acc_mat) const;
	void insertLocalVar(UINT rhs_idx);
	void insertLoopBefore(UINT iv_idx);
	void insertLoopAfter(UINT iv_idx);

	INT get_max_arr_base_id() const
	{ return m_map_arr_base_id2refs.get_last_idx(); }

	void get_read_refs(OUT List<AccMat*> & lst) const;
	void get_write_refs(OUT List<AccMat*> & lst) const;

	List<AccMat*> * mapArrayId2Refs(UINT arr_id);
	UINT map_ref2arr_id(AccMat const* acc_mat) const;

	void removeLoop(UINT iv_idx);

	void surroundAccByLoop();
	AccMat * set_ref(IN AccMat const& acc_mat, bool is_read);

	void privatize(UINT iv_idx);
};
//END AccMgr


class VarConstraintMat : public INTMat {
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
		ASSERT0(depth >= 1 && iv_idx < get_col_size());
		return get(depth, iv_idx);
	}
};


//
//START ScheduleMat
//
//Before any polyhedral transformations,
//A is identity, ¦£ is 0, and ¦Â is vector.
class ScheduleMat : public RMat {
protected:
	//Record iv_idx for each depth level.
	//Rows indicate depth, cols indicate iv_idx.
	VarConstraintMat m_map_iv;

	/* Index of column of static statment/loop syntactic
	order, and starting with 0.
	Columns from m_syn_order_idx to
	get_col_size() - 1 composes the Gamma(¦£) matrix. */
	UINT m_syn_order_idx;

	//Record the depth of STMT. It less than or equal
	//get_max_depth() if there exists 'virtual' depth.
	UINT m_stmt_depth;
public:
	void init(UINT loop_nest_dim, UINT num_of_cst_sym);
	void copy(IN ScheduleMat const& s);
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
	void get_iter_mat(OUT RMat & A);
	void set_iter_mat(IN RMat const& A);
	void get_gamma_mat(OUT RMat & G);
	void set_gamma_mat(IN RMat const& G);
	inline VarConstraintMat const* get_map_iv() const { return &m_map_iv; }
	inline VarConstraintMat * get_map_iv_m() { return &m_map_iv; }

	INT mapIV2Depth(UINT iv_idx) const;
	INT mapDepth2IV(UINT depth) const;
	void setMapDepth2IV(UINT depth, UINT iv_idx);

	INT mapDepth2PV(UINT depth, UINT pv_idx) const;
	void set_mapDepth2PV(UINT depth, UINT pv_idx, INT pv_val);

	INT computeStmtRowPos(UINT depth) const;
	INT computeLoopRowPos(UINT depth) const;
	void insertLoopBefore(UINT iv_idx);
	void insertLoopAfter(UINT iv_idx);
	void removeLoop(UINT iv_idx);
	void incStmtOrder(UINT depth, UINT n = 1);
	void decStmtOrder(UINT depth, UINT n = 1);
	void surroundStmtByLoop();
	void interchange(INT iv_idx1, INT iv_idx2);
	void reverse(UINT iv_idx);
	void dump(IN FILE * h, IN Poly const& p);
};


//
//START DomainMat
//
class DomainMat : public RMat {
public:
	DomainMat() {}
	DomainMat(INTMat & i):RMat(i) {}
	DomainMat(RMat & r):RMat(r) {}
	DomainMat(DomainMat & r):RMat(r) {}
	void insertLoopBefore(UINT iv_idx);
	void insertLoopAfter(UINT iv_idx);
	void removeLoop(UINT iv_idx);
	void interchange(INT iv_idx1, INT iv_idx2);
	void dump(IN FILE * h, IN Vector<CHAR*> & var_name, IN Poly const& p);
};
//END DomainMat


//
//START LocalVarMat
//
class LocalVarMat : public RMat {
public:
	void insertLoopBefore(UINT iv_idx);
	void insertLoopAfter(UINT iv_idx);
	void removeLoop(UINT iv_idx);
	void dump(IN FILE * h, IN Vector<CHAR*> & var_name, IN Poly const& p);
};
//END LocalVarMat


//
//START ContextMat
//
class ContextMat : public RMat {
public:
};
//END ContextMat



//
//START Poly
//
/* Poly correspond to individual statement.
It describe various polyhedral information, such as:
CONTEXT, DOMAIN, ACCESS FUNCTION, SCHEDULING FUNCTION.
The 'rhs_idx' of AccMat and CONTEXT must have same value
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
class Poly {
protected:
	Vector<CHAR*> m_var_name; //record variable name, used for dump.
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
	RMat * context;
	LocalVarMat * locvar_constrains; //record local variable constrains
	DomainMat * domain;
	UINT domain_rhs_idx;
	INT local_variable_idx; //initial value is -1
	AccMgr * acc_mgr;
	ScheduleMat * scheduling_function;
	Vector<bool> is_local_var_vec;
	void * stmt; //correspond to IR STMT.

public:
	Poly() { init(); }
	virtual ~Poly() { destroy(); }

	bool is_same_dim(Poly const& p) const;
	UINT insertLoopBefore(UINT iv_idx, OUT UINT * changed_iv_idx = NULL);
	UINT insertLoopAfter(UINT iv_idx);
	UINT insertLocalVar();
	void insertLocalVarColumns(IN RMat const& lv_cols);
	void init();
	void destroy();

	void copy(Poly const& p);

	bool grow_depth(UINT depth, IN RMat const* domain_constrains = NULL);

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

	UINT surroundStmtByLoop();

	void removeLocalVarColumns(IN OUT RMat & lv_cols);
	bool removeLoop(UINT iv_idx);
};
//END Poly



//
//START PolyMgr
//
class PolyMgr {
public:
	virtual ~PolyMgr() {}

	virtual DomainMat * newDomainMat() { return new DomainMat(); }
	virtual ScheduleMat * newScheduleMat() { return new ScheduleMat(); }
	virtual AccMgr * newAccMgr() { return new AccMgr(); }
	virtual Poly * newPoly() { return new Poly(); }
	virtual ContextMat * newContextMat() { return new ContextMat(); }

	//Create a polyhedron represetation.
	Poly * createPoly()
	{
		Poly * p = newPoly();
		POLY_domain(*p) = newDomainMat();
		POLY_sche(*p) = newScheduleMat();
		POLY_acc_mgr(*p) = newAccMgr();
		POLY_context(*p) = newContextMat();
		return p;
	}

	//Destroy polyhedron represetation.
	void destroyPoly(Poly * p)
	{
		delete POLY_domain(*p);
		delete POLY_sche(*p);
		delete POLY_acc_mgr(*p);
		delete POLY_context(*p);
		delete p;
	}

	//Dump a list of polyhedrons.
	void dump_poly_list(IN List<Poly*> & lst);

	//Given a list of polyhedrons with different dimension,
	//this function find the maximum dimension and make all
	//polyhedrons to grow up to the maximum dimension.
	void growToMaxDepth(IN OUT List<Poly*> & lst);

	//Copy a list of Poly from 'from' to 'to'.
	void copyPolyList(IN List<Poly*> & from, OUT List<Poly*> & to);

	//Copy a list of Poly.
	void freePolyList(List<Poly*> & lst);

	//Remove virtual depth for each polyhedron in list.
	void removeVirtualDepth(IN OUT List<Poly*> & lst);
};
//END PolyMgr



//
//Poly Tree
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
class PolyTree {
public:
	INT type;
	Poly * poly;
	PolyTree * next;
	PolyTree * prev;
	PolyTree * body;
};


//Operations of PolyTree.
class PolyTreeMgr {
	SMemPool * m_pool;
public:
	PolyTreeMgr();
	~PolyTreeMgr();
	void * xmalloc(size_t size);
	PolyTree * newPolyTree();
	PolyTree * insert(IN Poly * p, IN OUT PolyTree * root);
};


//
//START PolyTran
//
/* Polytope, formed as Ax<=b, where A is an integer coefficient
matrix, vector x belongs to Z(n).
Poly defines a group of convex integer polyhedron.

Polyhedral information consists of three components:
iteration domains, schedules, and data accesses,
and the domains are defined by the loop bounds.
The translation from any compiler's IR to Poly builds
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
class PolyTran {
	bool m_is_init;
	SMemPool * m_pool;
	void * xmalloc(size_t size);
	PolyTree * _scan(IN List<Poly*> & plst,
					PolyTreeMgr & ptmgr, INT depth);
	void step_0(IN OUT DepGraph & g);
	void step_1(IN DepGraph & g,
				IN OUT Vector<UINT> & start_u_idx,
				IN OUT Vector<UINT> & end_u_idx,
				IN OUT Vector<UINT> & start_lam_idx,
				IN OUT Vector<UINT> & end_lam_idx,
				IN OUT Vector<Poly*> & poly_vec,
				IN OUT UINT * u_count,
				IN OUT UINT * lam_count);
	void step_2(IN DepGraph & g,
				IN OUT RMat & sys,
				IN OUT Vector<RMat*> & theta_vec,
				IN OUT Vector<RMat*> & lam_vec,
				IN Vector<UINT> const& start_u_idx,
				IN Vector<UINT> const& end_u_idx,
				IN Vector<UINT> const& start_lam_idx,
				IN Vector<UINT> const& end_lam_idx,
				IN UINT u_count,
				IN UINT lam_count);
	void step_3_1(IN OUT DepGraph & g,
				  IN Poly const* p,
				  IN RMat const& sol,
				  IN Vector<RMat*> const& theta_vec,
				  IN Vector<UINT> const& start_u_idx,
			      IN Vector<UINT> const& end_u_idx);
	void step_3(IN OUT DepGraph & g,
				IN RMat const& sol,
				IN Vector<RMat*> const& theta_vec,
				IN Vector<UINT> const& start_u_idx,
				IN Vector<UINT> const& end_u_idx);
	void step_4(IN DepGraph & g,
				OUT RMat & ub);
	void dump_lambda_info(IN DepPoly const* dp,
						  IN Poly const* from,
						  IN Poly const* to,
						  IN Vector<UINT> const& start_lam_idx,
						  IN Vector<UINT> const& end_lam_idx,
		   				  IN Vector<RMat*> const& lam_vec,
						  IN FILE * h);
	void dump_poly_info(IN RMat const& sol,
						IN Poly const* p,
						IN Vector<UINT> const& start_u_idx,
						IN Vector<UINT> const& end_u_idx,
						IN Vector<Poly*> const& poly_vec,
						IN Vector<RMat*> const& theta_vec,
						IN FILE * h);
	void fea_dump(IN DepGraph & g,
				  IN RMat const& sol,
				  IN Vector<UINT> const& start_u_idx,
				  IN Vector<UINT> const& end_u_idx,
				  IN Vector<UINT> const& start_lam_idx,
				  IN Vector<UINT> const& end_lam_idx,
				  IN Vector<Poly*> const& poly_vec,
				  IN Vector<RMat*> const& theta_vec,
				  IN Vector<RMat*> const& lam_vec,
				  IN FILE * h);
public:
	PolyTran();
	~PolyTran();
	void init();

	bool cutdomain(IN Poly & poly, IN RMat & c);

	void dump_poly_tree(PolyTree * t, INT indent);
	void destroy();

	bool FeaSchedule(IN OUT DepGraph & g, OUT RMat & ub);
	bool fusion(IN List<Poly*> & lst,
				IN OUT List<Poly*> & scop_poly_lst,
				UINT depth);
	bool fission(IN OUT List<Poly*> & lst,
				IN OUT List<Poly*> & scop_poly_lst,
				IN Poly & split_p,
				UINT depth);

	bool is_lex_eq(Poly const& p1, Poly const& p2, UINT depth);
	bool is_lex_lt(Poly const& p1, Poly const& p2, OUT INT * diff = NULL);
	bool interchange(IN Poly & poly, INT d1, INT d2);
	bool interchange(List<Poly*> & lst, INT d1, INT d2);

	//Primitive polyhedra transformations
	bool unroll(IN Poly & poly);

	bool peel(IN Poly & poly);
	bool privatize(IN Poly & poly, UINT depth);

	bool nonsingular(IN Poly & poly, IN RMat & t,
					OUT RMat * pstride, OUT RMat * pidx_map,
					OUT RMat * pofst, OUT RMat * pmul,
					bool tran_domain);

	bool tiling(IN OUT Poly & poly,
				UINT depth, UINT B,
				OUT UINT * changed_depth,
				OUT UINT * generated_depth);
	bool tiling(IN OUT List<Poly*> & lst,
				UINT depth, UINT B,
				OUT UINT * changed_depth,
				OUT UINT * generated_depth);

	bool shift(IN Poly & poly, IN UINT depth,
				IN UINT pv_idx, IN INT shift_val);
	bool stripmine(IN Poly & poly, UINT depth, UINT B,
					OUT UINT * changed_depth,
					OUT UINT * generated_depth);
	bool stripmine(IN OUT List<Poly*> & lst, UINT depth,
					UINT B, OUT UINT * changed_depth,
					OUT UINT * generated_depth);
	bool skew(IN OUT Poly & poly, UINT d_iv, UINT d_co, UINT factor);
	bool skew(IN OUT List<Poly*> & lst, UINT d_iv, UINT d_co, UINT factor);
	bool singular(IN Poly & poly, IN RMat & t,
				OUT RMat * pstride, OUT RMat * pidx_map,
				OUT RMat * pofst, OUT RMat * pmul,
				bool tran_domain);
	bool scale(IN Poly & poly);

	//Code Generation
	void sortInLexcialOrder(IN OUT List<Poly*> & lst);
	void scan(IN List<Poly*> & plst);

	bool reverse(IN Poly & poly, UINT depth);
	bool reverse(IN OUT List<Poly*> & lst, UINT depth);

	//Composite polytope transformations
	bool UnrollAndJam(IN Poly & poly);
};
//END PolyTran
#endif
