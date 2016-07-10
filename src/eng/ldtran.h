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
#ifndef __LOOP_DATA_TRAN_H_
#define __LOOP_DATA_TRAN_H_

/* Loop Transformation
TOD0: Simplified loop bound
    CASE1:
        e.g: test35()
            new upper loop bound is
                for (y = 0; y <= min( N, -1+x ); y++)
            but N alway large than x-1, so the perfectly
            upper bound should be
                for (y = 0; y <= (-1+x); y++)
*/
#define TGT_VAR_PREFIX "T"
#define ORG_VAR_PREFIX "I"
#define CST_SYM_PREFIX "C"
#define TGT_FLOOR    "FLOOR"
#define TGT_CEIL    "CEIL"
#define TGT_LP "zlp.tmp"

//Manner Options
#define OP_DELTA    1 //premultiply T by delta-matrix
#define    OP_PERM         2 //premultiply T by classical permuation matrix.
class LoopTran {
    SMemPool * m_pool;
    RMat * m_a; //Records loop limits: Ax <= b

    //Records starting column of right hand side of equation or inequlity.
    INT m_rhs_idx;
    void * xmalloc(size_t size)
    {
        void * p = smpoolMalloc(size,m_pool);
        ASSERT0(p);
        memset(p, 0, size);
        return p;
    }
public:
    LoopTran(RMat * m, INT rhs_idx = -1)
    {
        m_pool = NULL;
        m_rhs_idx = -1;
        m_a = NULL;
        init(m, rhs_idx);
    }
    ~LoopTran() { destroy(); }

    void init(RMat * m, INT rhs_idx = -1)
    {
        ASSERT0(m_pool == NULL);
        m_pool = smpoolCreate(16, MEM_COMM);
        if (m != NULL) {
            set_param(m, rhs_idx);
        }
    }

    void destroy()
    {
        ASSERT0(m_pool);
        m_a = NULL;
        m_rhs_idx = -1;
        smpoolDelete(m_pool);
        m_pool = NULL;
    }

    //Set index of const column and coeff matrix.
    void set_param(RMat * m, INT rhs_idx = -1);

    //Applying loop transformation.
    bool transformIterSpace(IN RMat & t,
                        OUT RMat & stride,
                        OUT RMat & idx_map,
                        OUT List<RMat*> & limits,
                        OUT RMat & ofst,
                        OUT RMat & mul,
                        OUT RMat * trA = NULL); //Perform nonunimodular trans.

    //Functions to generate automatically unimodular/nonsingular
    //transforming matrix for various loop transformations
    bool FullyPermute(OUT RMat & t, DVECS const& dvec);
    bool is_fully_permutable(DVECS const& dvec);
    bool is_legal(DVECS const& dvec);
    bool is_innermost_loop_parallelizable(DVECS const& dvec);
    bool permuteOutZeroRows(OUT RMat & t, RMat const& m);
    bool parallelInnerLoops(OUT RMat & t,
                            DVECS const& dvec,
                            UINT dep_level = 0,
                            UINT option = OP_DELTA | OP_PERM);
    bool parallelOuterLoops(OUT RMat & t, DVECS const& dvec);
    bool parallelMostLoops(OUT RMat & t, DVECS const& dvec);
};


//Generate C Code
class GEN_C {
    bool m_is_init;
    SMemPool * m_pool;
    RMat * m_a; //Records loop limits: Ax <= b
    INT m_rhs_idx; //Records starting column of right hand side of equation
                   //or inequlity.
    CHAR * m_sbuf; //buffer to hold the output string.
    UINT m_sbufl; //length of m_sbuf.
    void * xmalloc(size_t size);
    CHAR ** m_cst_sym;
    CHAR ** m_var_sym;
    CHAR ** m_org_sym;
public:
    GEN_C(RMat * m, INT rhs_idx = -1);
    ~GEN_C();
    void init(RMat * m, INT rhs_idx = -1);
    void destroy();

    //Set index of const column and coeff matrix.
    void set_param(RMat * m, INT rhs_idx = -1);
    void set_sym(CHAR ** tgtvar_sym = NULL,
                CHAR ** orgvar_sym = NULL, CHAR ** cst_sym = NULL);
    /*
    Functions to generate code for new loop bound and the mapping
    code in between iteration space that used in loop body.
    */
    CHAR * get_orgvar_sym(OUT CHAR * sbuf, INT varid);
    CHAR * get_newvar_sym(OUT CHAR * sbuf, INT varid);
    CHAR * get_cst_sym(OUT CHAR * sbuf, INT varid);
    void gen_ppl(OUT CHAR sbuf[], INT num);//placeholder
    void genidxm(OUT CHAR sbuf[], IN RMat & idx_map);
    bool genofst(OUT CHAR sbuf[], IN RMat & ofst);
    void genub(OUT CHAR sbuf[], IN RMat * limits, INT ub, INT ivar);
    void genlb(OUT CHAR sbuf[], IN RMat * limits, INT lb, INT ivar);
    void genmin(OUT CHAR sbuf[], IN RMat * limits, INT ub1, INT ub2, INT ivar);
    void genmax(OUT CHAR sbuf[], IN RMat * limits, INT lb1, INT lb2, INT ivar);
    void genmaxs(OUT CHAR sbuf[], IN RMat * limits,
                    INT lbnum,    INT * lb, INT ivar);
    void genmins(OUT CHAR sbuf[], IN RMat * limits,
                    INT ubnum, INT * ub, INT ivar);
    void genlinexp(OUT CHAR sbuf[], IN RMat & coeff_vec, INT ivar,
                    INT comden, bool is_lb, UINT sym_start_cl, UINT num_sc);
    void gen_loop_start(OUT CHAR sbuf[], INT stride,
                    IN RMat * limits, IN RMat & ofst, INT mul, INT ivar,
                    INT * lb, INT lbnum);
    void gen_loop_end(OUT CHAR sbuf[], INT stride,
                    IN RMat * limits, IN RMat & ofst, INT mul, INT ivar,
                    INT * ub, INT ubnum);
    void gen_loop_step(OUT CHAR sbuf[], INT stride,
                    IN RMat * limits, IN RMat & ofst, INT mul, INT ivar);
    void genlimit(OUT CHAR sbuf[], INT stride, IN RMat * limits,
                    IN RMat & ofst, INT mul, INT ivar);
    void genlimits(IN List<RMat*> & limits,
                    IN RMat * pstride = NULL,
                    IN RMat * pidx_map = NULL,
                    IN RMat * pofst = NULL,
                    IN RMat * pmul = NULL,
                    IN CHAR * name = NULL,
                    bool is_del = false);
};
#endif

