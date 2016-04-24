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
#ifndef __TRAN_GRAPHITE_H_
#define __TRAN_GRAPHITE_H_

//This file is an example to use xpoly as an loop transformation tool.

class GPOLY : public POLY {
public:
    virtual ~GPOLY() {}
    void dump_arr_base(poly_bb * pbb, FILE * h, INT indent);
    virtual void dump(CHAR * name = NULL);
};


//Reference Dependence Graph
class REF_DG : public DG {
public:
    REF_DG(IN LIST<POLY*> & lst);
    virtual ~REF_DG();
    virtual bool is_red_stmt(IN POLY const& p);
    void dump(IN LIST<POLY*> & lst, bool is_detail);
};


//Stmt Dependence Graph
#define SDG_stmt_vec(g)        ((g).stmt_vec)
#define SDG_stmt_bs(g)        ((g).stmt_bs)
class STMT_DG : public GRAPH {
public:
    BITSET stmt_bs; //record stmt in scop.
    SVECTOR<basic_block> stmt_vec;

    STMT_DG(scop * s);
    virtual ~STMT_DG() {}
    virtual void dump(CHAR * name = NULL);
};


class GPOLY_MGR : public POLY_MGR {
public:
    virtual ~GPOLY_MGR() {}
    virtual POLY * new_poly()
    {
        return new GPOLY();
    }
};
#endif
