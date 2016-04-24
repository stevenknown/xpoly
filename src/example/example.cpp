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

#include <math.h>

#include "ltype.h"
#include "comf.h"
#include "smempool.h"
#include "rational.h"
#include "flty.h"
#include "sstl.h"
#include "matt.h"
#include "xmat.h"
#include "bs.h"
#include "sbs.h"
#include "sgraph.h"
#include "lpsol.h"
#include "linsys.h"

using namespace xcom;

#include "depvecs.h"
#include "ldtran.h"
#include "ldtran.h"

//This function demostrate how to use SIX to compute maxmium solution.
void solve_linear_program2()
{
    /* Given system has 2 variable, x1, x2
    max = 2x1 - x2
    s.t.
        2x1 - x2 <= 2
        x1 - 5x2 <= -4

        x1,x2 >= 0
    */
    Float v;

    //Init linear inequality.
    FloatMat leq(2,3);
    leq.sete(6,
                2.0, -1.0,         2.0,
                1.0, -5.0,         -4.0);

    //Init target function.
    FloatMat tgtf(1,3);
    tgtf.sete(3,
                2.0, -1.0, 0.0);

    //Init variable constrain.
    FloatMat vc(2,3);
    vc.sete(6,
                -1.0,    0.0,    0.0,
                0.0,    -1.0,     0.0);

    FloatMat res, eq;
    SIX<FloatMat,Float> six;

    //Dump to check.
    tgtf.dumpf();
    vc.dumpf();
    leq.dumpf();

    /*
    maximum is 2
    solution is:
       14/9(1.555556)       10/9(1.111111)        0
    */
    if (SIX_SUCC == six.maxm(v,res,tgtf,vc,eq,leq)) {
        printf("\nmaxv is %f\n", v.f());
        printf("\nsolution is:\n"); res.dumpf();
    } else {
        printf("\nunbound");
    }
}


//This function demostrate how to use SIX to compute maxmium and minmum solution.
void solve_linear_program()
{
    /*
    Given system has 5 variable, v0, v1, v2, v3, v4.
    linear inequality:
        v0 >= 10
        v0 + v1 >= 8
        v0 + v1 + v2 >= 9
        v0 + v1 + v2 + v3 >= 11
        v1 + v2 + v3 + v4 >= 13
        v2 + v3 + v4 >= 8
        v3 + v4 >= 5
        v4 >= 3

    variable constrain:
        v0 >= 0
        v1 >= 0
        v2 >= 0
        v3 >= 0
        v4 >= 0

    target function:
        min=v0+v1+v2+v3+v4
    */
    Rational v; //maximum or minimum result value.
    RMat leq(8,6); //linear inequality.
    RMat eq; //linear equality.
    RMat tgtf(1,6); //target function.
    RMat vc(5,6); //variable constrain.
    RMat res; //result solution.

    tgtf.sete(6, //indicate tgtf has 6 elements.
              1, 1, 1, 1, 1, 0);  //

    leq.sete(48,
            -1,0,0,0,0,        -10,
            -1,-1,0,0,0,    -8,
            -1,-1,-1,0,0,    -9,
            -1,-1,-1,-1,0,    -11,
            0,-1,-1,-1,-1,    -13,
            0,0,-1,-1,-1,    -8,
            0,0,0,-1,-1,    -5,
            0,0,0,0,-1,        -3);

    vc.sete(30,
            -1,0,0,0,0,            0,
            0,-1,0,0,0,            0,
            0,0,-1,0,0,            0,
            0,0,0,-1,0,            0,
            0,0,0,0,-1,            0);

    SIX<RMat, Rational> six;

    //Dump to check.
    tgtf.dumps();
    vc.dumps();
    eq.dumps();
    leq.dumps();

    //solution is unbound
    if (SIX_SUCC != six.maxm(v, res,tgtf,vc,eq,leq)) {
        printf("\nunbound");
    } else {
        printf("\nmax val:%d/%d",v.num(), v.den());
        res.dumps();
    }

    /*
    min val:23
    solution is:v0=10  v1=5 v2=3  v3=2  v4=3  v5=1
    */
    if (SIX_SUCC != six.minm(v, res,tgtf,vc,eq,leq)) {
        //res is unbound!!
        printf("\nunbound");
    } else {
        printf("\nmin val:%d/%d",v.num(), v.den());
        res.dumps();
    }
}


INT main(INT argc, CHAR * argv[])
{
    solve_linear_program2();
    solve_linear_program();
    return 0;
}
