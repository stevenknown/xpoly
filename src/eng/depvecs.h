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

#ifndef __DEPVEC_H__
#define __DEPVEC_H__


class DVECS;

//Generating transforming matrix.
//Directio Dependence Type
typedef enum {
    DT_DIS = 0,
    DT_POS,
    DT_NEG,
    DT_MISC,
} DT;

//Data Dependence.
//If 'dir' is DDT_DIS, that indicate the data dependence is constant, otherwise
//being direction of '+=,-=' or indefinitely.
class DD {
public:
    DT dir;
    INT dis;

    DD(){dir = DT_MISC; dis = 0;}
    DD(DT ddir)
    {
        dir = ddir;
        switch (dir) {
        case DT_DIS:
            ASSERT(0, ("Distant-dependence must take a constant value"));
            break;
        case DT_POS:
        case DT_NEG:
        case DT_MISC:
            dis = 0; break;
        default: ASSERT(0,("unknown operand"));
        }
    }
    DD(DT ddir, INT ddis)
    {
        dir = ddir; dis = ddis;
        switch (dir) {
        case DT_DIS:
        case DT_MISC: break;
        case DT_POS: ASSERT(dis >= 0, ("illegal bound")); break;
        case DT_NEG: ASSERT(dis <= 0, ("illegal bound")); break;
        default: ASSERT(0,("unknown operand"));
        }
    }
    DD(INT a){dir = DT_DIS; dis = a;} //support declaration as 'DD a=0'
};


//Dependence Matix, each row characterize one dependence vector.
//Dependence vector descripting distance/direction dependence.
class DVECS : public Matrix<DD> {
    friend DVECS operator * (DVECS const& a, DVECS const& b);
    friend DVECS operator + (DVECS const& a, DVECS const& b);
    friend DVECS operator - (DVECS const& a, DVECS const& b);
    friend DVECS operator * (RMat const& a, DVECS const& b);
    friend DVECS operator + (RMat const& a, DVECS const& b);
    friend DVECS operator - (RMat const& a, DVECS const& b);
    bool m_is_init;
public:
    DVECS();
    DVECS(DVECS const& m);
    DVECS(UINT row, UINT col);
    ~DVECS();
    void init();
    void destroy();
    void sete(UINT num, ...);
    void setv(UINT num, Vector<DD> const& dd);
    bool cvt_to(OUT RMat & r); //Converting dvecs to rmat.
    DVECS & operator = (DVECS const& m);
    DVECS & operator = (RMat const& m);
    DVECS & operator = (INTMat const& m);
};

#define DD_TRUE        1
#define DD_FALSE    0
#define DD_UNK        2 //unknown relation

extern bool operator == (DD const& a, DD const& b);
extern bool operator != (DD const& a, DD const& b);
extern bool operator < (DD const& a, DD const& b);
extern bool operator <= (DD const& a, DD const& b);
extern bool operator > (DD const& a, DD const& b);
extern bool operator >= (DD const& a, DD const& b);
UINT DD_Le (DD const& a, DD const& b);
UINT DD_Ge (DD const& a, DD const& b);
UINT DD_Lt (DD const& a, DD const& b);
UINT DD_Gt (DD const& a, DD const& b);

extern DD operator * (DD const& a, DD const& b);
extern DD operator / (DD const& a, DD const& b);
extern DD operator + (DD const& a, DD const& b);
extern DD operator - (DD const& a, DD const& b);
extern DD operator - (DD const& a);
#endif
