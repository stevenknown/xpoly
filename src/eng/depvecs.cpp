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
#include "sstl.h"
#include "matt.h"
#include "rational.h"
#include "flty.h"
#include "xmat.h"

using namespace xcom;

#include "depvecs.h"

UINT DD_Le (DD const& a, DD const& b)
{
	if (a == b) {
		return DD_TRUE;
	}
	return DD_Lt(a, b);
}


UINT DD_Ge (DD const& a, DD const& b)
{
	if (a == b) {
		return DD_TRUE;
	}
	return DD_Gt(a, b);
}


UINT DD_Lt (DD const& a, DD const& b)
{
	return DD_Gt(b, a);
}


UINT DD_Gt (DD const& a, DD const& b)
{
	if (a.dir == DT_DIS && b.dir == DT_DIS) { //a is Dis,b is Dis
		if (a.dis > b.dis) {
			return DD_TRUE;
		} else {
			return DD_FALSE;
		}
	} else {//a is DIS, or b, or neither
		if (a.dir == DT_DIS) { //a is Dis,b is not Dis
			if(a.dis > 0) {
				if (b.dir == DT_NEG) {
					return DD_TRUE;
				}
				if (b.dir == DT_POS && a.dis < b.dis) {
					return DD_FALSE;
				}
			} else if (a.dis == 0) {
				if (b.dir == DT_NEG && b.dis < 0) {
					return DD_TRUE;
				}
				if (b.dir == DT_POS && b.dis > 0) {
					return DD_FALSE;
				}
			} else if (a.dis < 0) {
				if (b.dir == DT_POS) {
					return DD_FALSE;
				}
				if (b.dir == DT_NEG && a.dis > b.dis) {
					return DD_TRUE;
				}
			}
		} else if (b.dir == DT_DIS) { //a is not Dis,b is Dis
			/*
			If b > a is false, then b <= a, and a can not equal to b, so
			the only result is b < a.
			*/
			UINT s = DD_Gt(b, a);
			if (s == DD_TRUE) { return DD_FALSE; }
			else if (s == DD_FALSE) { return DD_TRUE; }
			else return s;
		} else if (a.dir == DT_POS && b.dir == DT_NEG && a.dis > b.dis) {
			return DD_TRUE;
		} else if (a.dir == DT_NEG && b.dir == DT_POS && a.dis < b.dis) {
			return DD_FALSE;
		}
	}
	return DD_UNK;
}


bool operator == (DD const& a, DD const& b)
{
	if (a.dir == DT_MISC && b.dir == DT_MISC) return true;
	return a.dir == b.dir && a.dis == b.dis;
}


bool operator != (DD const& a, DD const& b)
{
	if ((a.dir == DT_MISC) ^ (b.dir == DT_MISC)) return true;
	if ((a.dir == DT_MISC) && (b.dir == DT_MISC)) return false;
	return a.dir != b.dir || a.dis != b.dis;
}


bool operator < (DD const&, DD const&)
{
	ASSERT(0, ("utilize DD_Lt"));
	return false;
}


bool operator <= (DD const&, DD const&)
{
	ASSERT(0, ("utilize DD_Le"));
	return false;
}


bool operator > (DD const&, DD const&)
{
	ASSERT(0, ("utilize DD_Gt"));
	return false;
}


bool operator >= (DD const&, DD const&)
{
	ASSERT(0, ("utilize DD_Ge"));
	return false;
}


DD operator * (DD const& a, DD const& b)
{
	DD res;
	switch (a.dir) {
	case DT_DIS:
		switch (b.dir) {
		case DT_DIS: res.dir = DT_DIS; res.dis = a.dis * b.dis; break;
		case DT_POS:
			ASSERT(b.dis >= 0, ("min val of POS is 0"));
			res.dis = a.dis * b.dis;
			if (a.dis > 0) { res.dir = DT_POS; }
			else if (a.dis == 0) { res.dir = DT_DIS; }
			else { res.dir = DT_NEG; }
			break;
		case DT_NEG:
			ASSERT(b.dis <= 0, ("max val of NEG is 0"));
			res.dis = a.dis * b.dis;
			if (a.dis > 0) { res.dir = DT_NEG; }
			else if (a.dis == 0) { res.dir = DT_DIS; }
			else { res.dir = DT_POS; }
			break;
		case DT_MISC:
			res.dis = 0;
			if (a.dis == 0) { res.dir = DT_DIS; }
			else { res.dir = DT_MISC; }
			break;
		default: ASSERT(0, ("illegal operand"));
		}
		break;
	case DT_POS:
		ASSERT(a.dis >= 0, ("min of POS is 0"));
		res.dir = b.dir;
		res.dis = a.dis * b.dis;
		switch (b.dir) {
		case DT_DIS: return b * a;
		case DT_POS: ASSERT(b.dis >= 0, ("min of POS is 1")); break;
		case DT_NEG: ASSERT(b.dis <= 0, ("max of NEG is -1")); break;
		case DT_MISC: res.dis = 0; break;
		default: ASSERT(0, ("illegal operand"));
		}
		break;
	case DT_NEG:
		ASSERT(a.dis <= 0, ("max of NEG is 0"));
		res.dir = b.dir;
		res.dis = a.dis * b.dis;
		switch (b.dir) {
		case DT_DIS: return b * a;
		case DT_POS: ASSERT(b.dis >= 0, ("min val is 1")); break;
		case DT_NEG: ASSERT(b.dis <= 0, ("illegal bound")); break;
		case DT_MISC: res.dis = 0; break;
		default: ASSERT(0, ("illegal operand"));
		}
		break;
	case DT_MISC: res.dir = DT_MISC; res.dis = 0; break;
	default: ASSERT(0, ("illegal operand"));
	}
	return res;
}


DD operator / (DD const&, DD const&)
{
	ASSERT(0, ("NYI"));
	return DD(0);
}


DD operator + (DD const& a, DD const& b)
{
	DD res;
	if (a.dir == DT_DIS) {
		res.dis = a.dis + b.dis;
		res.dir = b.dir;
		if ((res.dis > 0 && res.dir == DT_NEG) ||
			(res.dis < 0 && res.dir == DT_POS)) {
			res.dir = DT_MISC;
			res.dis = 0;
		}
		return res;
	}
	if (b.dir == DT_DIS) {
		res.dis = a.dis + b.dis;
		res.dir = a.dir;
		if ((res.dis > 0 && res.dir == DT_NEG) ||
			(res.dis < 0 && res.dir == DT_POS)) {
			res.dir = DT_MISC;
			res.dis = 0;
		}
		return res;
	}
	if (a.dir == DT_MISC || b.dir == DT_MISC) {
		res.dir = DT_MISC;
		res.dis = 0;
		return res;
	}
	switch (a.dir) {
	case DT_POS:
		ASSERT(a.dis >= 0, ("illegal bound"));
		switch (b.dir) {
		case DT_POS:
			ASSERT(b.dis >= 0, ("illegal bound"));
			res.dis = a.dis + b.dis;
			res.dir = DT_POS;
			break;
		case DT_NEG:
			ASSERT(b.dis <= 0, ("illegal bound"));
			res.dis = 0;
			res.dir = DT_MISC;
			break;
		default: ASSERT(0, ("illegal operand"));
		}
		break;
	case DT_NEG:
		ASSERT(a.dis <= 0, ("illegal bound"));
		switch (b.dir) {
		case DT_POS:
			ASSERT(b.dis >= 1, ("illegal bound"));
			res.dis = 0;
			res.dir = DT_MISC;
			break;
		case DT_NEG:
			ASSERT(b.dis <= 0, ("illegal bound"));
			res.dis = a.dis + b.dis;
			res.dir = DT_NEG;
			break;
		default: ASSERT(0, ("illegal operand"));
		}
		break;
	default: ASSERT(0, ("illegal operand"));
	}
	return res;
}


//minus operation
DD operator - (DD const& a)
{
	DD res;
	res.dir = DT_MISC;
	switch (a.dir) {
	case DT_DIS: res.dir = DT_DIS; res.dis = -a.dis; break;
	case DT_POS: res.dir = DT_NEG; res.dis = -a.dis; break;
	case DT_NEG: res.dir = DT_POS; res.dis = -a.dis; break;
	case DT_MISC: res.dir = DT_MISC; res.dis = 0; break;
	default: ASSERT(0, ("illegal operand"));
	}
	return res;
}


//Subtration operation
DD operator - (DD const& a, DD const& b)
{
	return a + (-b);
}



//
//START DVECS
//
static void Init_VecE(Matrix<DD> * pbasis);
static void Dvecs_Dumpf_By_Handle(void const* pbasis, FILE * h);
static void Dvecs_Dumpf(void const* pbasis, CHAR const* name, bool is_del);
static void Dvecs_Dumps(void const* pbasis);
DVECS::DVECS()
{
	m_is_init = false;
	init();
	INHR i;
	i.hi = Init_VecE;
	i.hds = Dvecs_Dumps;
	i.hdf = Dvecs_Dumpf;
	i.hdfh = Dvecs_Dumpf_By_Handle;
	set_hook(&i);
}


DVECS::DVECS(DVECS const& m) : Matrix<DD>(m)
{
	m_is_init = false;
	init();
	INHR i;
	i.hi = Init_VecE;
	i.hds = Dvecs_Dumps;
	i.hdf = Dvecs_Dumpf;
	i.hdfh = Dvecs_Dumpf_By_Handle;
	set_hook(&i);
}


DVECS::DVECS(UINT row, UINT col)
{
	m_is_init = false;
	init();
	grow_all(row, col);
	INHR i;
	i.hi = Init_VecE;
	i.hds = Dvecs_Dumps;
	i.hdf = Dvecs_Dumpf;
	i.hdfh = Dvecs_Dumpf_By_Handle;
	set_hook(&i);
}


DVECS::~DVECS()
{
  	destroy();
}


void DVECS::init()
{
	if (m_is_init) return;
	m_is_init = true;
}


void DVECS::destroy()
{
	if (!m_is_init) return;
	m_is_init = false;
}


DVECS& DVECS::operator = (DVECS const& m)
{
	((Matrix<DD>*)this)->copy(*((Matrix<DD>*)&m));
	return *this;
}


DVECS& DVECS::operator = (RMat const& m)
{
	reinit(m.get_row_size(), m.get_col_size());
	for (UINT i = 0; i < m_row_size; i++) {
		for (UINT j = 0; j < m_col_size; j++) {
			ASSERT(m.get(i,j).den() == 1, ("dep element only be integer"));
			set(i, j, DD(m.get(i,j).num()));
		}
	}
	return *this;
}


DVECS& DVECS::operator = (INTMat const& m)
{
	reinit(m.get_row_size(), m.get_col_size());
	for (UINT i = 0; i < m_row_size; i++) {
		for (UINT j = 0; j < m_col_size; j++) {
			set(i, j, DD(m.get(i,j)));
		}
	}
	return *this;
}


/* Assignment of integer value.
'num': number of value
'...": value list, type is 'INT'
*/
void DVECS::sete(UINT num, ...)
{
	ASSERT(m_is_init, ("not yet initialize."));
	ASSERT(num <= m_col_size * m_row_size, ("set out of boundary."));
	if (num <= 0) {
		return;
	}
	INT *ptr = (INT*) (((BYTE*)(&num)) + sizeof(UINT));
	UINT i = 0;
	UINT row = 0, col = 0;
	while (i < num) {
		INT ddv = *ptr;
		set(row, col++, DD(ddv));
		if (col >= m_col_size) {
			row++;
			col = 0;
		}
		i++;
		ptr++; //stack growing down
	}
}



/* Assignment of value.
'num': number of value
'dd": value list, type is 'DD'
*/
void DVECS::setv(UINT num, Vector<DD> const& dd)
{
	ASSERT(m_is_init, ("not yet initialize."));
	ASSERT(num <= m_col_size * m_row_size, ("set out of boundary."));
	if (num <= 0) {
		return;
	}
	UINT i = 0;
	UINT row = 0, col = 0;
	while (i < num) {
		set(row, col++, dd.get(i));
		if (col >= m_col_size) {
			row++;
			col = 0;
		}
		i++;
	}
}


//Converting DVECs to RMat if all elements be rational.
bool DVECS::cvt_to(OUT RMat & r)
{
	ASSERT(m_is_init, ("not yet initialize."));
	r.reinit(get_row_size(), get_col_size());
	for (UINT i = 0; i < get_row_size(); i++) {
		for (UINT j = 0; j < get_col_size(); j++) {
			DD dd = get(i,  j);
			if (dd.dir == DT_DIS) {
				r.set(i, j, dd.dis);
			} else {
				r.clean();
				return false;
			}
		}
	}
	return true;
}
//END DVECS



//init vec element
static void Init_VecE(Matrix<DD> * pbasis)
{
	DD dd(DT_MISC);
	for (UINT i = 0; i < pbasis->get_row_size(); i++) {
		for (UINT j = 0; j < pbasis->get_col_size(); j++) {
			pbasis->set(i, j, dd);
		}
	}
}


static void Dvecs_Dumpf_By_Handle(void const* pbasis, FILE * h)
{
	static INT g_count = 0;
	ASSERT(h, ("dump file handle is NULL"));
	fprintf(h, "\nMATRIX dump id:%d\n", g_count++);

	//start
	CHAR buf[256];
	DVECS * pthis = (DVECS*)pbasis;
	for (UINT i = 0; i < pthis->get_row_size(); i++) {
		for (UINT j = 0; j < pthis->get_col_size(); j++) {
			DD dd = pthis->get(i, j);
			CHAR *blank="";
			if (dd.dir == DT_DIS) {
				sprintf(buf, "%-5d", dd.dis);
			} else {
				//Assuming that the value of dep-distance is maximum
				//range of no more than 999.
				switch (dd.dir) {
				case DT_POS:sprintf(buf, "%s%-3d", ">=", dd.dis);break;
				case DT_NEG:sprintf(buf, "%s%-3d", "<=", dd.dis);break;
				case DT_MISC:sprintf(buf, "%s%-3d", " *", dd.dis);break;
				default:ASSERT(0,("unknown dep type"));
				}
			}
			fprintf(h, "%s%s", buf, blank);
		}
		fprintf(h, "\n");
	}
	//end
	fprintf(h, "\n");
}


static void Dvecs_Dumpf(void const* pbasis, CHAR const* name, bool is_del)
{
	if (!name) {
		name = "matrix.tmp";
	}
	if (is_del) {
		unlink(name);
	}

	FILE * h = fopen(name, "a+");
	ASSERT(h, ("%s create failed!!!", name));
	Dvecs_Dumpf_By_Handle(pbasis, h);
	fclose(h);
}


static void Dvecs_Dumps(void const* pbasis)
{
	printf("\n");

	//start
	DVECS *pthis = (DVECS*)pbasis;
	CHAR buf[256];
	for (UINT i = 0; i < pthis->get_row_size(); i++) {
		for (UINT j = 0; j < pthis->get_col_size(); j++) {
			DD dd = pthis->get(i, j);
			CHAR *blank="";
			if (dd.dir == DT_DIS) {
				sprintf(buf, "%-5d", dd.dis);
			} else {
				//Assuming that the value of dep-distance is maximum
				//range of no more than 999.
				switch (dd.dir) {
				case DT_POS:sprintf(buf, "%s%-3d", ">=", dd.dis);break;
				case DT_NEG:sprintf(buf, "%s%-3d", "<=", dd.dis);break;
				case DT_MISC:sprintf(buf, "%s%-3d", " *", dd.dis);break;
				default:ASSERT(0,("unknown dep type"));
				}
			}
			printf("%s%s", buf, blank);
		}
		printf("\n");
	}
	//end
	printf("\n");
}


DVECS operator * (DVECS const& a, DVECS const& b)
{
	ASSERT(a.m_is_init && b.m_is_init, ("not yet initialize."));
	DVECS c;
	Matrix<DD> *cp = (Matrix<DD>*)&c;
	Matrix<DD> *ap = (Matrix<DD>*)&a;
	Matrix<DD> *bp = (Matrix<DD>*)&b;
	*cp = *ap * *bp;
	return c;
}


DVECS operator + (DVECS const& a, DVECS const& b)
{
	ASSERT(a.m_is_init && b.m_is_init, ("not yet initialize."));
	DVECS c;
	Matrix<DD> *cp = (Matrix<DD>*)&c;
	Matrix<DD> *ap = (Matrix<DD>*)&a;
	Matrix<DD> *bp = (Matrix<DD>*)&b;
	*cp = *ap + *bp;
	return c;
}


DVECS operator - (DVECS const& a, DVECS const& b)
{
	ASSERT(a.m_is_init && b.m_is_init, ("not yet initialize."));
	DVECS c;
	Matrix<DD> *cp = (Matrix<DD>*)&c;
	Matrix<DD> *ap = (Matrix<DD>*)&a;
	Matrix<DD> *bp = (Matrix<DD>*)&b;
	*cp = *ap - *bp;
	return c;
}


DVECS operator * (RMat const& a, DVECS const& b)
{
	ASSERT(a.is_init() && b.m_is_init, ("not yet initialize."));
	ASSERT(a.get_row_size() > 0 && a.get_col_size() > 0, ("invalid matrix"));
	ASSERT(b.m_row_size > 0 && b.m_col_size > 0, ("invalid matrix"));
	ASSERT(a.get_col_size() == b.m_row_size, ("invalid matrix type of mul"));

	DVECS c(a.get_row_size(), b.m_col_size);
	for (UINT i = 0; i < a.get_row_size(); i++) {
		for (UINT j = 0; j < b.m_col_size; j++) {
			DD tmp = 0;
			for (UINT k = 0; k < a.get_col_size(); k++) {
				ASSERT(a.get(i,k).den() == 1, ("only permit integer"));
				tmp = tmp + DD(a.get(i,k).num()) * b.get(k,j);
				if (tmp.dir == DT_MISC) {
					//* + * = *
					break;
				}
			}
			c.set(i,j,tmp);
		}
	}
	return c;

}


DVECS operator + (RMat const& a, DVECS const& b)
{
	ASSERT(a.is_init() && b.m_is_init, ("not yet initialize."));
	ASSERT(a.get_row_size() == b.m_row_size &&
			a.get_col_size() == b.m_col_size, ("invalid matrix type of mul"));

	DVECS c(a.get_row_size(), a.get_col_size());
	for (UINT i = 0; i < a.get_row_size(); i++) {
		for (UINT j = 0; j < a.get_col_size(); j++) {
			ASSERT(a.get(i,j).den() == 1, ("only permit integer"));
			c.set(i, j, DD(a.get(i,j).num()) + b.get(i,j));
		}
	}
	return c;
}


DVECS operator - (RMat const& a, DVECS const& b)
{
	ASSERT(a.is_init() && b.m_is_init, ("not yet initialize."));
	ASSERT(a.get_row_size() == b.m_row_size &&
			a.get_col_size() == b.m_col_size, ("invalid matrix type of mul"));

	DVECS c(a.get_row_size(), a.get_col_size());
	for (UINT i = 0; i < a.get_row_size(); i++) {
		for (UINT j = 0; j < a.get_col_size(); j++) {
			ASSERT(a.get(i,j).den() == 1, ("only permit integer"));
			c.set(i, j, DD(a.get(i,j).num()) - b.get(i,j));
		}
	}
	return c;
}
