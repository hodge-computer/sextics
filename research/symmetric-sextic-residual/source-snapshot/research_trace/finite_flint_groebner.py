#!/usr/bin/env python3
"""Small ctypes adapter to the installed FLINT 3.6.0 bounded Buchberger API.

No CAS is installed or downloaded. The layouts and signatures below are the
public FLINT 3.6.0 headers (fmpz_mod_types.h, mpoly_types.h,
fmpz_mod_mpoly.h and flint.h). The adapter is restricted to that ABI.
The adapter checks the version and a known ideal before doing research work.
FLINT's limits return an incomplete generating set, not a Groebner basis.
"""
from pathlib import Path
import ctypes as C
import flint
import json
import sys

L=C.c_long; U=C.c_ulong; P=C.c_void_p
class Nmod(C.Structure):
    _fields_=[('n',U),('ninv',U),('norm',U)]
class ModCtx(C.Structure):
    _fields_=[('n',L),('add_fxn',P),('sub_fxn',P),('mul_fxn',P),
              ('mod',Nmod),('n_limbs',U*3),('ninv_limbs',U*3),('ninv_huge',P)]
class MonoCtx(C.Structure):
    _fields_=[('nvars',L),('nfields',L),('ord',C.c_int),('deg',C.c_int),
              ('rev',C.c_int),('words',L*64),('fixbits',C.c_ubyte*64)]
class Ctx(C.Structure):
    _fields_=[('minfo',MonoCtx),('ffinfo',ModCtx)]
class Poly(C.Structure):
    _fields_=[('coeffs',C.POINTER(L)),('exps',C.POINTER(U)),('length',L),
              ('bits',U),('coeffs_alloc',L),('exps_alloc',L)]
class Vec(C.Structure):
    _fields_=[('p',C.POINTER(Poly)),('alloc',L),('length',L)]

class FlintGB:
    def __init__(self,names,prime,order='degrevlex'):
        assert flint.__FLINT_VERSION__=='3.6.0', 'ABI adapter is pinned to FLINT 3.6.0'
        assert C.sizeof(L)==8 and C.sizeof(Poly)==48
        libs=list((Path(flint.__file__).resolve().parent.parent/'python_flint.libs').glob('libflint*.so*'))
        assert len(libs)==1
        self.lib=C.CDLL(str(libs[0]));self.names=tuple(names);self.prime=prime
        self.x=(C.c_char_p*len(names))(*(s.encode() for s in names))
        self.ctx=Ctx();self.vectors=[]
        def bind(name,args,restype=None):
            f=getattr(self.lib,name);f.argtypes=args;f.restype=restype;return f
        self.ctx_init=bind('fmpz_mod_mpoly_ctx_init',[P,L,C.c_int,P])
        self.ctx_clear=bind('fmpz_mod_mpoly_ctx_clear',[P])
        self.vi=bind('fmpz_mod_mpoly_vec_init',[P,L,P]);self.vc=bind('fmpz_mod_mpoly_vec_clear',[P,P])
        self.parse=bind('fmpz_mod_mpoly_set_str_pretty',[P,C.c_char_p,P,P],C.c_int)
        self.pretty=bind('fmpz_mod_mpoly_get_str_pretty',[P,P,P],P)
        self.free=bind('flint_free',[P])
        self.buchberger=bind('fmpz_mod_mpoly_buchberger_naive_with_limits',[P,P,L,L,P],C.c_int)
        self.check=bind('fmpz_mod_mpoly_vec_is_groebner',[P,P,P],C.c_int)
        self.autoreduce=bind('fmpz_mod_mpoly_vec_autoreduction_groebner',[P,P,P])
        self.termexp=bind('fmpz_mod_mpoly_get_term_exp_ui',[P,P,L,P])
        self.degree=bind('fmpz_mod_mpoly_total_degree_si',[P,P],L)
        modulus=L(prime)
        self.ctx_init(C.byref(self.ctx),len(names),{'lex':0,'deglex':1,'degrevlex':2}[order],C.byref(modulus))
        assert self.ctx.minfo.nvars==len(names) and self.ctx.ffinfo.n==prime
    def vec(self,strings=()):
        v=Vec();self.vi(C.byref(v),len(strings),C.byref(self.ctx));self.vectors.append(v)
        for i,s in enumerate(strings):
            ret=self.parse(C.byref(v.p[i]),s.encode(),self.x,C.byref(self.ctx))
            assert ret==0,(i,s[:80],ret)
        return v
    def strs(self,v):
        out=[]
        for i in range(v.length):
            p=self.pretty(C.byref(v.p[i]),self.x,C.byref(self.ctx))
            out.append(C.string_at(p).decode());self.free(p)
        return out
    def leading(self,v):
        result=[]
        for i in range(v.length):
            assert v.p[i].length
            exp=(U*len(self.names))()
            self.termexp(exp,C.byref(v.p[i]),0,C.byref(self.ctx));result.append(tuple(exp))
        return result
    def run(self,strings,ideal_limit=1000,term_limit=10000,check=True):
        F=self.vec(strings);G=self.vec()
        success=bool(self.buchberger(C.byref(G),C.byref(F),ideal_limit,term_limit,C.byref(self.ctx)))
        result={'completed':success,'generators':G.length,'max_terms':max((G.p[i].length for i in range(G.length)),default=0),
                'max_total_degree':max((self.degree(C.byref(G.p[i]),C.byref(self.ctx)) for i in range(G.length)),default=0)}
        if success:
            if check:assert self.check(C.byref(G),C.byref(F),C.byref(self.ctx))==1
            H=self.vec();self.autoreduce(C.byref(H),C.byref(G),C.byref(self.ctx))
            result.update(reduced_basis=self.strs(H),leading_monomials=self.leading(H),reduced_length=H.length)
        return result
    def close(self):
        for v in reversed(self.vectors):self.vc(C.byref(v),C.byref(self.ctx))
        self.vectors=[];self.ctx_clear(C.byref(self.ctx))

def sanity():
    ring=FlintGB(('x','y'),37)
    try:
        r=ring.run(['x^2-y','x*y-1'])
        assert r['completed']
        assert {s.replace(' ','') for s in r['reduced_basis']}=={'x^2+36*y','x*y+36','y^2+36*x'},r
        return r
    finally:ring.close()

if __name__=='__main__':print(json.dumps(sanity(),indent=2))
