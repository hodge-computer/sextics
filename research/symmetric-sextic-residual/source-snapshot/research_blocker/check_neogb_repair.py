#!/usr/bin/env python3
"""Compare complete original/patched/audited bases with independent SymPy bases."""
from pathlib import Path
import hashlib,json,time
import sympy as S
from neogb_solver import NativeF4

HERE=Path(__file__).resolve().parent
def canon(fs,p):
    return sorted(tuple(sorted((e,int(c)%p) for e,c in f.items() if int(c)%p)) for f in fs)
def main():
    libs={name:NativeF4(HERE/'vendor'/('libneogb_'+name+'.so'))
          for name in ['original','compact','compact_audit']}
    x,y,z=S.symbols('x y z')
    cases=[('quadratic',(x,y),[x*x+y*y-1,x-y],37),
           ('nonreduced',(x,y),[x*x,x*y,y*y],101),
           ('empty',(x,y),[x*x,y-x,x*y-1,x*y],37),
           ('positive_dimension',(x,y,z),[x*y-z*z,x*x-y*z],101),
           ('mixed_cubic',(x,y,z),[x*x+y*z+1,y*y+x*z+2,z*z+x*y+3],65537),
           ('degree_fall',(x,y,z),[x*x*y+x*z+y,y*y*z+y*x+z,z*z*x+z*y+x],1073741827)]
    receipt=[]
    for name,variables,expressions,p in cases:
        inputs=[{e:int(c)%p for e,c in S.Poly(f,*variables,modulus=p).terms()} for f in expressions]
        reference=S.groebner(expressions,*variables,modulus=p,order='grevlex')
        reference=canon([dict(f.terms()) for f in reference.polys],p)
        runs={}
        for libname,lib in libs.items():
            meta,basis=lib.solve(inputs,len(variables),p,pairs=2,reset=1)
            assert canon(basis,p)==reference,(name,libname)
            runs[libname]=meta
        # The disabled option must really disable compaction; interval2 must
        # not be silently treated as interval1.
        off,basis=libs['compact'].solve(inputs,len(variables),p,pairs=2,reset=0)
        assert canon(basis,p)==reference
        assert off['compaction']['hc_compact_calls']==0
        every2,basis=libs['compact'].solve(inputs,len(variables),p,pairs=2,reset=2)
        assert canon(basis,p)==reference
        assert every2['compaction']['hc_compact_calls']<=runs['compact']['compaction']['hc_compact_calls']
        receipt.append({'case':name,'prime':p,'independent_complete_basis_agrees':True,
                        'runs':runs,'disabled_calls':0,'every_two':every2})
    out={'status':'PASS','scope':'Complete small-system bases independently checked with SymPy; audited native build compares every retained exponent vector exactly before/after compaction.',
         'cases':receipt,'input_target_solved':False,
         'patch_sha256':hashlib.sha256((HERE/'msolve_compact_hash.patch').read_bytes()).hexdigest()}
    (HERE/'neogb_repair_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':main()
