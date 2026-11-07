#!/usr/bin/env python3
"""Bounded modular quotient experiment for the ACTUAL contact incidence.

Reads the adjacent full original-target scalar circuit. A completed basis for
the unsaturated ideal is only preliminary: its full regular open, generic
flatness, the multiplication operands and their traces still must be checked.
An incomplete Buchberger run proves nothing about quotient degree or traces.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import hashlib
import json
import resource
import time
import flint
from finite_flint_groebner import FlintGB,sanity

HERE=Path(__file__).resolve().parent

def quotient_eliminate(ctx,variables,raw,exponents):
    """Eliminate all 19 quotient coefficients; check every pivot exactly.

    The common denominator is theta5*theta3=(1-z)(1-3z)(1-2z).
    The three blocks for c,d degrees 0,2,4 have tridiagonal sizes 5,3,1.
    """
    zero=ctx.constant(0);one=ctx.constant(1)
    mu=[variables[f'mu{i}'] for i in range(5)];z=mu[0]*mu[1]
    theta=[one,one]
    for k in range(2,6):theta.append(theta[-1]-z*theta[-2])
    den=theta[5]*theta[3]
    assert den==(1-z)*(1-2*z)*(1-3*z)
    R=dict(zip(map(tuple,exponents),[-h for h in raw]));Ns={}
    Q={(2,0,0,0):mu[0],(1,1,0,0):one,(0,2,0,0):mu[1],
       (0,0,2,0):mu[2],(0,0,1,1):mu[3],(0,0,0,2):mu[4]}
    S={e:v for e,v in Q.items() if e[2]+e[3]}
    minus=lambda e,f:tuple(a-b for a,b in zip(e,f))
    for cddegree in [0,2,4]:
        n=5-cddegree
        for ce in range(cddegree+1):
            de=cddegree-ce
            rhs=[]
            for i in range(n):
                e=(i+1,n-i,ce,de)
                rhs.append(R.get(e,zero)*den-sum((v*Ns.get(minus(e,f),zero) for f,v in S.items()),zero))
            for i in range(n):
                value=zero
                for j in range(n):
                    if i<=j:adj=(-1)**(i+j)*mu[1]**(j-i)*theta[i]*theta[n-j-1]
                    else:adj=(-1)**(i+j)*mu[0]**(i-j)*theta[j]*theta[n-i-1]
                    value+=adj*rhs[j]
                quo,rem=divmod(value,theta[n]);assert not rem
                Ns[(i,n-1-i,ce,de)]=quo
    assert len(Ns)==19
    equations=[];pivots=0
    for e in map(tuple,exponents):
        E=R.get(e,zero)*den-sum((v*Ns.get(minus(e,f),zero) for f,v in Q.items()),zero)
        if e[0] and e[1]:assert not E;pivots+=1
        else:
            for factor in (1-z,1-2*z,1-3*z):
                while E:
                    q,remainder=divmod(E,factor)
                    if remainder:break
                    E=q
            equations.append(E)
    assert pivots==19 and len(equations)==25
    return equations

def system(p,lam,r,s,eliminate_point=False,opens=False,order='degrevlex',alpha_resultant=False,variable_order='contact',branch='full',eliminate_quotient=False,ab_free=False):
    path=HERE/'finite_input_global_residue.json'
    d=json.loads(path.read_text());source_sha=hashlib.sha256(path.read_bytes()).hexdigest();names=d['incidence_variable_order'][:]
    if ab_free:
        assert alpha_resultant
        path2=HERE/'finite_input_alpha_elimination.json';extension=json.loads(path2.read_text())
        assert extension['scalar_nodes'][:len(d['scalar_nodes'])]==d['scalar_nodes']
        d['scalar_nodes']=extension['scalar_nodes'];source_sha=hashlib.sha256(path2.read_bytes()).hexdigest()
    if eliminate_quotient:
        assert opens,'Cleared quotient equations require the Delta open'
        names=[v for v in names if not v.startswith('g2_')]
    if eliminate_point:names=[v for v in names if v not in ['mu0','A0']]
    removed_alpha=alpha_resultant or branch!='full'
    if removed_alpha:
        assert not eliminate_point
        names=[v for v in names if v!='alpha']
    if alpha_resultant:
        assert branch=='full'
        names+=['invbn']
    if branch=='q2zero':names=[v for v in names if v not in ['mu0','mu2']]
    if branch=='bnzero':names+=['invq2']
    if opens:
        names+=['invdelta1','invdelta2','invdelta3']
        if not removed_alpha:names+=['invalpha']
        elif alpha_resultant:names+=['invan']
    if variable_order=='quotient_first':
        names=[v for v in names if v.startswith('g2_')]+[v for v in names if not v.startswith('g2_')]
    elif variable_order=='reverse':names=list(reversed(names))
    ctx=flint.nmod_mpoly_ctx.get(tuple(names),p,order)
    variables=dict(zip(names,ctx.gens()))
    variables.update(lam=ctx.constant(lam),r=ctx.constant(r),s=ctx.constant(s))
    if eliminate_quotient:variables.update((f'g2_{i}',ctx.constant(0)) for i in range(19))
    if branch=='q2zero':
        variables['mu0']=-r-variables['mu1']*r*r
        variables['mu2']=-s*variables['mu3']-s*s*variables['mu4']
    if eliminate_point:
        z=variables['alpha'];a=[variables[f'A{i}'] for i in range(1,8)];b=[variables[f'B{i}'] for i in range(8)]
        variables['mu0']=-r-variables['mu1']*r*r-z*z*(variables['mu2']+variables['mu3']*s+variables['mu4']*s*s)
        variables['A0']=-(a[0]*r**3+z*z*(a[1]+s*a[2]+s*s*a[3]+r*a[4]+r*s*a[5]+r*s*s*a[6])
                           +z*(b[0]+s*b[1]+r*r*b[2]+r*r*s*b[3])
                           +z**3*(b[4]+s*b[5]+s*s*b[6]+s**3*b[7]))
    @lru_cache(None)
    def ev(k):
        n=d['scalar_nodes'][k];op,v=n['op'],n['data']
        if op=='rational':return ctx.constant(v[0]*pow(v[1],-1,p)%p)
        if op=='variable':return variables[v]
        if op=='add':return sum(map(ev,v),ctx.constant(0))
        if op=='multiply':
            z=ctx.constant(1)
            for k in v:z*=ev(k)
            return z
        if op=='power':return ev(v[0])**v[1]
        if op=='inverse':
            poly=ev(v);terms=poly.to_dict();assert len(terms)==1 and next(iter(terms))==(0,)*len(names)
            return ctx.constant(pow(int(next(iter(terms.values()))),-1,p))
        raise ValueError(op)
    polys=[ev(k) for k in d['incidence_equation_nodes'][:44]]
    if eliminate_quotient:polys=quotient_eliminate(ctx,variables,polys,d['contact_equation_monomial_order'])
    if not removed_alpha:polys += [ev(k) for k in d['incidence_equation_nodes'][44:]]
    if removed_alpha:
        q0=r+variables['mu0']+variables['mu1']*r*r
        q2=variables['mu2']+s*variables['mu3']+s*s*variables['mu4']
        aa=[variables[f'A{i}'] for i in range(8)];bb=[variables[f'B{i}'] for i in range(8)]
        a0=aa[0]+aa[1]*r**3
        a2=aa[2]+s*aa[3]+s*s*aa[4]+r*aa[5]+r*s*aa[6]+r*s*s*aa[7]
        b0=bb[0]+s*bb[1]+r*r*bb[2]+r*r*s*bb[3]
        b2=bb[4]+s*bb[5]+s*s*bb[6]+s**3*bb[7]
        an=q2*a0-q0*a2;bn=q2*b0-q0*b2
        if alpha_resultant:
            pointpoly=ev(extension['coefficient_nodes']['G3']) if ab_free else q2*an*an+q0*bn*bn
            polys += [pointpoly,variables['invbn']*bn-1]
        elif branch=='bnzero':polys += [an,bn,variables['invq2']*q2-1]
        else:assert branch=='q2zero' and not q0 and not q2
    if eliminate_point:
        assert not polys[-1] and not polys[-2]
        polys=polys[:-2]
    if opens:
        zz=variables['mu0']*variables['mu1']
        polys += [variables[f'invdelta{k}']*(1-k*zz)-1 for k in (1,2,3)]
        if not removed_alpha:polys += [variables['invalpha']*variables['alpha']-1]
        elif alpha_resultant:polys += [variables['invan']*an-1]
    return names,polys,source_sha

def staircase(lms,nvars,limit=1000000):
    def multiple(a,b):return all(x>=y for x,y in zip(a,b))
    if any(not any(e) for e in lms):return []
    bounds=[]
    for j in range(nvars):
        pure=[e[j] for e in lms if e[j] and sum(bool(x) for x in e)==1]
        if not pure:return None
        bounds.append(min(pure))
    base={(0,)*nvars};todo=list(base)
    while todo:
        e=todo.pop()
        for j in range(nvars):
            f=list(e);f[j]+=1;f=tuple(f)
            if f in base or any(multiple(f,g) for g in lms):continue
            base.add(f);todo.append(f)
            if len(base)>limit:raise RuntimeError('standard monomial limit reached')
    return sorted(base)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prime',type=int,default=37)
    ap.add_argument('--lam',type=int,default=1);ap.add_argument('--r',type=int,default=2);ap.add_argument('--s',type=int,default=3)
    ap.add_argument('--point-elimination',action='store_true');ap.add_argument('--opens',action='store_true')
    ap.add_argument('--alpha-resultant',action='store_true')
    ap.add_argument('--branch',choices=['full','bnzero','q2zero'],default='full')
    ap.add_argument('--quotient-elimination',action='store_true');ap.add_argument('--ab-free',action='store_true')
    ap.add_argument('--variable-order',default='contact',choices=['contact','quotient_first','reverse'])
    ap.add_argument('--order',default='degrevlex',choices=['lex','deglex','degrevlex'])
    ap.add_argument('--ideal-limit',type=int,default=200);ap.add_argument('--term-limit',type=int,default=3000)
    ap.add_argument('--tag',default='37_initial');args=ap.parse_args()
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    sanity()
    start=time.monotonic();names,polys,sha=system(args.prime,args.lam,args.r,args.s,args.point_elimination,args.opens,args.order,args.alpha_resultant,args.variable_order,args.branch,args.quotient_elimination,args.ab_free)
    receipt={'parameters':vars(args),'source_sha256':sha,'variables':len(names),'equations':len(polys),
             'input_terms':sum(len(f) for f in polys),'max_input_degree':int(max(f.total_degree() for f in polys)),
             'method':'FLINT 3.6.0 bounded native Buchberger','sanity_check':'PASS',
             'full_regularity_localization_included':False,'generic_flatness_proved':False,'traces_computed':False}
    if args.alpha_resultant:receipt['extra_open']='bN != 0; omitted locus is NOT discarded in the target algebra'
    equations=[str(f) for f in polys]
    (HERE/f'finite_system_{args.tag}.json').write_text(json.dumps({'names':names,'prime':args.prime,'equations':equations},separators=(',',':'))+'\n')
    print(json.dumps({'phase':'input_ready',**receipt}),flush=True)
    ring=FlintGB(names,args.prime,args.order)
    try:result=ring.run(equations,args.ideal_limit,args.term_limit)
    finally:ring.close()
    if result['completed']:
        bs=staircase(result['leading_monomials'],len(names))
        result['zero_dimensional']=bs is not None
        if bs is not None:result['quotient_dimension']=len(bs)
        (HERE/f'finite_basis_{args.tag}.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
        result={k:v for k,v in result.items() if k not in ['reduced_basis','leading_monomials']}
    receipt.update(result);receipt['seconds']=time.monotonic()-start
    receipt['scope']='Specialized modular experiment only. No generic trace identity follows from this computation.'
    (HERE/f'finite_groebner_{args.tag}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
