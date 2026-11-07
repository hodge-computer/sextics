#!/usr/bin/env python3
"""Independent generic audit of the denominator-free sparse30 reduction.

Reads the original44 equations and extracts their affine dependence on the
14 eliminated variables independently of the reduction builder. All base
parameters remain symbolic; no root samples or solver are used.
"""
from pathlib import Path
from functools import lru_cache
import hashlib, json, resource, time
import flint
from trace_schur25_audit import evaluator, locate

HERE=Path(__file__).resolve().parent


def main():
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(1024*1024**2,1024*1024**2))
    point_path=locate('point_scaled_system.json',('research_memory','research_trace2','research_point_scaled','proof_attempt6'))
    sparse_path=HERE/'sparse30_system.json'
    old=json.loads(point_path.read_text());new=json.loads(sparse_path.read_text())
    fullnames=old['variable_order'];names=new['variable_order'];zvars=new['quotient_variable_order']
    assert len(names)==30 and len(zvars)==14
    assert names==[n for n in fullnames if n not in zvars]
    free=new['free_row_indices'];pivots=new['pivot_row_indices']
    assert free==[i for i,e in enumerate(old['equation_monomial_order']) if e[0]%2==0]
    assert pivots==[i for i,e in enumerate(old['equation_monomial_order']) if e[0]%2==1]
    assert sorted(free+pivots)==list(range(44))
    rowperm=free+pivots;colperm=[fullnames.index(n) for n in names+zvars]
    inversions=lambda p:sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
    assert (inversions(rowperm),inversions(colperm))==(147,63)
    assert new['jacobian_sign']==1
    nodes=new['scalar_nodes'];visited=set();inverse=[]
    def scan(k):
        if k in visited:return
        visited.add(k);op,d=nodes[k]['op'],nodes[k]['data']
        if op in ('add','multiply'):
            for j in d:scan(j)
        elif op=='power':scan(d[0])
        elif op=='inverse':inverse.append(k);scan(d)
    roots=new['equation_nodes']+new['quotient_reconstruction_nodes']+old['equation_nodes']
    roots += [k for row in new['jacobian_matrix_nodes'] for k in row]
    roots += [k for row in new['reconstruction_derivative_nodes'] for k in row]
    roots += [t['coefficient_node'] for poly in new['parity_polynomials'].values() for t in poly]
    for root in roots:scan(root)
    @lru_cache(None)
    def deps(k):
        op,d=nodes[k]['op'],nodes[k]['data']
        if op=='rational':return frozenset()
        if op=='variable':return frozenset([d])
        if op in ('add','multiply'):return frozenset().union(*(deps(j) for j in d))
        if op=='power':return deps(d[0])
        if op=='inverse':return deps(d)
        raise ValueError(op)
    assert len(inverse)==1 and deps(inverse[0])==frozenset(['lam'])
    extra=['lam','r','s','inverse_ell']
    fullctx=flint.fmpq_mpoly_ctx.get(tuple(fullnames+extra))
    fv=dict(zip(fullnames+extra,fullctx.gens()))
    full_eval=evaluator(old['scalar_nodes'],fullctx,fv,{inverse[0]:fv['inverse_ell']})
    H=[full_eval(i) for i in old['equation_nodes']]
    ctx=flint.fmpq_mpoly_ctx.get(tuple(names+extra));v=dict(zip(names+extra,ctx.gens()))
    ev=evaluator(nodes,ctx,v,{inverse[0]:v['inverse_ell']});zero=ctx.constant(0)
    phi=[ev(k) for k in new['quotient_reconstruction_nodes']]
    F=[ev(k) for k in new['equation_nodes']]
    ys=[(fullnames+extra).index(n) for n in names+extra]
    zs=[fullnames.index(n) for n in zvars]
    raw=[];matrix=[]
    for f in H:
        c={};a=[{} for _ in zvars]
        for e,coefficient in f.to_dict().items():
            ze=[e[j] for j in zs];assert sum(ze)<=1
            ye=tuple(e[j] for j in ys)
            target=a[ze.index(1)] if sum(ze) else c
            target[ye]=target.get(ye,flint.fmpq(0))+coefficient
        raw.append(ctx.from_dict(c));matrix.append([ctx.from_dict(p) for p in a])
    for k,i in enumerate(pivots):
        assert matrix[i]==[ctx.constant(int(j==k)) for j in range(14)]
        assert raw[i]==-phi[k]
    free_index={i:k for k,i in enumerate(free)}
    for i in range(44):
        reconstructed=raw[i]+sum((a*p for a,p in zip(matrix[i],phi)),zero)
        assert reconstructed==(F[free_index[i]] if i in free_index else zero)
    for f,row in zip(F,new['jacobian_matrix_nodes']):
        for name,node in zip(names,row):assert f.derivative(name)==ev(node)
    for f,row in zip(phi,new['reconstruction_derivative_nodes']):
        for name,node in zip(names,row):assert f.derivative(name)==ev(node)
    chain_count=0
    for i in range(44):
        entries=[(j,a) for j,a in enumerate(matrix[i]) if a]
        for name in names:
            lhs=raw[i].derivative(name)+sum((a.derivative(name)*phi[j]+a*phi[j].derivative(name) for j,a in entries),zero)
            rhs=F[free_index[i]].derivative(name) if i in free_index else zero
            assert lhs==rhs
            chain_count+=1
    # Independently multiply the five ambient parity polynomials.
    parity={key:{tuple(t['exponent']):ev(t['coefficient_node']) for t in terms}
            for key,terms in new['parity_polynomials'].items()}
    def polyadd(*polys):
        out={}
        for p in polys:
            for e,c in p.items():out[e]=out.get(e,zero)+c
        return {e:c for e,c in out.items() if c}
    def polymul(p,q):
        out={}
        for e,a in p.items():
            for f,b in q.items():
                ef=tuple(x+y for x,y in zip(e,f));out[ef]=out.get(ef,zero)+a*b
        return {e:c for e,c in out.items() if c}
    negate=lambda p:{e:-c for e,c in p.items()}
    qdet=polyadd({(2,2,0,0):ctx.constant(1)},negate(polymul(parity['M'],parity['M'])))
    formula=polyadd(parity['R_even'],negate(polymul(parity['M'],parity['T'])),polymul(qdet,parity['O']))
    assert formula=={tuple(old['equation_monomial_order'][i]):F[k] for k,i in enumerate(free)}
    degree=lambda f:max((sum(e[:30]) for e in f.to_dict()),default=-1)
    assert max(map(degree,phi))==2 and max(map(degree,F))==3
    receipt={'status':'PASS','coefficient_ring':'QQ[30 core variables,lambda,r,s,inverse_ell]',
        'all_base_parameters_symbolic':True,'only_lambda_scalar_inverse_abstracted':True,
        'identity_pivot_matrix_entries_checked':196,'identity_pivot_rows_checked':14,
        'original_row_reconstruction_identities_checked':44,
        'independent_reduced_gradient_identities_checked':900,
        'independent_reconstruction_gradient_identities_checked':420,
        'off_ideal_chain_rule_identities_checked':chain_count,
        'independent_parity_polynomial_multiplication_checked':True,
        'row_permutation_inversions':147,'column_permutation_inversions':63,
        'Jacobian_relation':'J30=J44 after the14 polynomial reconstructions; no extra unit factor.',
        'reconstruction_degree':2,'reduced_core_degree':3,
        'no_extra_localization_required':True,
        'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (point_path,sparse_path)},
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'helper_sha256':hashlib.sha256((HERE/'trace_schur25_audit.py').read_bytes()).hexdigest(),
        'scope':'Exact generic polynomial identities, not numerical point controls. This proves the original/reduced equation and derivative binding. It does not certify a fixed RHS, a completed quotient basis, or a source trace.',
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,'source_trace_proved':False,
        'full_certificate_proved':False,'seconds':time.monotonic()-started,
        'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    (HERE/'trace_sparse30_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
