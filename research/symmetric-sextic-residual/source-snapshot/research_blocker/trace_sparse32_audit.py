#!/usr/bin/env python3
"""Independent generic audit of the denominator-free sparse32 reduction.

Reads the original46 equations and extracts their affine dependence on the
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
    sparse_path=HERE/'sparse32_system.json'
    old=json.loads(point_path.read_text());new=json.loads(sparse_path.read_text())
    fullnames=old['uneliminated_incidence_variable_order'];names=new['variable_order'];zvars=new['quotient_variable_order']
    original_roots=old['uneliminated_incidence_equation_nodes']
    assert len(names)==32 and len(zvars)==14
    assert names==[n for n in fullnames if n not in zvars]
    free=new['free_row_indices'];pivots=new['pivot_row_indices']
    assert free==[i for i,e in enumerate(old['equation_monomial_order']) if e[0]%2==0]+[44,45]
    assert pivots==[i for i,e in enumerate(old['equation_monomial_order']) if e[0]%2==1]
    assert sorted(free+pivots)==list(range(46))
    rowperm=free+pivots;colperm=[fullnames.index(n) for n in names+zvars]
    inversions=lambda p:sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
    assert (inversions(rowperm),inversions(colperm))==(175,63)
    assert new['jacobian_sign']==1
    nodes=new['scalar_nodes'];visited=set();inverse=[]
    def scan(k):
        if k in visited:return
        visited.add(k);op,d=nodes[k]['op'],nodes[k]['data']
        if op in ('add','multiply'):
            for j in d:scan(j)
        elif op=='power':scan(d[0])
        elif op=='inverse':inverse.append(k);scan(d)
    roots=new['equation_nodes']+new['quotient_reconstruction_nodes']+original_roots+old['equation_nodes']
    roots += [k for row in new['jacobian_matrix_nodes'] for k in row]
    roots += [k for row in new['reconstruction_derivative_nodes'] for k in row]
    roots += list(new['small_open_nodes'].values())+list(old['small_open_nodes'].values())
    roots += new['small_open_equation_nodes']+old['small_open_equation_nodes']
    roots += list(old['eliminated_variable_nodes'].values())
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
    assert len(inverse)==2 and all(deps(k)==frozenset(['lam']) for k in inverse)
    assert list(new['small_open_nodes'])==list(old['small_open_nodes'])
    assert new['small_open_inverse_variables']==old['small_open_inverse_variables']
    extra=['lam','r','s','inverse_ell']+new['small_open_inverse_variables']
    fullctx=flint.fmpq_mpoly_ctx.get(tuple(fullnames+extra))
    fv=dict(zip(fullnames+extra,fullctx.gens()))
    full_eval=evaluator(nodes,fullctx,fv,{k:fv['inverse_ell'] for k in inverse})
    assert full_eval(nodes[inverse[0]]['data'])==full_eval(nodes[inverse[1]]['data'])
    H=[full_eval(i) for i in original_roots]
    ctx=flint.fmpq_mpoly_ctx.get(tuple(names+extra));v=dict(zip(names+extra,ctx.gens()))
    ev=evaluator(nodes,ctx,v,{k:v['inverse_ell'] for k in inverse});zero=ctx.constant(0)
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
    for i in range(46):
        reconstructed=raw[i]+sum((a*p for a,p in zip(matrix[i],phi)),zero)
        assert reconstructed==(F[free_index[i]] if i in free_index else zero)
    for f,row in zip(F,new['jacobian_matrix_nodes']):
        for name,node in zip(names,row):assert f.derivative(name)==ev(node)
    for f,row in zip(phi,new['reconstruction_derivative_nodes']):
        for name,node in zip(names,row):assert f.derivative(name)==ev(node)
    chain_count=0
    for i in range(46):
        entries=[(j,a) for j,a in enumerate(matrix[i]) if a]
        for name in names:
            lhs=raw[i].derivative(name)+sum((a.derivative(name)*phi[j]+a*phi[j].derivative(name) for j,a in entries),zero)
            rhs=F[free_index[i]].derivative(name) if i in free_index else zero
            assert lhs==rhs
            chain_count+=1
    # Independently substitute both original point pivots; do not use the
    # builder's stored point_binding_nodes or point_open_binding_nodes.
    point_sub=old['eliminated_variable_nodes']
    assert list(point_sub)==['mu0','A0']
    bound_values=dict(fv)
    for n,node in point_sub.items():bound_values[n]=full_eval(node)
    bound_eval=evaluator(nodes,fullctx,bound_values,{k:fv['inverse_ell'] for k in inverse})
    assert H[44]==fv['mu0']-full_eval(point_sub['mu0'])
    assert H[45]==fv['A0']-full_eval(point_sub['A0'])
    for a,b in zip(original_roots[:44],old['equation_nodes']):assert bound_eval(a)==full_eval(b)
    for key in old['small_open_nodes']:
        assert bound_eval(new['small_open_nodes'][key])==full_eval(old['small_open_nodes'][key])
    for key,inv,node in zip(new['small_open_nodes'],new['small_open_inverse_variables'],new['small_open_equation_nodes']):
        assert inv=='open_'+key
        assert full_eval(node)==fv[inv]*full_eval(new['small_open_nodes'][key])-1
    for a,b in zip(new['small_open_equation_nodes'],old['small_open_equation_nodes']):assert bound_eval(a)==full_eval(b)
    point_column_order=[n for n in fullnames if n not in point_sub]+list(point_sub)
    point_inversions=inversions([fullnames.index(n) for n in point_column_order])
    assert point_inversions==74
    degree=lambda f:max((sum(e[:32]) for e in f.to_dict()),default=-1)
    assert max(map(degree,phi))==2 and max(map(degree,F))==3
    receipt={'status':'PASS','coefficient_ring':'QQ[32 core variables,lambda,r,s,inverse_ell,6 open-inverse variables]',
        'all_base_parameters_symbolic':True,'only_lambda_scalar_inverse_abstracted':True,
        'identity_pivot_matrix_entries_checked':196,'identity_pivot_rows_checked':14,
        'syntactically_distinct_inverse_denominators_proved_equal':2,
        'original_row_reconstruction_identities_checked':46,
        'independent_reduced_gradient_identities_checked':1024,
        'independent_reconstruction_gradient_identities_checked':448,
        'off_ideal_chain_rule_identities_checked':chain_count,
        'point_scaled44_source_bindings_checked':44,
        'linear_point_equations_independently_checked':2,
        'original_open_factor_bindings_checked':6,
        'open_inverse_equation_bindings_checked':6,
        'row_permutation_inversions':175,'column_permutation_inversions':63,
        'point_elimination_column_inversions':point_inversions,
        'Jacobian_relation':'J32=J46=J44_point after the polynomial reconstructions; no extra unit factor.',
        'reconstruction_degree':2,'reduced_core_degree':3,
        'no_extra_localization_required':True,
        'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (point_path,sparse_path)},
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'helper_sha256':hashlib.sha256((HERE/'trace_schur25_audit.py').read_bytes()).hexdigest(),
        'scope':'Exact generic polynomial identities, not numerical point controls. This proves the original/reduced equation and derivative binding. It does not certify a fixed RHS, a completed quotient basis, or a source trace.',
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,'source_trace_proved':False,
        'full_certificate_proved':False,'seconds':time.monotonic()-started,
        'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    (HERE/'trace_sparse32_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
