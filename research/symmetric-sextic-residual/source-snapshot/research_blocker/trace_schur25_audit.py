#!/usr/bin/env python3
"""Independent exact polynomial audit of reduced contact Schur derivatives.

No solver is invoked. The generic quotient identities are checked over QQ in
49 formal coefficient variables. The instantiated bindings and every gradient
are checked as polynomial identities in all25 core variables at one exact
characteristic-zero base specialization, including all off-ideal row terms.
"""
from pathlib import Path
from functools import lru_cache
import hashlib, json, resource, sys, time
import flint

HERE=Path(__file__).resolve().parent


def locate(name,parents):
    for parent in parents:
        path=HERE.parent/parent/name
        if path.exists():return path
    raise FileNotFoundError(name)


def generic_audit(path):
    g=json.loads(path.read_text())
    ctx=flint.fmpq_mpoly_ctx.get(tuple(g['coefficient_variables']))
    variables=dict(zip(g['coefficient_variables'],ctx.gens()))
    parse=lambda x:flint.fmpq_mpoly(x.replace('**','^'),ctx)
    den=parse(g['D']);mu=[variables[f'mu{i}'] for i in range(5)]
    deltas=[1-k*mu[0]*mu[1] for k in (1,2,3)]
    assert den==deltas[0]*deltas[1]*deltas[2]
    Q={tuple(v['exponent']):parse(v['coefficient']) for v in g['Q2']}
    N={tuple(v['exponent']):parse(v['numerator']) for v in g['N']}
    free={tuple(v['exponent']):v for v in g['free_equations']}
    checked=0
    for i,e0 in enumerate(g['R_monomial_order']):
        e=tuple(e0);p=den*variables[f'R{i}']
        for m,c in Q.items():
            diff=tuple(a-b for a,b in zip(e,m))
            p-=c*N.get(diff,ctx.constant(0))
        if e not in free:assert not p
        else:
            entry=free[e];factor=ctx.constant(1)
            for d,k in zip(deltas,entry['divided_factor_powers']):factor*=d**k
            assert p==factor*parse(entry['normalized_polynomial'])
        checked+=1
    return {'generic_coefficient_variables':49,'exact_generic_row_identities':checked,
            'generic_denominator_factors_checked':True}


def evaluator(nodes,ctx,variables,overrides=None):
    overrides={} if overrides is None else overrides
    @lru_cache(None)
    def ev(k):
        if k in overrides:return overrides[k]
        op,d=nodes[k]['op'],nodes[k]['data']
        if op=='rational':return ctx.constant(flint.fmpq(d[0],d[1]))
        if op=='variable':return variables[d]
        if op=='add':return sum((ev(j) for j in d),ctx.constant(0))
        if op=='multiply':
            out=ctx.constant(1)
            for j in d:out*=ev(j)
            return out
        if op=='power':return ev(d[0])**d[1]
        if op=='inverse':
            poly=ev(d);assert poly.is_constant() and poly
            return ctx.constant(1/poly.leading_coefficient())
        raise ValueError(op)
    return ev


def main():
    started=time.monotonic()
    generic_base='--generic' in sys.argv
    resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
    generic_path=locate('contact_generic_g2_numerators.json',('research_trace','proof_attempt5'))
    point_path=locate('point_scaled_system.json',('research_memory','research_trace2','research_point_scaled','proof_attempt6'))
    reduced_path=HERE/'schur25_system.json'
    generic=generic_audit(generic_path)
    point=json.loads(point_path.read_text());reduced=json.loads(reduced_path.read_text())
    # These schema aliases are intentionally explicit; no source expressions
    # or gradient data are inferred from numerical samples.
    names=reduced['variable_order']
    roots=reduced['equation_nodes']
    jac=reduced['jacobian_matrix_nodes']
    numerator_nodes=reduced['quotient_numerator_nodes']
    denominator_node=reduced['quotient_denominator_node']
    factor_nodes=reduced['rowfactor_nodes']
    free_rows=reduced['free_row_indices'];pivot_rows=reduced['pivot_row_indices']
    assert len(names)==len(roots)==25 and len(numerator_nodes)==19
    assert names==[n for n in point['variable_order'] if not n.startswith('g2_')]
    assert free_rows==[i for i,e in enumerate(point['equation_monomial_order']) if not(e[0] and e[1])]
    assert sorted(free_rows+pivot_rows)==list(range(44))
    base={'lam':1,'r':2,'s':3}
    extra_names=['lam','r','s','inverse_ell'] if generic_base else []
    polynomial_names=names+extra_names
    ctx=flint.fmpq_mpoly_ctx.get(tuple(polynomial_names));zero=ctx.constant(0)
    values=dict(zip(polynomial_names,ctx.gens()))
    if not generic_base:values.update((k,ctx.constant(v)) for k,v in base.items())
    inverse_nodes=[]
    if generic_base:
        visited=set()
        def scan(k):
            if k in visited:return
            visited.add(k);op,d=reduced['scalar_nodes'][k]['op'],reduced['scalar_nodes'][k]['data']
            if op in ('add','multiply'):
                for j in d:scan(j)
            elif op=='power':scan(d[0])
            elif op=='inverse':inverse_nodes.append(k);scan(d)
        for root in roots+numerator_nodes+[denominator_node]+factor_nodes+point['equation_nodes']+[n for row in jac for n in row]:scan(root)
        assert len(inverse_nodes)==1
        @lru_cache(None)
        def dependencies(k):
            op,d=reduced['scalar_nodes'][k]['op'],reduced['scalar_nodes'][k]['data']
            if op=='variable':return frozenset([d])
            if op=='rational':return frozenset()
            if op in ('add','multiply'):return frozenset().union(*(dependencies(j) for j in d))
            if op=='power':return dependencies(d[0])
            if op=='inverse':return dependencies(d)
            raise ValueError(op)
        assert dependencies(inverse_nodes[0])==frozenset(['lam'])
    overrides={k:values['inverse_ell'] for k in inverse_nodes}
    ev=evaluator(reduced['scalar_nodes'],ctx,values,overrides)
    N=[ev(k) for k in numerator_nodes];D=ev(denominator_node)
    factors=[ev(k) for k in factor_nodes];F=[ev(k) for k in roots]
    # Extract the ORIGINAL44 rows as affine functions of the19 g2 variables.
    fullnames=point['variable_order'];full_polynomial_names=fullnames+extra_names
    fullctx=flint.fmpq_mpoly_ctx.get(tuple(full_polynomial_names))
    fullvalues=dict(zip(full_polynomial_names,fullctx.gens()))
    if not generic_base:fullvalues.update((k,fullctx.constant(v)) for k,v in base.items())
    full_eval=evaluator(point['scalar_nodes'],fullctx,fullvalues,{k:fullvalues['inverse_ell'] for k in inverse_nodes})
    full=[full_eval(k) for k in point['equation_nodes']]
    yindices=[full_polynomial_names.index(n) for n in polynomial_names]
    zindices=[fullnames.index(f'g2_{j}') for j in range(19)]
    raw=[];matrix=[]
    for poly in full:
        c={};rows=[{} for _ in range(19)]
        for e,v in poly.to_dict().items():
            ze=[e[j] for j in zindices];assert sum(ze)<=1
            ye=tuple(e[j] for j in yindices)
            target=rows[ze.index(1)] if sum(ze) else c
            target[ye]=target.get(ye,flint.fmpq(0))+v
        raw.append(ctx.from_dict(c));matrix.append([ctx.from_dict(row) for row in rows])
    free_index={i:j for j,i in enumerate(free_rows)}
    for i in range(44):
        clear=D*raw[i]+sum((c*n for c,n in zip(matrix[i],N)),zero)
        if i in free_index:
            j=free_index[i];assert clear==factors[j]*F[j],('row',i)
        else:assert not clear,('pivot',i)
    # Compare ALL emitted reduced derivatives with independent FLINT formal
    # differentiation, not the circuit differentiator used by the builder.
    gradient=[]
    for i,(poly,row) in enumerate(zip(F,jac)):
        derivatives=[]
        for k,(name,node) in enumerate(zip(names,row)):
            q=poly.derivative(name);assert q==ev(node),('gradient',i,k)
            derivatives.append(q)
        gradient.append(derivatives)
    # Off-ideal chain rule. Merely taking a minor or freezing g2 fails these
    # identities; so does omitting the derivative of a row-clearing unit.
    D2=D*D;Dy=[D.derivative(name) for name in names]
    Ny=[[n.derivative(name) for name in names] for n in N]
    fy=[[f.derivative(name) for name in names] for f in factors]
    chain_checked=0
    for i in range(44):
        nonzero=[(j,a) for j,a in enumerate(matrix[i]) if a]
        for k,name in enumerate(names):
            lhs=D2*raw[i].derivative(name)
            for j,a in nonzero:
                lhs+=D*a.derivative(name)*N[j]+a*(D*Ny[j][k]-N[j]*Dy[k])
            if i in free_index:
                j=free_index[i]
                rhs=D*factors[j]*gradient[j][k]+(D*fy[j][k]-factors[j]*Dy[k])*F[j]
                assert lhs==rhs,('off_ideal_chain',i,k)
            else:assert not lhs,('pivot_chain',i,k)
            chain_checked+=1
    receipt={
        'status':'PASS',**generic,
        'exact_QQ_base_specialization':None if generic_base else {'lambda':1,'r':2,'s':3},
        'generic_base_parameters_left_symbolic':generic_base,
        'generic_scalar_ring':'QQ[25 core variables,lambda,r,s,inverse_ell]' if generic_base else None,
        'inverse_ell_treated_as_independent_scalar':generic_base,
        'core_polynomial_variables':25,'original_row_bindings_checked':44,
        'pivot_reconstruction_identities_checked':19,
        'reduced_row_bindings_checked':25,
        'exact_reduced_gradient_identities_checked':625,
        'exact_off_ideal_chain_rule_identities_checked':chain_checked,
        'off_ideal_identity':'D^2*S_ik=D*rowfactor_i*Jred_ik+(D*d_k(rowfactor_i)-rowfactor_i*d_k(D))*F_i',
        'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (generic_path,point_path,reduced_path)},
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':('All44 source bindings,625 derivatives and1100 off-ideal chain rules are exact polynomial identities with all25 core variables and lambda,r,s left symbolic. The sole inverse of a lambda-only scalar is treated as an independent formal coefficient, so these identities specialize to the required rational function field.' if generic_base else 'The generic49-parameter quotient identities are exact. All instantiated equations and gradients are polynomial identities in25 variables over QQ at the stated base specialization, not root samples. General-base binding additionally follows from the builder substitution and chain-rule construction; this independent replay does not claim to expand every generic base coefficient.'),
        'fixed_rhs_good_proved':False,'quotient_basis_completed':False,'source_trace_proved':False,
        'full_certificate_proved':False,'seconds':time.monotonic()-started,
        'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    receipt_name='trace_schur25_generic_receipt.json' if generic_base else 'trace_schur25_audit_receipt.json'
    (HERE/receipt_name).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
