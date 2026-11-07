#!/usr/bin/env python3
"""Sparse cubic parity reduction retaining the two linear point equations.

Fourteen g2 coefficients are eliminated by an identity pivot block.  Keeping
mu0 and A0 avoids expanding their linear reconstructions into every cubic.
The resulting square32-variable system is polynomially equivalent to the
point-scaled44-variable system, and has the same required open factors.
"""
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import json
import random
import time
import jacobian_witness_system as W
import schur25_system as S25

HERE=Path(__file__).resolve().parent


def build():
    source_path=W.POINT/'point_scaled_system.json';source=json.loads(source_path.read_text())
    C=W.DifferentialCircuit(source['scalar_nodes'])
    full_names=source['uneliminated_incidence_variable_order']
    full_roots=source['uneliminated_incidence_equation_nodes']
    assert len(full_names)==len(full_roots)==46
    exps=source['equation_monomial_order']
    g2={C.nodes[t['coefficient_node']]['data']:tuple(t['exponent']) for t in source['scaled_polynomials']['g2']}
    eliminated=[n for n in full_names if n in g2 and g2[n][0]%2==0]
    retained=[n for n in full_names if n in g2 and g2[n][0]%2==1]
    pivots=[exps.index([g2[n][0]+1,g2[n][1]+1,*g2[n][2:]]) for n in eliminated]
    free=[i for i,e in enumerate(exps) if e[0]%2==0]+[44,45]
    assert len(eliminated)==14 and len(free)==32 and sorted(free+pivots)==list(range(46))
    names=[n for n in full_names if n not in eliminated]
    phi=[C.neg(i) for i in C.substitute([full_roots[j] for j in pivots],{n:C.zero for n in eliminated})]
    equations=C.substitute([full_roots[i] for i in free],dict(zip(eliminated,phi)))
    matrix=[[C.derivative(f,n) for n in names] for f in equations]
    recon_derivatives=[[C.derivative(f,n) for n in names] for f in phi]
    opens={f'delta{k}':C.sub(C.one,C.mul(C.const(k),C.var('mu0'),C.var('mu1'))) for k in (1,2,3)}
    opens.update({n:source['small_open_nodes'][n] for n in ('t','beta','Gw')})
    inverse_names=source['small_open_inverse_variables']
    open_eqs=[C.sub(C.mul(C.var(inv),node),C.one) for inv,node in zip(inverse_names,opens.values())]
    row_order=free+pivots;column_order=[full_names.index(n) for n in names+eliminated]
    inversions=lambda p:sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
    row_swaps,column_swaps=inversions(row_order),inversions(column_order)
    sign=(-1)**(row_swaps+column_swaps)
    point_sub=source['eliminated_variable_nodes']
    point_binding=C.substitute(full_roots[:44],point_sub)
    open_binding=C.substitute(list(opens.values()),point_sub)
    point_columns=[n for n in full_names if n not in point_sub]+list(point_sub)
    point_column_swaps=inversions([full_names.index(n) for n in point_columns])
    assert list(point_sub)==['mu0','A0'] and point_column_swaps==74
    rng=random.Random(20261107)
    return {'schema':'symmetric-sparse32-polynomial-contact-system-v1',
        'coefficient_field':'Q(lambda,r,s)','scalar_nodes':C.nodes,
        'variable_order':names,'equation_nodes':equations,'jacobian_matrix_nodes':matrix,
        'full_source_variable_order':full_names,'full_source_equation_nodes':full_roots,
        'source_equation_monomial_order':exps,'free_row_indices':free,'pivot_row_indices':pivots,
        'quotient_variable_order':eliminated,'retained_g2_variables':retained,
        'quotient_reconstruction_nodes':phi,'reconstruction_derivative_nodes':recon_derivatives,
        'small_open_nodes':opens,'small_open_inverse_variables':inverse_names,
        'small_open_equation_nodes':open_eqs,
        'point_eliminated_variable_nodes':point_sub,'point_binding_nodes':point_binding,
        'point_source_equation_nodes':source['equation_nodes'],
        'point_open_binding_nodes':open_binding,'point_source_open_nodes':source['small_open_nodes'],
        'polynomial_identity':'Q2=ab+M; g2=E+ab*O; H=R_even+ab*T+Q2*g2; E=-M*O-T; H_even=R_even-M*T+(a^2*b^2-M^2)*O. Retain q(1,r,1,s)=h(1,r,1,s)=0 as two linear equations.',
        'exact_row_identity':'H_pivot=y-phi(x), with identity pivot matrix; H_free minus the corresponding polynomial multiples of H_pivot equals the32 emitted equations.',
        'scheme_equivalence':'Polynomial quotient isomorphism, without new localization, to the original point-scaled44 equations. The six existing opens are preserved modulo the linear point equations.',
        'row_permutation_inversions':row_swaps,'column_permutation_inversions':column_swaps,
        'point_elimination_column_inversions':point_column_swaps,
        'jacobian_sign':sign,'determinant_relation':f'J32={sign}*J46 and J46=J44_point on the equation ideal, after the displayed polynomial reconstructions',
        'fixed_rhs':{'prime':37,'seed':20261107,'b':[rng.randrange(1,37) for _ in names],
                     'c':[rng.randrange(1,37) for _ in names],'genericity_proved':False},
        'fixed_rhs_acceptance':'A verified zero-dimensional augmented quotient with unrestricted auxiliary vectors certifies the same J-localized core algebra. This gate is not yet completed.',
        'no_additional_open_assumptions':True,'remaining_full_opens':['delta9','D10'],
        'source_hashes':{'point_scaled_system.json':sha256(source_path.read_bytes()).hexdigest()},
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,
        'source_trace_proved':False,'full_certificate_proved':False},source


def audit(packet):
    import flint
    nodes=packet['scalar_nodes'];names=packet['variable_order'];full_names=packet['full_source_variable_order']
    roots=packet['full_source_equation_nodes']+packet['equation_nodes']+packet['quotient_reconstruction_nodes']
    roots+=packet['point_binding_nodes']+packet['point_source_equation_nodes']
    roots+=packet['point_open_binding_nodes']+list(packet['point_source_open_nodes'].values())
    roots += [n for row in packet['jacobian_matrix_nodes']+packet['reconstruction_derivative_nodes'] for n in row]
    visited=set();inverse_nodes=[]
    @lru_cache(None)
    def dependencies(k):
        op,d=nodes[k]['op'],nodes[k]['data']
        if op=='variable':return frozenset([d])
        if op=='rational':return frozenset()
        if op in ('add','multiply'):return frozenset().union(*(dependencies(i) for i in d))
        if op=='power':return dependencies(d[0])
        if op=='inverse':return dependencies(d)
        raise ValueError(op)
    def scan(k):
        if k in visited:return
        visited.add(k);op,d=nodes[k]['op'],nodes[k]['data']
        if op in ('add','multiply'):
            for i in d:scan(i)
        elif op=='power':scan(d[0])
        elif op=='inverse':inverse_nodes.append(k);scan(d)
    for k in roots:scan(k)
    assert inverse_nodes and all(dependencies(k)==frozenset(['lam']) for k in inverse_nodes)
    extra=['lam','r','s','inverse_ell'];ctx=flint.fmpq_mpoly_ctx.get(tuple(full_names+extra))
    V=dict(zip(full_names+extra,ctx.gens()));zero=ctx.constant(0)
    @lru_cache(None)
    def ev(k):
        if k in inverse_nodes:return V['inverse_ell']
        op,d=nodes[k]['op'],nodes[k]['data']
        if op=='rational':return ctx.constant(flint.fmpq(*d))
        if op=='variable':return V[d]
        if op=='add':return sum((ev(i) for i in d),zero)
        if op=='multiply':
            result=ctx.constant(1)
            for i in d:result*=ev(i)
            return result
        if op=='power':return ev(d[0])**d[1]
        raise ValueError(op)
    # The original and substituted source circuits use two syntactic forms
    # of the same lambda-only denominator.  Verify equality before sharing
    # a single independent inverse_ell coefficient in the polynomial audit.
    assert all(ev(nodes[k]['data'])==ev(nodes[inverse_nodes[0]]['data']) for k in inverse_nodes)
    H=[ev(i) for i in packet['full_source_equation_nodes']]
    F=[ev(i) for i in packet['equation_nodes']]
    phi=[ev(i) for i in packet['quotient_reconstruction_nodes']]
    eliminated=packet['quotient_variable_order'];pivots=packet['pivot_row_indices'];free=packet['free_row_indices']
    for row,name,p in zip(pivots,eliminated,phi):
        assert H[row]==V[name]-p
        assert all(not p.derivative(n) for n in eliminated)
    for i,f in zip(free,F):
        coeffs=[H[i].derivative(n) for n in eliminated]
        assert all(not a.derivative(n) for a in coeffs for n in eliminated)
        assert H[i]-sum((a*H[j] for a,j in zip(coeffs,pivots)),zero)==f
    gradients=0;recon_gradients=0
    for f,row in zip(F,packet['jacobian_matrix_nodes']):
        for name,node in zip(names,row):assert f.derivative(name)==ev(node);gradients+=1
    for p,row in zip(phi,packet['reconstruction_derivative_nodes']):
        for name,node in zip(names,row):assert p.derivative(name)==ev(node);recon_gradients+=1
    free_index={i:k for k,i in enumerate(free)};chains=0
    for i,h in enumerate(H):
        coefficients=[h.derivative(n) for n in eliminated]
        constant=h-sum((a*V[n] for a,n in zip(coefficients,eliminated)),zero)
        for name in names:
            lhs=constant.derivative(name)+sum((a.derivative(name)*p+a*p.derivative(name) for a,p in zip(coefficients,phi)),zero)
            rhs=F[free_index[i]].derivative(name) if i in free_index else zero
            assert lhs==rhs;chains+=1
    for a,b in zip(packet['point_binding_nodes'],packet['point_source_equation_nodes']):assert ev(a)==ev(b)
    for a,b in zip(packet['point_open_binding_nodes'],packet['point_source_open_nodes'].values()):assert ev(a)==ev(b)
    assert H[44]==V['mu0']-ev(packet['point_eliminated_variable_nodes']['mu0'])
    assert H[45]==V['A0']-ev(packet['point_eliminated_variable_nodes']['A0'])
    indices=[full_names.index(n) for n in names]
    degree=lambda p:max((sum(e[j] for j in indices) for e in p.to_dict()),default=-1)
    assert max(map(degree,phi))<=2 and max(map(degree,F))<=3
    return {'status':'PASS','scalar_ring':'QQ[46 contact variables,lambda,r,s,inverse_ell]',
        'base_parameters_left_symbolic':True,'inverse_ell_treated_as_independent_scalar':True,
        'syntactic_inverse_denominators_identified_exactly':len(inverse_nodes),
        'identity_pivot_rows_checked':14,'exact_free_row_operations_checked':32,
        'exact_reduced_derivatives_checked':gradients,'exact_reconstruction_derivatives_checked':recon_gradients,
        'exact_off_ideal_chain_identities_checked':chains,
        'point_scaled_source_bindings_checked':44,'linear_point_equations_checked':2,
        'original_open_bindings_checked':6,'maximum_reconstruction_degree':int(max(map(degree,phi))),
        'maximum_reduced_degree':int(max(map(degree,F))),
        'no_denominators_introduced':True,'no_additional_open_assumptions':True,
        'determinant_relation':packet['determinant_relation']}


def emit(packet,count):
    n=len(packet['variable_order']);aux=[]
    if count:aux += [f'pv{i}' for i in range(n)]
    if count==2:aux += [f'pw{i}' for i in range(n)]
    names=packet['variable_order']+aux+packet['small_open_inverse_variables']
    ctx,V,ev,core=S25.evaluate_modular(packet,packet['equation_nodes'],names)
    matrix=[[f.derivative(j) for j in range(n)] for f in core]
    for row,stored in zip(matrix,packet['jacobian_matrix_nodes']):
        for f,node in zip(row,stored):assert f==ev(node)
    equations=list(core)
    if count:
        vectors=[('pv',packet['fixed_rhs']['b'])]+([('pw',packet['fixed_rhs']['c'])] if count==2 else [])
        for prefix,rhs in vectors:
            equations += [sum((a*V[f'{prefix}{j}'] for j,a in enumerate(row)),ctx.constant(0))-ctx.constant(rhs[i]) for i,row in enumerate(matrix)]
    equations += [ev(i) for i in packet['small_open_equation_nodes']]
    assert len(names)==len(equations)==n*(count+1)+6
    tag=f'sparse32_witness_{count}rhs_p37' if count else 'sparse32_smallopens_p37'
    path=HERE/(tag+'.ms');path.write_text(','.join(names)+'\n37\n'+',\n'.join(map(str,equations))+'\n')
    receipt={'file':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),
        'variables':len(names),'equations':len(equations),'rhs_count':count,'core_variables':n,
        'core_equations':n,'inverse_variables':6,'core_terms':sum(map(len,core)),
        'total_terms':sum(map(len,equations)),'maximum_core_degree':int(max(f.total_degree() for f in core)),
        'maximum_input_degree':int(max(f.total_degree() for f in equations)),
        'all1024_modular_gradient_polynomials_match_exact_DAG':True,
        'prime':37,'base':{'lam':1,'r':2,'s':3},'variable_order':names,
        'small_opens':list(packet['small_open_nodes']),'no_additional_open_assumptions':True,
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,
        'source_trace_proved':False,'full_certificate_proved':False}
    (HERE/(tag+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    started=time.monotonic();packet,source=build()
    path=HERE/'sparse32_system.json';path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    inputs=[]
    for count in (0,1,2):
        receipt=emit(packet,count);inputs.append(receipt)
        print(json.dumps({k:v for k,v in receipt.items() if k!='variable_order'}),flush=True)
    receipt=audit(packet)
    receipt.update(packet_sha256=sha256(path.read_bytes()).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        derivative_builder_sha256=sha256((HERE/'jacobian_witness_system.py').read_bytes()).hexdigest(),
        modular_inputs=inputs,seconds=time.monotonic()-started,
        scope='Exact generic characteristic-zero polynomial reduction, source binding and chain rules. No complete quotient basis or trace value has been computed.',
        fixed_rhs_equivalence_proved=False,quotient_basis_completed=False,
        source_trace_proved=False,full_certificate_proved=False)
    (HERE/'sparse32_system_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='modular_inputs'},indent=2),flush=True)


if __name__=='__main__':main()
