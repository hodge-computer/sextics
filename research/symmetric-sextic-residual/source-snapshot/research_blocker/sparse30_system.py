#!/usr/bin/env python3
"""Polynomial elimination of fourteen contact coefficients without denominators.

Write Q2=ab+M and g2=E+ab*O, where M,E,O have even a,b exponents.
Writing the remaining sextic as R_even+ab*T, the odd equations give
E=-M*O-T.  The thirty remaining equations are the coefficients of
R_even-M*T+(a^2*b^2-M^2)*O.  The actual T is only quadratic in the
contact coefficients, so this elimination preserves cubic degree.

The fixed RHS systems are solver inputs, not completed finite quotients.
No source trace or full certificate is claimed.
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
    path=W.POINT/'point_scaled_system.json'
    source=json.loads(path.read_text())
    C=W.DifferentialCircuit(source['scalar_nodes']);P=W.S.Polynomials(C)
    full_names=source['variable_order'];full_roots=source['equation_nodes']
    exponents=source['equation_monomial_order']
    g2={C.nodes[t['coefficient_node']]['data']:tuple(t['exponent'])
        for t in source['scaled_polynomials']['g2']}
    eliminated=[n for n in full_names if n in g2 and g2[n][0]%2==0]
    retained=[n for n in full_names if n in g2 and g2[n][0]%2==1]
    assert len(eliminated)==14 and len(retained)==5
    assert all(g2[n][1]%2==g2[n][0]%2 for n in g2)
    pivot_rows=[exponents.index([e[0]+1,e[1]+1,e[2],e[3]])
                for n in eliminated for e in [g2[n]]]
    free_rows=[i for i,e in enumerate(exponents) if e[0]%2==0]
    assert len(free_rows)==30 and sorted(free_rows+pivot_rows)==list(range(44))
    names=[n for n in full_names if n not in eliminated]
    # Every selected pivot row has coefficient one on its own eliminated
    # variable and zero on all thirteen others.  This is independently checked.
    stripped=C.substitute([full_roots[i] for i in pivot_rows],{n:C.zero for n in eliminated})
    phi=[C.neg(root) for root in stripped]
    substitutions=dict(zip(eliminated,phi))
    equations=C.substitute([full_roots[i] for i in free_rows],substitutions)
    matrix=[[C.derivative(f,n) for n in names] for f in equations]
    reconstruction_derivatives=[[C.derivative(f,n) for n in names] for f in phi]

    # Independently specified polynomial parity formula, with exact source
    # coefficient nodes.  Its coefficient equality is audited over QQ below.
    Rroots=C.substitute(full_roots,{n:C.zero for n in g2})
    R_even={tuple(exponents[i]):Rroots[i] for i in free_rows}
    T={tuple([exponents[i][0]-1,exponents[i][1]-1]+exponents[i][2:]):Rroots[i]
       for i in pivot_rows}
    M={tuple(t['exponent']):C.substitute([t['coefficient_node']],source['eliminated_variable_nodes'])[0]
       for t in source['scaled_polynomials']['Q2'] if tuple(t['exponent'])!=(1,1,0,0)}
    O={tuple([g2[n][0]-1,g2[n][1]-1]+list(g2[n][2:])):C.var(n) for n in retained}
    detpoly=P.add({(2,2,0,0):C.one},P.neg(P.mul(M,M)))
    reduced=P.add(R_even,P.neg(P.mul(M,T)),P.mul(detpoly,O))
    assert all(e[0]%2==e[1]%2==0 for e in reduced)
    rp=free_rows+pivot_rows
    row_swaps=sum(rp[i]>rp[j] for i in range(44) for j in range(i+1,44))
    cp=[full_names.index(n) for n in names+eliminated]
    column_swaps=sum(cp[i]>cp[j] for i in range(44) for j in range(i+1,44))
    sign=(-1)**(row_swaps+column_swaps)
    rng=random.Random(20261107)
    b=[rng.randrange(1,37) for _ in names];c=[rng.randrange(1,37) for _ in names]
    packet={
        'schema':'symmetric-sparse30-polynomial-contact-system-v1',
        'coefficient_field':'Q(lambda,r,s)',
        'scalar_nodes':C.nodes,'variable_order':names,'equation_nodes':equations,
        'jacobian_matrix_nodes':matrix,
        'full_source_variable_order':full_names,'full_source_equation_nodes':full_roots,
        'source_equation_monomial_order':exponents,
        'free_row_indices':free_rows,'pivot_row_indices':pivot_rows,
        'quotient_variable_order':eliminated,'retained_g2_variables':retained,
        'quotient_reconstruction_nodes':phi,'quotient_numerator_nodes':phi,
        'quotient_denominator_node':C.one,'rowfactor_nodes':[C.one]*30,
        'reconstruction_derivative_nodes':reconstruction_derivatives,
        'parity_polynomials':{key:P.encode(poly) for key,poly in
            [('M',M),('T',T),('O',O),('R_even',R_even),('reduced',reduced)]},
        'small_open_nodes':source['small_open_nodes'],
        'small_open_inverse_variables':source['small_open_inverse_variables'],
        'small_open_equation_nodes':source['small_open_equation_nodes'],
        'polynomial_identity':'Q2=ab+M; g2=E+ab*O; R=R_even+ab*T; H_odd/(ab)=E+M*O+T; E=-M*O-T; H_even=R_even-M*T+(a^2*b^2-M^2)*O.',
        'exact_row_identity':'H_pivot(x,phi)=0; H_free(x,phi)=F(x); pivot Jacobian in the fourteen eliminated coordinates is the identity matrix.',
        'scheme_equivalence':'A polynomial ring quotient isomorphism, valid without any localization. It also preserves the six existing small opens, which involve none of the eliminated g2 variables.',
        'row_permutation_inversions':row_swaps,'column_permutation_inversions':column_swaps,
        'jacobian_sign':sign,'determinant_relation':f'J30={sign}*J44 on the equation ideal after reconstruction',
        'fixed_rhs':{'prime':37,'seed':20261107,'b':b,'c':c,'genericity_proved':False},
        'fixed_rhs_acceptance':'A verified zero-dimensional augmented quotient with unrestricted auxiliary vectors certifies the same J-localized core algebra. No fixed-RHS equivalence is asserted before this gate.',
        'no_additional_open_assumptions':True,'remaining_full_opens':['delta9','D10'],
        'source_hashes':{'point_scaled_system.json':sha256(path.read_bytes()).hexdigest()},
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,
        'source_trace_proved':False,'full_certificate_proved':False,
    }
    return packet,source


def characteristic_zero_audit(packet,source):
    import flint
    nodes=packet['scalar_nodes'];names=packet['variable_order']
    full_names=packet['full_source_variable_order'];eliminated=packet['quotient_variable_order']
    all_roots=packet['equation_nodes']+packet['quotient_reconstruction_nodes']+packet['full_source_equation_nodes']
    all_roots += [x for row in packet['jacobian_matrix_nodes'] for x in row]
    all_roots += [x for row in packet['reconstruction_derivative_nodes'] for x in row]
    all_roots += [t['coefficient_node'] for p in packet['parity_polynomials'].values() for t in p]
    visited=set();inverse_nodes=[]
    @lru_cache(None)
    def dependencies(i):
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':return frozenset()
        if op=='variable':return frozenset([d])
        if op in ('add','multiply'):return frozenset().union(*(dependencies(j) for j in d))
        if op=='power':return dependencies(d[0])
        if op=='inverse':return dependencies(d)
        raise ValueError(op)
    def scan(i):
        if i in visited:return
        visited.add(i);op,d=nodes[i]['op'],nodes[i]['data']
        if op in ('add','multiply'):
            for j in d:scan(j)
        elif op=='power':scan(d[0])
        elif op=='inverse':inverse_nodes.append(i);scan(d)
    for root in all_roots:scan(root)
    assert len(inverse_nodes)==1 and dependencies(inverse_nodes[0])==frozenset(['lam'])
    extra=['lam','r','s','inverse_ell']
    ctx=flint.fmpq_mpoly_ctx.get(tuple(full_names+extra));V=dict(zip(full_names+extra,ctx.gens()))
    zero=ctx.constant(0)
    @lru_cache(None)
    def ev(i):
        if i in inverse_nodes:return V['inverse_ell']
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':return ctx.constant(flint.fmpq(*d))
        if op=='variable':return V[d]
        if op=='add':return sum((ev(j) for j in d),zero)
        if op=='multiply':
            out=ctx.constant(1)
            for j in d:out*=ev(j)
            return out
        if op=='power':return ev(d[0])**d[1]
        raise ValueError(op)
    H=[ev(i) for i in packet['full_source_equation_nodes']]
    phi=[ev(i) for i in packet['quotient_reconstruction_nodes']]
    free=packet['free_row_indices'];pivots=packet['pivot_row_indices']
    index={n:j for j,n in enumerate(full_names)}
    for k,(i,n,p) in enumerate(zip(pivots,eliminated,phi)):
        assert H[i]==V[n]-p,('pivot_row',i)
        for m in eliminated:assert not p.derivative(m)
    F=[ev(i) for i in packet['equation_nodes']]
    matrices=[]
    for k,i in enumerate(free):
        coeffs=[H[i].derivative(n) for n in eliminated]
        assert all(not a.derivative(n) for a in coeffs for n in eliminated)
        # This row operation proves the original and reduced ideals identical
        # after adjoining the reconstruction equations, globally, not at roots.
        transformed=H[i]-sum((a*H[j] for a,j in zip(coeffs,pivots)),zero)
        assert transformed==F[k],('free_row',i)
        assert all(not F[k].derivative(n) for n in eliminated)
        matrices.append(coeffs)
    gradients=0;chains=0
    for k,(f,row) in enumerate(zip(F,packet['jacobian_matrix_nodes'])):
        for n,node in zip(names,row):
            derivative=f.derivative(n);assert derivative==ev(node),('gradient',k,n)
            gradients+=1
    for k,(p,row) in enumerate(zip(phi,packet['reconstruction_derivative_nodes'])):
        for n,node in zip(names,row):assert p.derivative(n)==ev(node)
    # Off-ideal chain identity for every original row.  For a row H=c+A*y,
    # substitute y=phi only after differentiating: d(c+A*phi)=dc+dA*phi+A*dphi.
    free_index={i:k for k,i in enumerate(free)}
    for i,h in enumerate(H):
        a=[h.derivative(n) for n in eliminated]
        c=h-sum((coef*V[n] for coef,n in zip(a,eliminated)),zero)
        for n in names:
            lhs=c.derivative(n)+sum((coef.derivative(n)*p+coef*p.derivative(n) for coef,p in zip(a,phi)),zero)
            rhs=F[free_index[i]].derivative(n) if i in free_index else zero
            assert lhs==rhs,('chain',i,n);chains+=1
    reduced={tuple(t['exponent']):ev(t['coefficient_node']) for t in packet['parity_polynomials']['reduced']}
    assert set(reduced)==set(tuple(packet['source_equation_monomial_order'][i]) for i in free)
    for i,f in zip(free,F):assert f==reduced[tuple(packet['source_equation_monomial_order'][i])]
    core_indices=[index[n] for n in names]
    degree=lambda p:max((sum(e[j] for j in core_indices) for e in p.to_dict()),default=-1)
    assert max(map(degree,phi))<=2 and max(map(degree,F))<=3
    return {'status':'PASS','scalar_ring':'QQ[44 contact variables,lambda,r,s,inverse_ell]',
        'inverse_ell_treated_as_independent_scalar':True,'base_parameters_left_symbolic':True,
        'identity_pivot_rows_checked':14,'exact_free_row_operations_checked':30,
        'exact_reduced_derivatives_checked':gradients,'exact_reconstruction_derivatives_checked':420,
        'exact_off_ideal_chain_identities_checked':chains,'parity_formula_coefficients_checked':30,
        'maximum_reconstruction_degree':int(max(map(degree,phi))),
        'maximum_reduced_degree':int(max(map(degree,F))),
        'no_denominators_introduced':True,'no_additional_open_assumptions':True,
        'determinant_relation':packet['determinant_relation']}


def emit_modular(packet,count):
    n=len(packet['variable_order'])
    aux=[f'pv{i}' for i in range(n)] if count else []
    if count==2:aux += [f'pw{i}' for i in range(n)]
    names=packet['variable_order']+aux+packet['small_open_inverse_variables']
    ctx,V,ev,core=S25.evaluate_modular(packet,packet['equation_nodes'],names)
    matrix=[[f.derivative(j) for j in range(n)] for f in core]
    for row,nodes in zip(matrix,packet['jacobian_matrix_nodes']):
        for poly,node in zip(row,nodes):assert poly==ev(node)
    equations=list(core)
    if count:
        rhs_list=[('pv',packet['fixed_rhs']['b'])]
        if count==2:rhs_list += [('pw',packet['fixed_rhs']['c'])]
        for prefix,rhs in rhs_list:
            equations.extend(sum((f*V[f'{prefix}{j}'] for j,f in enumerate(row)),ctx.constant(0))-ctx.constant(rhs[i])
                             for i,row in enumerate(matrix))
    equations += [ev(i) for i in packet['small_open_equation_nodes']]
    assert len(names)==len(equations)==n*(count+1)+6
    tag=f'sparse30_witness_{count}rhs_p37' if count else 'sparse30_smallopens_p37'
    path=HERE/(tag+'.ms')
    path.write_text(','.join(names)+'\n37\n'+',\n'.join(map(str,equations))+'\n')
    receipt={'file':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),
        'variables':len(names),'equations':len(equations),'rhs_count':count,
        'core_variables':n,'core_equations':n,'inverse_variables':6,
        'core_terms':sum(map(len,core)),'total_terms':sum(map(len,equations)),
        'maximum_core_degree':int(max(f.total_degree() for f in core)),
        'maximum_input_degree':int(max(f.total_degree() for f in equations)),
        'all900_modular_gradient_polynomials_match_exact_DAG':True,
        'prime':37,'base':{'lam':1,'r':2,'s':3},'variable_order':names,
        'small_opens':list(packet['small_open_nodes']),'no_additional_open_assumptions':True,
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,
        'source_trace_proved':False,'full_certificate_proved':False}
    (HERE/(tag+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    started=time.monotonic();packet,source=build()
    audit=characteristic_zero_audit(packet,source)
    path=HERE/'sparse30_system.json';path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    outputs=[]
    for count in (0,1,2):
        receipt=emit_modular(packet,count);outputs.append(receipt)
        print(json.dumps({k:v for k,v in receipt.items() if k!='variable_order'}),flush=True)
    audit.update(packet_sha256=sha256(path.read_bytes()).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        derivative_builder_sha256=sha256((HERE/'jacobian_witness_system.py').read_bytes()).hexdigest(),
        modular_inputs=outputs,seconds=time.monotonic()-started,
        scope='Exact polynomial quotient reduction and generic characteristic-zero source/gradient identities. The emitted fixed-RHS systems have no completed quotient basis or trace evaluation.',
        fixed_rhs_equivalence_proved=False,quotient_basis_completed=False,
        source_trace_proved=False,full_certificate_proved=False)
    (HERE/'sparse30_system_receipt.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps({k:v for k,v in audit.items() if k!='modular_inputs'},indent=2),flush=True)


if __name__=='__main__':main()
