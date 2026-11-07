#!/usr/bin/env python3
"""Exact 19-variable quotient elimination and 25-variable Jacobian witnesses.

The generic quotient numerators are instantiated by a ring homomorphism.
The reduced equations have the same Delta-localized scheme as the full44
point-scaled equations.  No other component or open is removed.  The emitted
fixed RHS systems still require a completed zero-dimensional quotient.
"""
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import ast
import json
import random
import time
import jacobian_witness_system as W

HERE=Path(__file__).resolve().parent
POINT=W.POINT
for candidate in (HERE.parent/'research_trace',HERE.parent/'proof_attempt5'):
    if (candidate/'contact_generic_g2_numerators.json').exists():
        GENERIC=candidate/'contact_generic_g2_numerators.json';break
else:raise RuntimeError('Cannot locate the independently audited generic g2 numerator packet')


def parse_polynomial(text,variables,constant,add,subtract,multiply,power,negate):
    def rec(n):
        if isinstance(n,ast.Name):return variables[n.id]
        if isinstance(n,ast.Constant) and type(n.value) is int:return constant(n.value)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return negate(rec(n.operand))
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return add(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Sub):return subtract(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Mult):return multiply(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Pow):
                assert isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0
                return power(rec(n.left),n.right.value)
        raise ValueError('Unexpected syntax in a polynomial coefficient witness')
    return rec(ast.parse(text,mode='eval').body)


def generic_audit(witness):
    from sympy.polys.rings import ring
    from sympy.polys.domains import QQ
    R,*xs=ring(','.join(witness['coefficient_variables']),QQ);V=dict(zip(witness['coefficient_variables'],xs))
    parse=lambda text:parse_polynomial(text,V,R,lambda a,b:a+b,lambda a,b:a-b,lambda a,b:a*b,lambda a,n:a**n,lambda a:-a)
    D=parse(witness['D']);z=V['mu0']*V['mu1'];factors=[1-z,1-2*z,1-3*z]
    assert D==factors[0]*factors[1]*factors[2]
    Q={tuple(t['exponent']):parse(t['coefficient']) for t in witness['Q2']}
    N={tuple(t['exponent']):parse(t['numerator']) for t in witness['N']}
    free={tuple(t['exponent']):t for t in witness['free_equations']};rowchecks=0
    for i,e0 in enumerate(witness['R_monomial_order']):
        e=tuple(e0)
        error=D*V[f'R{i}']-sum((q*N.get(tuple(a-b for a,b in zip(e,f)),R.zero) for f,q in Q.items()),R.zero)
        if e[0] and e[1]:assert error==0
        else:
            entry=free[e];factor=R.one
            for d,n in zip(factors,entry['divided_factor_powers']):factor*=d**n
            assert error==factor*parse(entry['normalized_polynomial'])
        rowchecks+=1
    return {'generic_characteristic_zero_rows_verified':rowchecks,'generic_numerators':len(N),
            'coefficient_ring':'QQ[mu0,...,mu4,R0,...,R43]'}


def build():
    path=POINT/'point_scaled_system.json';source=json.loads(path.read_text());witness=json.loads(GENERIC.read_text())
    generic_receipt=generic_audit(witness)
    C=W.DifferentialCircuit(source['scalar_nodes'])
    full_names=source['variable_order'];ynames=[n for n in full_names if n.startswith('g2_')]
    names=[n for n in full_names if n not in ynames];assert len(names)==25 and len(ynames)==19
    exponents=source['equation_monomial_order'];assert exponents==witness['R_monomial_order']
    full_roots=source['equation_nodes'];H0=C.substitute(full_roots,{n:C.zero for n in ynames})
    replacements={f'mu{i}':source['eliminated_variable_nodes']['mu0'] if i==0 else C.var(f'mu{i}') for i in range(5)}
    replacements.update({f'R{i}':C.neg(node) for i,node in enumerate(H0)})
    parse=lambda text:parse_polynomial(text,replacements,C.const,C.add,C.sub,C.mul,C.power,C.neg)
    D=parse(witness['D']);delta=[source['small_open_nodes'][f'delta{i}'] for i in (1,2,3)]
    g2_names={tuple(term['exponent']):C.nodes[term['coefficient_node']]['data']
              for term in source['scaled_polynomials']['g2']}
    numerator_by_name={g2_names[tuple(entry['exponent'])]:parse(entry['numerator']) for entry in witness['N']}
    N=[numerator_by_name[n] for n in ynames];inverseD=C.node('inverse',D)
    phi=[C.mul(n,inverseD) for n in N]
    free_indices=[i for i,e in enumerate(exponents) if not(e[0] and e[1])]
    pivot_indices=[i for i,e in enumerate(exponents) if e[0] and e[1]]
    free_entries={tuple(e['exponent']):e for e in witness['free_equations']}
    equations=[];factors=[];powers=[]
    for i in free_indices:
        entry=free_entries[tuple(exponents[i])]
        equations.append(C.neg(parse(entry['normalized_polynomial'])))
        powers.append(entry['divided_factor_powers'])
        factors.append(C.mul(*(C.power(d,k) for d,k in zip(delta,entry['divided_factor_powers']))))
    matrix=[[C.derivative(eq,n) for n in names] for eq in equations]
    q2={tuple(term['exponent']):C.substitute([term['coefficient_node']],source['eliminated_variable_nodes'])[0]
        for term in source['scaled_polynomials']['Q2']}
    g2_exponents={v:k for k,v in g2_names.items()}
    M=[[q2.get(tuple(a-b for a,b in zip(exponents[i],g2_exponents[n])),C.zero) for n in ynames] for i in pivot_indices]
    rp=free_indices+pivot_indices;row_swaps=sum(rp[i]>rp[j] for i in range(44) for j in range(i+1,44))
    cp=[full_names.index(n) for n in names+ynames];col_swaps=sum(cp[i]>cp[j] for i in range(44) for j in range(i+1,44))
    assert (row_swaps,col_swaps)==(115,19)
    assert [sum(p[i] for p in powers) for i in range(3)]==[7,2,0]
    rng=random.Random(20261107);b=[rng.randrange(1,37) for _ in range(25)];c=[rng.randrange(1,37) for _ in range(25)]
    packet={'schema':'symmetric-schur25-contact-system-v1','scalar_nodes':C.nodes,
        'variable_order':names,'equation_nodes':equations,'jacobian_matrix_nodes':matrix,
        'small_open_nodes':source['small_open_nodes'],'small_open_inverse_variables':source['small_open_inverse_variables'],
        'small_open_equation_nodes':source['small_open_equation_nodes'],
        'full_source_variable_order':full_names,'full_source_equation_nodes':full_roots,
        'source_H_at_g2_zero_nodes':H0,'source_R_nodes':[replacements[f'R{i}'] for i in range(44)],
        'source_equation_monomial_order':exponents,'free_row_indices':free_indices,'pivot_row_indices':pivot_indices,
        'quotient_variable_order':ynames,'quotient_numerator_nodes':N,'quotient_denominator_node':D,
        'quotient_reconstruction_nodes':phi,'quotient_pivot_matrix_nodes':M,
        'rowfactor_nodes':factors,'rowfactor_delta_exponents':powers,
        'exact_row_identity':'H_pivot(x,N/D)=0; H_free_i(x,N/D)=(rowfactor_i/D)*F_i(x)',
        'off_ideal_gradient_identity':'D^2*S_ik = D*rowfactor_i*dF_i/dx_k + (D*d(rowfactor_i)/dx_k-rowfactor_i*dD/dx_k)*F_i, where S=d(H_free(x,N/D))/dx.',
        'row_permutation_inversions':row_swaps,'column_permutation_inversions':col_swaps,
        'determinant_relations':{'pivot_M':'delta1*delta2^3*delta3',
            'reduced_J_on_ideal':'delta1^17*delta2^20*delta3^24*full_J44',
            'rowfactor_product':'delta1^7*delta2^2'},
        'generic_rhs_claim':'Apply the two-RHS theorem to the25 reduced equations. This is exactly the full44 J-localization on the same Delta open, after generic RHS scalar extension.',
        'fixed_rhs':{'prime':37,'seed':20261107,'b':b,'c':c,'genericity_proved':False},
        'fixed_rhs_acceptance':'A verified zero-dimensional augmented quotient with unrestricted auxiliary vectors suffices; no fixed RHS equivalence is asserted before that gate.',
        'no_additional_open_assumptions':True,'remaining_full_opens':['delta9','D10'],
        'source_hashes':{'point_scaled':sha256(path.read_bytes()).hexdigest(),'generic_numerators':sha256(GENERIC.read_bytes()).hexdigest()},
        'generic_audit':generic_receipt,'fixed_rhs_equivalence_proved':False,
        'quotient_basis_completed':False,'source_trace_proved':False,'full_certificate_proved':False}
    return packet,source,witness


def source_binding_audit(packet,source):
    import sympy as sp
    cache={};nodes=packet['scalar_nodes']
    def val(i):
        if i in cache:return cache[i]
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':v=sp.Rational(*d)
        elif op=='variable':v=sp.Symbol(d)
        elif op=='add':v=sp.Add(*(val(j) for j in d))
        elif op=='multiply':v=sp.Mul(*(val(j) for j in d))
        elif op=='power':v=val(d[0])**d[1]
        elif op=='inverse':v=1/val(d)
        else:raise ValueError(op)
        cache[i]=v;return v
    q2={tuple(t['exponent']):val(t['coefficient_node']) for t in source['scaled_polynomials']['Q2']}
    sub={sp.Symbol(n):val(i) for n,i in source['eliminated_variable_nodes'].items()}
    q2={e:c.subs(sub,simultaneous=True) for e,c in q2.items()}
    g2exp={nodes[t['coefficient_node']]['data']:tuple(t['exponent']) for t in source['scaled_polynomials']['g2']}
    checked=0
    for root,zero,e in zip(packet['full_source_equation_nodes'],packet['source_H_at_g2_zero_nodes'],packet['source_equation_monomial_order']):
        linear=sum(q2.get(tuple(a-b for a,b in zip(e,g2exp[n])),0)*sp.Symbol(n) for n in packet['quotient_variable_order'])
        assert sp.cancel(sp.expand(val(root)-val(zero)-linear))==0
        checked+=1
    return {'source_affine_g2_identities_verified':checked,
        'characteristic_zero_binding':'The audited generic49-variable polynomial identities are instantiated by the displayed homomorphism R_i=-H_i|g2=0, mu0=the exact moving-point elimination. The44 source affine identities establish the full original equation binding without freezing g2.'}


def evaluate_modular(packet,roots,names,prime=37):
    import flint
    ctx=flint.nmod_mpoly_ctx.get(tuple(names),prime,'degrevlex');V=dict(zip(names,ctx.gens()))
    V.update(lam=ctx.constant(1),r=ctx.constant(2),s=ctx.constant(3));nodes=packet['scalar_nodes']
    @lru_cache(None)
    def ev(i):
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':return ctx.constant(d[0]*pow(d[1],-1,prime)%prime)
        if op=='variable':return V[d]
        if op=='add':return sum((ev(j) for j in d),ctx.constant(0))
        if op=='multiply':
            out=ctx.constant(1)
            for j in d:out*=ev(j)
            return out
        if op=='power':return ev(d[0])**d[1]
        if op=='inverse':
            p=ev(d);terms=p.to_dict();assert len(terms)==1 and next(iter(terms))==(0,)*len(names)
            return ctx.constant(pow(int(next(iter(terms.values()))),-1,prime))
        raise ValueError(op)
    return ctx,V,ev,[ev(i) for i in roots]


def emit_witness(packet,count):
    aux=[f'sv{i}' for i in range(25)]+([f'sw{i}' for i in range(25)] if count==2 else [])
    names=packet['variable_order']+aux+packet['small_open_inverse_variables']
    ctx,V,ev,core=evaluate_modular(packet,packet['equation_nodes'],names)
    matrix=[[f.derivative(j) for j in range(25)] for f in core]
    # Bind all emitted modular gradients to the exact derivative DAG, not just
    # sampled values. This is separate from the exact source/generic audits.
    for row,nodes in zip(matrix,packet['jacobian_matrix_nodes']):
        for f,node in zip(row,nodes):assert f==ev(node)
    equations=list(core)
    for prefix,rhs in [('sv',packet['fixed_rhs']['b'])]+([('sw',packet['fixed_rhs']['c'])] if count==2 else []):
        equations.extend(sum((f*V[f'{prefix}{j}'] for j,f in enumerate(row)),ctx.constant(0))-ctx.constant(rhs[i]) for i,row in enumerate(matrix))
    equations.extend(ev(i) for i in packet['small_open_equation_nodes'])
    assert len(names)==len(equations)==31+25*count
    text=','.join(names)+'\n37\n'+',\n'.join(map(str,equations))+'\n'
    path=HERE/f'schur25_witness_{count}rhs_p37.ms';path.write_text(text)
    receipt={'file':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),'variables':len(names),'equations':len(equations),
        'rhs_count':count,'core_variables':25,'core_equations':25,'inverse_variables':6,
        'core_terms':sum(map(len,core)),'total_terms':sum(map(len,equations)),
        'maximum_core_degree':int(max(p.total_degree() for p in core)),
        'maximum_input_degree':int(max(p.total_degree() for p in equations)),
        'all625_modular_gradient_polynomials_match_exact_DAG':True,
        'prime':37,'base':{'lam':1,'r':2,'s':3},'variable_order':names,
        'small_opens':list(packet['small_open_nodes']),'no_additional_open_assumptions':True,
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,'source_trace_proved':False}
    (HERE/f'schur25_witness_{count}rhs_p37_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def main():
    started=time.monotonic();packet,source,witness=build()
    output=HERE/'schur25_system.json';output.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    receipt=dict(packet['generic_audit']);receipt.update(source_binding_audit(packet,source))
    print(json.dumps({'phase':'exact_reconstruction_audit_passed','packet':output.name,**receipt}),flush=True)
    inputs=[]
    for count in (1,2):
        result=emit_witness(packet,count);inputs.append(result)
        print(json.dumps({k:v for k,v in result.items() if k!='variable_order'},indent=2),flush=True)
    receipt.update(status='PASS',packet_sha256=sha256(output.read_bytes()).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),modular_inputs=inputs,
        derivative_builder_sha256=sha256((HERE/'jacobian_witness_system.py').read_bytes()).hexdigest(),
        determinant_relation=packet['determinant_relations']['reduced_J_on_ideal'],
        scope='Exact generic quotient reconstruction plus exact characteristic-zero source binding. Gradients are generated by the chain rule and independently compared as625 full polynomials overF37. Fixed-RHS equivalence, a complete finite quotient, and all nine traces remain unproved.',
        fixed_rhs_equivalence_proved=False,quotient_basis_completed=False,source_trace_proved=False,full_certificate_proved=False,
        seconds=time.monotonic()-started)
    (HERE/'schur25_system_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','seconds':receipt['seconds'],'packet_sha256':receipt['packet_sha256']}),flush=True)


if __name__=='__main__':main()
