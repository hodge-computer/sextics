#!/usr/bin/env python3
"""Eight disjoint B-pivot strata for the remaining common-sign quotient.

Chart j imposes B_0=...=B_(j-1)=0, B_j!=0, and writes every cubic
coefficient as gamma times a normalized one, with gamma=B_j and z=gamma^2.
All eight charts are retained.  No assertion that chart zero is sufficient is
made, and the large full-localization determinants are not silently omitted.
"""
from hashlib import sha256
from pathlib import Path
import json
import time
import point_scaled_system as S

HERE=Path(__file__).resolve().parent


def build():
    source=json.loads((HERE/'point_scaled_system.json').read_text())
    C=S.Circuit(source['scalar_nodes']);P=S.Polynomials(C);z=C.var('z')
    def form(name):return {tuple(e['exponent']):e['coefficient_node'] for e in source['scaled_polynomials'][name]}
    Q1,Q2,A,B,g2,h2,h4,h6=[form(n) for n in ('Q1','Q2','A','B','g2','h2','h4','h6')]
    R=P.add(P.mul(Q1,Q1,Q1),P.neg(P.mul(h2,Q1,Q1)),P.mul(h4,Q1),P.mul(Q2,g2),P.neg(h6))
    cubic=P.add(P.mul(A,A),P.neg(P.mul(B,B)))
    H=P.add(R,P.scale(cubic,z))
    roots=[H.get(tuple(e),C.zero) for e in source['equation_monomial_order']]
    charts=[]
    for j in range(8):
        replacements={f'B{k}':C.zero for k in range(j)}
        replacements[f'B{j}']=C.one
        A0=C.substitute([source['eliminated_variable_nodes']['A0']],replacements)[0]
        replacements.update(mu0=source['eliminated_variable_nodes']['mu0'],A0=A0)
        equations=C.substitute(roots,replacements)
        names=[v for v in source['variable_order'] if v not in {f'B{k}' for k in range(j+1)}]+['z']
        opens=dict(source['small_open_nodes']);opens['z']=z
        inverse_names=[f'open_{key}' for key in opens]
        inverse_equations=[C.sub(C.mul(C.var(f'open_{key}'),node),C.one) for key,node in opens.items()]
        charts.append({'index':j,'pivot':f'B{j}','prior_zero_coefficients':[f'B{k}' for k in range(j)],
            'variable_order':names,'equation_nodes':equations,'eliminated_variable_nodes':replacements,
            'small_open_nodes':opens,'small_open_inverse_variables':inverse_names,'small_open_equation_nodes':inverse_equations,
            'coordinate_change':'hat_Ai=gamma*Ai, hat_Bi=gamma*Bi, gamma=hat_Bj, Bj=1, z=gamma^2',
            'raw_core_variables':len(names),'raw_equations':len(equations),
            'no_stratum_discarded':True})
        assert len(names)==44-j and len(equations)==44
    return {'schema':'symmetric-point-scaled-B-pivot-quotients-v1','scalar_nodes':C.nodes,'charts':charts,
        'source_point_scaled_packet_sha256':sha256((HERE/'point_scaled_system.json').read_bytes()).hexdigest(),
        'coefficient_field':'Q(lambda,r,s)',
        'cover_reason':'On the original J-open the B coefficient vector is not zero: its eight contact Jacobian columns vanish when B=0, and the single h row can restore at most one rank. The first nonzero B coefficient therefore gives exactly one of the eight strata.',
        'remaining_deck_involution':'gamma->-gamma, all normalized coefficients and z fixed',
        'degree_factor_per_stratum':2,'combined_degree_factor_with_T_B':4,
        'full_trace_rule':'rank(old)=4*sum_j rank(chart_j), Tr_old(M)=4*sum_j Tr_chart_j(M_j). Normalized traces must be combined with these degrees; chart0 alone is not assumed sufficient.',
        'full_open_relations':{'J44_point':'gamma^15*J44_point(normalized cubics)',
            'delta9_point':'gamma^60*delta9_normalized','D10_point':'gamma^71*D10_normalized',
            'small_opens':'delta1,delta2,delta3,t,beta,Gw,z are inverted',
            'chart0_square_jacobian':'J44_B0=-(z^14/2)*J44_point(normalized cubics)',
            'higher_strata_warning':'Charts j>0 have44 equations in44-j variables. Their full J condition is the evaluated original44-Jacobian, not an incorrectly asserted square determinant of the smaller rectangular system.'},
        'source_trace_proved':False,'full_certificate_proved':False}


def audit(packet,source):
    import sympy as sp
    nodes=packet['scalar_nodes'];cache={}
    def val(i):
        if i in cache:return cache[i]
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':v=sp.Rational(*d)
        elif op=='variable':v=sp.Symbol(d)
        elif op=='add':v=sp.Add(*(val(k) for k in d))
        elif op=='multiply':v=sp.Mul(*(val(k) for k in d))
        elif op=='power':v=val(d[0])**d[1]
        elif op=='inverse':v=1/val(d)
        else:raise ValueError(op)
        cache[i]=v;return v
    gamma,z=sp.symbols('gamma z');lam,r,s=sp.symbols('lam r s')
    original=[val(i) for i in source['equation_nodes']]
    checked=0;results=[]
    for chart in packet['charts']:
        j=chart['index'];replacement={sp.Symbol(f'A{k}'):gamma*sp.Symbol(f'A{k}') for k in range(1,8)}
        replacement.update({sp.Symbol(f'B{k}'):(0 if k<j else gamma if k==j else gamma*sp.Symbol(f'B{k}')) for k in range(8)})
        variables=[sp.Symbol(n) for n in chart['variable_order']]
        maxdegree=0
        for old,node in zip(original,chart['equation_nodes']):
            target=val(node)
            assert sp.cancel(sp.expand(old.subs(replacement,simultaneous=True)-target.subs(z,gamma**2)))==0
            deg=sp.Poly(target,*variables,domain=sp.QQ.frac_field(lam,r,s)).total_degree()
            assert deg<=3
            maxdegree=max(maxdegree,deg);checked+=1
        results.append({'chart':j,'verified_rows':44,'variables':len(variables),'maximum_degree':maxdegree})
    # Independently verify the common cubic-degree pattern that yields the
    # exact gamma^15 scaling of the original reduced44-Jacobian.
    cubics=[sp.Symbol(f'A{k}') for k in range(1,8)]+[sp.Symbol(f'B{k}') for k in range(8)]
    others=[sp.Symbol(v) for v in source['variable_order'] if sp.Symbol(v) not in cubics]
    assert len(cubics)==15 and len(others)==29
    for eq in original:
        poly=sp.Poly(eq,*cubics,domain=sp.QQ.frac_field(lam,r,s,*others))
        for e,c in poly.terms():
            degree=sum(e);assert degree in (0,2)
            if degree==2:assert not (c.free_symbols & set(others))
    return {'status':'PASS','exact_characteristic_zero_row_bindings':checked,'charts':results,
            'all_eight_disjoint_strata_retained':True,'Jacobian_column_scaling_verified':{'linear_cubic_columns':15,'independent_other_columns':29},
            'chart0_coordinate_permutation_inversions':27,
            'selected_h_rows_for_delta9':59,'selected_h_columns_for_D10':71,
            'scope':'Exact polynomial coordinate binding for all eight strata over Q(lambda,r,s). No nonempty/empty claim for any stratum, completed finite basis, or trace value is inferred.',
            'source_trace_proved':False,'full_certificate_proved':False}


def main():
    started=time.monotonic();packet=build();path=HERE/'point_scaled_Bpivot_systems.json'
    path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    inputs=[]
    for chart in packet['charts']:
        sub=dict(chart,scalar_nodes=packet['scalar_nodes'])
        receipts=[S.emit_modular(sub,f'point_scaled_B{chart["index"]}_p37_raw',False),
                  S.emit_modular(sub,f'point_scaled_B{chart["index"]}_p37_smallopens',True)]
        inputs.extend(receipts)
        print(json.dumps({'phase':'chart_inputs_ready','chart':chart['index'],
                          'inputs':[{k:q[k] for k in ('file','sha256','variables','equations','terms','maximum_total_degree')} for q in receipts]}),flush=True)
    source=json.loads((HERE/'point_scaled_system.json').read_text());receipt=audit(packet,source)
    receipt.update(packet_sha256=sha256(path.read_bytes()).hexdigest(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   modular_inputs=inputs,seconds=time.monotonic()-started)
    (HERE/'point_scaled_Bpivot_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='modular_inputs'},indent=2),flush=True)


if __name__=='__main__':main()
