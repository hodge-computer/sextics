#!/usr/bin/env python3
"""Emit the full finite-etale-algebra trace target, without root enumeration.

The scalar DAG, coefficient matrices and determinant/adjugate recipes are all
specified. It does not evaluate the final traces. The finite algebra is the
entire Jacobian-localized contact incidence, not an unspecified chosen root.
"""
from pathlib import Path
from itertools import product
import copy, hashlib, json
import contact_forms_circuit as F

HERE=Path(__file__).resolve().parent

def mons(d,parity=None):
    return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d and
                  (parity is None or (e[2]+e[3])%2==parity))

def build():
    frame=F.build();C=F.N.Circuit()
    C.nodes=copy.deepcopy(frame['nodes'])
    # Retain the nineteen quotient coefficients as actual algebra variables.
    for node in C.nodes:
        if node['op']=='solve_entry':
            assert node['data'][0]==0
            node.update(op='variable',data=f'g2_{node["data"][1]}')
    C.memo={(v['op'],tuple(v['data']) if isinstance(v['data'],list) else v['data']):i
            for i,v in enumerate(C.nodes)}
    source_path=HERE/'contact_target_circuit.json'
    if not source_path.exists():source_path=F.OLD/'symmetric_norm_contact_circuit.json'
    source=json.loads(source_path.read_text())
    P=F.Polynomials(C,4)
    Q2={tuple(e['exponent']):e['coefficient_node'] for e in frame['residue_forms']['Q2']}
    g2={tuple(e['exponent']):e['coefficient_node'] for e in frame['residue_forms']['g2']}
    residual={tuple(e['exponent']):e['coefficient_node'] for e in source['polynomials']['R']}
    full=P.add(P.mul(Q2,g2),P.neg(residual))
    basis=mons(6,0);assert len(basis)==44
    equation_nodes=[full.get(e,C.zero) for e in basis]
    contact_order=source['parameter_order']+[f'g2_{j}' for j in range(19)]
    incidence_order=contact_order+['alpha']
    equations=equation_nodes+[source['point_q_node'],source['point_h_node']]
    regular=json.loads((HERE/'contact_forms_regularity_witness.json').read_text())
    nonzero=json.loads((HERE/'contact_forms_nonzero_witness.json').read_text())
    fs=[{tuple(e['exponent']):e['coefficient_node'] for e in frame['residue_forms'][name]}
         for name in ('Q2','h','g1bar','g2')]
    rows10=mons(10);idx10={e:i for i,e in enumerate(rows10)};columns10=[]
    for f,d in zip(fs,[2,3,4,4]):
        for m in mons(10-d):columns10.append([[idx10[tuple(x+y for x,y in zip(e,m))],v]
                                             for e,v in sorted(f.items())])
    selected10=[columns10[j] for j in regular['selected_columns']]
    selected9=[frame['ideal_product_columns'][j]['entries'] for j in nonzero['selected_ideal_columns']]
    # G_w at the selected point, with independent quotient variables irrelevant.
    source_G={tuple(t['exponent']):t['coefficient_node'] for t in source['polynomials']['G']}
    r,s,alpha=[C.var(v) for v in ('r','s','alpha')]
    beta=source['point_beta_node'];point=[C.one,r,alpha,C.mul(s,alpha),beta]
    GW={tuple(n-int(i==4) for i,n in enumerate(e)):C.mul(v,C.const(e[4]))
        for e,v in source_G.items() if e[4]}
    gpoint=F.Polynomials(C,5).evaluate(GW,point)
    return {'schema':'symmetric-full-incidence-global-residue-target-v1',
        'coefficient_field':'K=Q(lambda,r,s)',
        'scalar_nodes':C.nodes,'linear_solves':[],
        'contact_variable_order':contact_order,'incidence_variable_order':incidence_order,
        'localized_variable_order':incidence_order+['zeta'],
        'contact_equation_monomial_order':[list(e) for e in basis],
        'contact_equation_nodes':equation_nodes,'incidence_equation_nodes':equations,
        'equation_sign':'H=Q1^3-h2*Q1^2+h4*Q1+A^2-B^2+Q2*g2-h6; coefficients in invariant sextic monomials.',
        'determinant_frames':{
            'J':{'op':'determinant','matrix':{'op':'jacobian','equation_nodes':equations,'variables':incidence_order}},
            'K':{'op':'signed_maximal_minors','matrix':{'op':'jacobian','equation_nodes':equation_nodes,'variables':contact_order},
                 'entry_formula':'K_j=(-1)^(44+j)*det(matrix with column j omitted), j=0,...,44'},
            'D10':{'op':'determinant','shape':[286,286],'sparse_columns':selected10,
                   'basis':[list(e) for e in rows10]},
            'T9':{'shape':[220,220],'first_219_sparse_rows':selected9,
                  'last_row':{'op':'polynomial_coefficients','basis':frame['socle_basis'],
                              'polynomial':{'op':'determinant','polynomial_matrix':frame['normalization_jacobian_matrix']}},
                  'orientation':'Rows are functional constraints: 219 ideal products then the Jacobian.'},
            'delta9':{'op':'determinant','matrix_ref':'T9'},
            'tau_numerator':{'op':'matrix_vector_product','matrix':{'op':'adjugate','matrix_ref':'T9'},
                             'vector':{'length':220,'nonzero_entries':[[219,96]]}},
            'f_numerator':{'op':'sum','terms':[
                {'op':'multiply','factors':[{'op':'entry','vector_ref':'K','index':10+j},
                    {'op':'dot','left':{'length':220,'nonzero_entries':slot['socle_coefficient_nodes']},
                     'right_ref':'tau_numerator'}]}
                for j,slot in enumerate(frame['canonical_one_form']['components'])]}},
        'localization':{'factors':{'Delta_node':source['localization_Delta_node'],'J_ref':'J',
            'delta9_ref':'delta9','D10_ref':'D10','alpha_node':alpha,'beta_node':beta,'G_w_at_point_node':gpoint},
            'S':'Delta*J*delta9*D10*alpha*beta*G_w_at_point',
            'last_equation':'zeta*S-1=0',
            'S0':'S/delta9=Delta*J*D10*alpha*beta*G_w_at_point',
            'T0':'S/(delta9*J)=Delta*D10*alpha*beta*G_w_at_point'},
        'finite_algebra':{'presentation':'A=K[p_0,...,p_44,alpha,zeta]/(H_1,...,H_44,q,h,zeta*S-1)',
            'finite_etale_reason':'At every geometric point J and S are units. The 46-equation Jacobian has full rank, so the generic-fiber algebra is reduced of dimension zero; a zero-dimensional finite-type K-algebra is finite etale.',
            'nonzero_reason':'The exact root and nonzero determinant certificates give a point of this open at lambda=s=1; the incidence Jacobian gives a dominant local component over (lambda,r,s).',
            'component_selection':'All points of the stated localized generic algebra are included; no irreducible factor is chosen.'},
        'canonical_form':'eta_R=tau(R dh), with tau=tau_numerator/delta9, pulled back from the contact curve.',
        'source_numerator_polynomials':{'P1':frame['P1'],'P2':frame['P2']},
        'coefficient_obligations':[dict(pair,
            polynomial_representative='zeta*T0*f_numerator*P_coefficient_node-target_coefficient_node',
            trace_condition='Trace_A/K(multiplication_by_polynomial_representative)=0',
            equivalent_global_residue_numerator='S0*f_numerator*P_coefficient_node-target_coefficient_node*S*J')
            for pair in frame['target_pairs']],
        'global_residue':{'equations':'H_1,...,H_44,q,h,zeta*S-1',
            'dimension':47,'Jacobian':'S*J',
            'identity':'Res_A(H)=sum H(point)/(S(point)*J(point)); Trace_A(g)=Res_A(S*J*g).',
            'source_cancellation':'The sole canonical-form denominator delta9 and the incidence denominator J are absorbed by zeta*S=1; every displayed multiplication-trace target is polynomial in the finite algebra.',
            'computational_certificate':'An exact Groebner/linear-basis certificate for A, followed by the nine multiplication traces, would verify the rational-function target without enumerating algebraic roots.'},
        'input_hashes':{'base_circuit':frame['base_circuit_sha256'],
            'regularity_witness':hashlib.sha256((HERE/'contact_forms_regularity_witness.json').read_bytes()).hexdigest(),
            'nonzero_witness':hashlib.sha256((HERE/'contact_forms_nonzero_witness.json').read_bytes()).hexdigest()},
        'source_trace_proved':False,'full_certificate_proved':False,
        'scope':'The finite algebra and all trace operands are concretely specified. The nine coefficient rational-function trace equalities have not been evaluated or proved.'}

def main():
    p=build();path=HERE/'contact_forms_global_residue.json'
    path.write_text(json.dumps(p,separators=(',',':'))+'\n')
    print(json.dumps({'scalar_nodes':len(p['scalar_nodes']),'incidence_equations':len(p['incidence_equation_nodes']),
        'localized_equations':47,'trace_obligations':len(p['coefficient_obligations']),
        'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_trace_proved':False},indent=2),flush=True)

if __name__=='__main__':main()
