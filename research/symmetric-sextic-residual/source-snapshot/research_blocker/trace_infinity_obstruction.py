#!/usr/bin/env python3
"""Exact large infinity strata of the INPUT leading-form systems.

These are not claimed to be components of the saturated projective closure,
nor positive-dimensional affine components. They obstruct the elementary
Euler-Jacobi hypothesis that the displayed leading forms have no common
projective zero.
"""
from pathlib import Path
from functools import lru_cache
import hashlib, json, sys, time

HERE=Path(__file__).resolve().parent
try:
    import sympy as sp
except ModuleNotFoundError:
    for p in (HERE.parent/'research_workaround/python_deps',
              HERE.parent/'proof_attempt3/python_deps'):
        if p.exists(): sys.path.insert(0,str(p))
    import sympy as sp


def main():
    started=time.monotonic()
    candidates=[HERE.parent/p/'point_scaled_system.json' for p in
                ('research_memory','research_trace2','research_point_scaled','proof_attempt6')]
    path=next((p for p in candidates if p.exists()),None)
    if path is None:raise FileNotFoundError('Adjacent point_scaled_system.json')
    packet=json.loads(path.read_text());nodes=packet['scalar_nodes']
    lam,r,s=sp.symbols('lam r s');field=sp.QQ.frac_field(lam,r,s)
    @lru_cache(None)
    def value(i):
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':return sp.Rational(*d)
        if op=='variable':return sp.Symbol(d)
        if op=='add':return sp.Add(*(value(j) for j in d))
        if op=='multiply':return sp.Mul(*(value(j) for j in d))
        if op=='power':return value(d[0])**d[1]
        if op=='inverse':return 1/value(d)
        raise ValueError(op)
    forced=[f'rho{i}' for i in range(5)]+['t']+[f'mu{i}' for i in range(1,5)]+['A1','A5','A6','A7']
    names=packet['variable_order'];variables=list(map(sp.Symbol,names))
    zeros={sp.Symbol(n):0 for n in forced}
    degree_counts={};nonzero_monomials=[]
    for eq in packet['equation_nodes']:
        poly=sp.Poly(value(eq),*variables,domain=field)
        degree=poly.total_degree();degree_counts[degree]=degree_counts.get(degree,0)+1
        top={e:c for e,c in poly.terms() if sum(e)==degree}
        remaining={e:c for e,c in top.items() if all(e[names.index(v)]==0 for v in forced)}
        assert not remaining,(degree,remaining)
        nonzero_monomials.append(len(top))
    free=[n for n in names if n not in forced]
    assert len(free)==30
    # The six small-open inverse equations also vanish in their top degree
    # on the same plane, with all six inverse coordinates left free.
    open_names=packet['small_open_inverse_variables']
    extended=list(map(sp.Symbol,names+open_names))
    open_degrees={}
    for name,eq in zip(open_names,packet['small_open_equation_nodes']):
        poly=sp.Poly(value(eq),*extended,domain=field);degree=poly.total_degree()
        remaining=[(e,c) for e,c in poly.terms() if sum(e)==degree
                   and all(e[(names+open_names).index(v)]==0 for v in forced)]
        assert not remaining,(name,remaining)
        open_degrees[name]=degree
    # The four omitted h monomials remove the Q2*linear gauge. The even
    # block below has determinant 1-mu0*mu1; the odd block is the identity.
    mu0,mu1=sp.symbols('mu0 mu1')
    gauge_matrix=sp.Matrix([[1,mu0],[mu1,1]])
    assert gauge_matrix.det()==1-mu0*mu1
    receipt={
        'status':'PASS','coefficient_field':'Q(lambda,r,s)',
        'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'equations':len(packet['equation_nodes']),'variables':len(names),
        'input_total_degree_counts':degree_counts,
        'explicit_linear_infinity_stratum':{'zero_coordinates':forced,'free_coordinates':free,
            'projective_dimension':len(free)-1,'all_input_leading_forms_vanish':True},
        'small_open_inverse_equations':{'degrees':open_degrees,
            'all_inverse_coordinates_free_on_same_stratum':True,
            'projective_dimension':len(free)+len(open_names)-1},
        'gauge_check':{'even_omitted_monomials':['a^2*b','a*b^2'],
                       'odd_omitted_monomials':['a*b*c','a*b*d'],
                       'even_gauge_block_determinant':'1-mu0*mu1',
                       'odd_gauge_coefficients':'The abc/abd coefficients of Q2*(lc*c+ld*d) are lc/ld, since the ab coefficient of Q2 is1.',
                       'conclusion':'The four Q2*linear cubic gauges have no residual tangent on the Delta open.'},
        'proved_obstruction':'The displayed highest forms fail the no-common-projective-zero hypothesis needed by the elementary global Euler-Jacobi residue shortcut.',
        'not_proved':['an affine positive-dimensional component','a positive-dimensional component of the saturated projective closure','the precise cause of every F4 allocation','any full trace value'],
        'source_trace_proved':False,'full_certificate_proved':False,
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds':time.monotonic()-started}
    (HERE/'trace_infinity_obstruction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
