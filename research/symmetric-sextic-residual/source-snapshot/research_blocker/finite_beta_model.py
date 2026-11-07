#!/usr/bin/env python3
"""Exact beta coordinate and plane-cubic row replacement.

The transformation is an affine coordinate isomorphism and an invertible row
operation over Q(lambda,r,s).  It does not discard any component or claim that
the localized contact algebra has been computed.
"""
from pathlib import Path
from functools import lru_cache
from hashlib import sha256
import importlib.util
import json
import sys

HERE=Path(__file__).resolve().parent
SOURCE=next((HERE.parent/p for p in ('research_memory','proof_attempt6') if (HERE.parent/p).exists()))

def source_module():
    spec=importlib.util.spec_from_file_location('point_scaled_system',SOURCE/'point_scaled_system.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def main():
    S=source_module();source=json.loads((SOURCE/'point_scaled_system.json').read_text())
    C=S.Circuit(source['scalar_nodes']);beta=C.var('beta');r=C.var('r');s=C.var('s')
    rho=[C.var(f'rho{i}') for i in range(5)]
    rho0=C.neg(C.add(beta,C.mul(rho[1],C.power(r,2)),rho[2],C.mul(rho[3],s),C.mul(rho[4],C.power(s,2))))
    replacements={'rho0':rho0}
    point=[C.one,r,C.one,s,beta]
    Gpoint=C.add(*(C.mul(term['coefficient_node'],*(C.power(x,k) for x,k in zip(point,term['exponent'])))
                   for term in source['scaled_G']))
    pivot=source['equation_monomial_order'].index([6,0,0,0])
    equations=C.substitute(source['equation_nodes'],replacements)
    original_replaced_equations=list(equations);equations[pivot]=Gpoint
    weights=[C.mul(C.power(r,e[1]),C.power(s,e[3])) for e in source['equation_monomial_order']]
    opens={k:C.substitute([v],replacements)[0] for k,v in source['small_open_nodes'].items()}
    inverse_equations=C.substitute(source['small_open_equation_nodes'],replacements)
    names=['beta' if n=='rho0' else n for n in source['variable_order']]
    # Exact symbolic audit, retaining lambda/r/s as independent variables.
    import sympy as sp
    @lru_cache(None)
    def val(i):
        op,d=C.nodes[i]['op'],C.nodes[i]['data']
        if op=='rational':return sp.Rational(*d)
        if op=='variable':return sp.Symbol(d)
        if op=='add':return sp.Add(*(val(j) for j in d))
        if op=='multiply':return sp.Mul(*(val(j) for j in d))
        if op=='power':return val(d[0])**d[1]
        if op=='inverse':return 1/val(d)
        raise ValueError(op)
    row_identity=sp.cancel(sp.expand(val(Gpoint)+sum(val(w)*val(h) for w,h in zip(weights,original_replaced_equations))))
    assert row_identity==0
    assert val(weights[pivot])==1
    assert sp.cancel(sp.expand(val(opens['beta'])-sp.Symbol('beta')))==0
    assert sp.diff(val(rho0),sp.Symbol('beta'))==-1
    assert {str(v) for v in val(Gpoint).free_symbols}<={'beta','t','lam','r','s'}
    packet={
        'schema':'point-scaled-beta-plane-cubic-v1','coefficient_field':'Q(lambda,r,s)',
        'scalar_nodes':C.nodes,'variable_order':names,'equation_nodes':equations,
        'small_open_inverse_variables':source['small_open_inverse_variables'],
        'small_open_equation_nodes':inverse_equations,'small_open_nodes':opens,
        'rho0_substitution_node':rho0,'plane_cubic_node':Gpoint,
        'row_replacement':{'pivot_index':pivot,'pivot_monomial':[6,0,0,0],
            'old_equation_nodes_in_new_coordinates':original_replaced_equations,
            'weights':weights,'identity':'Gpoint=-sum(weights[i]*H[i])','row_determinant':-1},
        'coordinate_determinant':-1,'incidence_Jacobian_determinant_factor':1,
        'source_packet_sha256':sha256((SOURCE/'point_scaled_system.json').read_bytes()).hexdigest(),
        'full_localization_obligations':['J44','delta9_hat','D10_hat'],
        'source_trace_proved':False,'full_certificate_proved':False,
    }
    packet_path=HERE/'finite_beta_model.json';packet_path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    allnames=names+source['small_open_inverse_variables'];prime=37;base={'lam':1,'r':2,'s':3}
    polys=S.evaluate_modular(packet,equations+inverse_equations,allnames,prime,base)
    text=','.join(allnames)+'\n'+str(prime)+'\n'+',\n'.join(S.poly_string(p,allnames) for p in polys)+'\n'
    path=HERE/'finite_beta_p37.ms';path.write_text(text)
    first_names=[n for n in allnames if n.startswith('g2_')]+[n for n in allnames if not n.startswith('g2_')]
    first_polys=S.evaluate_modular(packet,equations+inverse_equations,first_names,prime,base)
    permutation=[allnames.index(n) for n in first_names]
    for before,after in zip(polys,first_polys):
        assert {tuple(e[i] for i in permutation):c for e,c in before.items()}==after
    first_path=HERE/'finite_beta_g2first_p37.ms'
    first_path.write_text(','.join(first_names)+'\n'+str(prime)+'\n'+',\n'.join(S.poly_string(p,first_names) for p in first_polys)+'\n')
    specialized=sp.Poly(val(Gpoint).subs({sp.Symbol(k):v for k,v in base.items()}),sp.Symbol('beta'),sp.Symbol('t'))
    receipt={
        'status':'PASS','exact_coefficient_field':'Q(lambda,r,s)',
        'plane_cubic_depends_only_on':['beta','t','lam','r','s'],
        'plane_cubic_at_lambda1_r2_s3':str(specialized.as_expr()),
        'row_identity_verified':True,'affine_coordinate_inverse_verified':True,
        'row_replacement_determinant':-1,'coordinate_determinant':-1,
        'incidence_Jacobian_determinant_factor':1,
        'variables':len(allnames),'equations':len(polys),'terms':sum(map(len,polys)),
        'maximum_total_degree':max(sum(e) for p in polys for e in p),
        'input_sha256':sha256(path.read_bytes()).hexdigest(),
        'ordinary_DRL_g2_first_variant':{
            'file':first_path.name,'sha256':sha256(first_path.read_bytes()).hexdigest(),
            'exact_permutation_verified':True,'variable_order':first_names,
            'warning':'Use ordinary DRL; this ordering does not impose a strict elimination block.'},
        'packet_sha256':sha256(packet_path.read_bytes()).hexdigest(),
        'scope':'Exact coordinate and equation transformation of the same cheap-open incidence. This is not a completed finite algebra or any trace evaluation.',
        'source_trace_proved':False,'full_certificate_proved':False,
    }
    (HERE/'finite_beta_model_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
