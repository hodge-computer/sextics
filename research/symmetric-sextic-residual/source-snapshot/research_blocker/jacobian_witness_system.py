#!/usr/bin/env python3
"""Sparse determinant-free Jacobian-open witness systems.

One or two unrestricted vectors solve J*v=b (and J*w=c).  The two-vector
system is generically exactly the J-localization by the accompanying dimension
argument.  Fixed modular RHS choices are NOT declared generic.  A complete
zero-dimensional basis for either fixed system would certify equivalence,
because a surviving singular root has a positive-dimensional kernel fiber.
"""
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import json
import random
import sys
import time

HERE=Path(__file__).resolve().parent
for candidate in (HERE.parent/'research_memory',HERE.parent/'research_trace2',HERE.parent/'research_point_scaled',HERE.parent/'proof_attempt6'):
    if (candidate/'point_scaled_system.py').exists():
        POINT=candidate;sys.path.insert(0,str(candidate));break
else:raise RuntimeError('Cannot locate the adjacent point-scaled source package')
import point_scaled_system as S


class DifferentialCircuit(S.Circuit):
    @lru_cache(None)
    def derivative(self,node,variable):
        op,d=self.nodes[node]['op'],self.nodes[node]['data']
        if op=='rational':return self.zero
        if op=='variable':return self.one if d==variable else self.zero
        if op=='add':return self.add(*(self.derivative(i,variable) for i in d))
        if op=='multiply':return self.add(*(self.mul(self.derivative(i,variable),*(d[:j]+d[j+1:])) for j,i in enumerate(d)))
        if op=='power':return self.mul(self.const(d[1]),self.power(d[0],d[1]-1),self.derivative(d[0],variable))
        if op=='inverse':return self.neg(self.mul(self.derivative(d,variable),self.power(self.node('inverse',d),2)))
        raise ValueError(op)


def build(path,label):
    source=json.loads(path.read_text());C=DifferentialCircuit(source['scalar_nodes'])
    names=source['variable_order'];equations=source['equation_nodes'];n=len(names)
    assert n==len(equations)==44
    matrix=[[C.derivative(eq,name) for name in names] for eq in equations]
    vnames=[f'jv{i}' for i in range(n)];wnames=[f'jw{i}' for i in range(n)]
    rhsnames_b=[f'rhs_b{i}' for i in range(n)];rhsnames_c=[f'rhs_c{i}' for i in range(n)]
    v=[C.var(x) for x in vnames];w=[C.var(x) for x in wnames]
    b=[C.var(x) for x in rhsnames_b];c=[C.var(x) for x in rhsnames_c]
    veqs=[C.sub(C.add(*(C.mul(a,x) for a,x in zip(row,v))),rhs) for row,rhs in zip(matrix,b)]
    weqs=[C.sub(C.add(*(C.mul(a,x) for a,x in zip(row,w))),rhs) for row,rhs in zip(matrix,c)]
    rng=random.Random(20261107)
    bvalues=[rng.randrange(1,37) for _ in range(n)]
    cvalues=[rng.randrange(1,37) for _ in range(n)]
    variants=[]
    for count in (1,2):
        variants.append({'rhs_count':count,'variable_order':names+vnames+(wnames if count==2 else []),
            'equation_nodes':equations+veqs+(weqs if count==2 else []),
            'small_open_nodes':source['small_open_nodes'],
            'small_open_inverse_variables':source['small_open_inverse_variables'],
            'small_open_equation_nodes':source['small_open_equation_nodes']})
    return {'schema':'symmetric-jacobian-witness-system-v1','source_label':label,
        'source_file':path.name,'source_sha256':sha256(path.read_bytes()).hexdigest(),
        'scalar_nodes':C.nodes,'core_variable_order':names,'core_equation_nodes':equations,
        'jacobian_matrix_nodes':matrix,'variants':variants,
        'generic_coefficient_field':'Q(lambda,r,s,rhs_b0,...,rhs_b43,rhs_c0,...,rhs_c43)',
        'rhs_names_b':rhsnames_b,'rhs_names_c':rhsnames_c,
        'explicit_modular_rhs':{'prime':37,'seed':20261107,'b':bvalues,'c':cvalues,
            'genericity_of_this_specialization_proved':False},
        'generic_two_vector_claim':'Over the field with88 independent RHS parameters, this presentation is canonically isomorphic to the J-localized core algebra on the same small opens.',
        'fixed_rhs_acceptance_criterion':'For either one or two unrestricted solve vectors, an independently certified zero-dimensional augmented quotient implies J is a unit and proves canonical equality with the original J-localization over that exact coefficient field.',
        'forbidden_shortcut':'Do not add linear normalizations or other constraints on the auxiliary solve vectors: they can remove kernel fibers and invalidate the zero-dimensionality criterion.',
        'remaining_full_opens':['delta9','D10'],
        'matrix_determinant_expanded':False,
        'generic_dimension_argument_Lean_formalized':False,
        'fixed_rhs_equivalence_proved':False,
        'quotient_basis_completed':False,'source_trace_proved':False,'full_certificate_proved':False}


def audit(packet):
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
    checked=0;nonzero=0
    names=packet['core_variable_order'];vars=[sp.Symbol(n) for n in names]
    for root,row in zip(packet['core_equation_nodes'],packet['jacobian_matrix_nodes']):
        f=val(root)
        for var,node in zip(vars,row):
            derivative=sp.diff(f,var)
            assert sp.cancel(sp.expand(derivative-val(node)))==0
            checked+=1;nonzero+=int(derivative!=0)
    # Exact counterexample to the requested one-RHS linear-normalization idea.
    b1,b2,c1,c2,d=sp.symbols('b1 b2 c1 c2 d',nonzero=True)
    x=sp.Integer(0);y=b2/b1;v1=b1;v2=(d-c1*b1)/c2
    J=sp.Matrix([[1,0],[y,x]])
    assert J.det()==0
    assert (J*sp.Matrix([v1,v2])-sp.Matrix([b1,b2])).applyfunc(sp.cancel)==sp.zeros(2,1)
    assert sp.cancel(c1*v1+c2*v2-d)==0
    return {'status':'PASS','exact_characteristic_zero_derivative_identities':checked,
        'structurally_nonzero_jacobian_entries':nonzero,
        'linear_normalization_counterexample_checked':True,
        'counterexample':{'f':['x','x*y'],'J':[['1','0'],['y','x']],
            'solution':{'x':'0','y':'b2/b1','v1':'b1','v2':'(d-c1*b1)/c2'},
            'constraints':['J*v=b','c1*v1+c2*v2=d'],'detJ':'0',
            'consequence':'A linear normalization can leave a finite singular quotient; it must not be used as a substitute for the second unrestricted RHS.'},
        'fixed_rhs_equivalence_proved':False,'quotient_basis_completed':False,
        'source_trace_proved':False,'full_certificate_proved':False}


def process(path,label):
    started=time.monotonic();packet=build(path,label)
    output=HERE/f'jacobian_witness_{label}.json'
    output.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    fixed=packet['explicit_modular_rhs'];base={'lam':1,'r':2,'s':3}
    base.update(dict(zip(packet['rhs_names_b'],fixed['b'])));base.update(dict(zip(packet['rhs_names_c'],fixed['c'])))
    inputs=[]
    # Use the same exact sparse emitter as the source system, but write locally.
    saved_here=S.HERE;S.HERE=HERE
    try:
        for variant in packet['variants']:
            view=dict(variant,scalar_nodes=packet['scalar_nodes'])
            tag=f'jacobian_{label}_{variant["rhs_count"]}rhs_p37'
            receipt=S.emit_modular(view,tag,True,37,base)
            receipt.update(source_packet_sha256=sha256(output.read_bytes()).hexdigest(),
                rhs_count=variant['rhs_count'],fixed_rhs_equivalence_proved=False,
                zero_dimensionality_would_certify_J_localization=True,
                full_delta9_D10_localization_included=False)
            (HERE/(tag+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
            inputs.append(receipt)
            print(json.dumps({'phase':'input_ready','source':label,'rhs_count':variant['rhs_count'],
                'file':receipt['file'],'variables':receipt['variables'],'equations':receipt['equations'],
                'terms':receipt['terms'],'maximum_total_degree':receipt['maximum_total_degree'],
                'sha256':receipt['sha256']}),flush=True)
    finally:S.HERE=saved_here
    receipt=audit(packet)
    receipt.update(source_label=label,packet_sha256=sha256(output.read_bytes()).hexdigest(),
                   script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   modular_inputs=inputs,seconds=time.monotonic()-started)
    (HERE/f'jacobian_witness_{label}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='modular_inputs'},indent=2),flush=True)


def main():
    process(POINT/'point_scaled_system.json','point_scaled')
    beta=HERE/'finite_beta_model.json'
    if beta.exists():process(beta,'beta')


if __name__=='__main__':main()
