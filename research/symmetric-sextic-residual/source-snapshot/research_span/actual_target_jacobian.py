#!/usr/bin/env python3
"""Exact binding and degree-six negative Jacobian rank for the actual target.

This checks rational polynomial identities, not the geometric correspondence
or a Lean certificate.  The 12 Jacobian columns are the entire negative
weight-six part of the Jacobian ideal.  Their selected minor reduces to 1
modulo 5, so the quotient has dimension 60 - 12 = 48 over Q and C.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import product
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
try:
    import sympy as S
except ImportError:
    sys.path.insert(0,str(ROOT/'proof_attempt3/python_deps'))
    import sympy as S
CIRCUIT = next(p for p in [ROOT/'proof_attempt4/contact_target_circuit.json',
                           ROOT/'research_contact/contact_target_circuit.json'] if p.exists())
INSTANCE = next(p for p in [ROOT/'sextics/data/symmetric-sextic-residual/instance.rec',
                            ROOT/'inputs/instance.rec'] if p.exists())


def main():
    a,b,c,d,u = S.symbols('a b c d u')
    variables = (a,b,c,d,u)
    qx = a*a + 2*a*b - u
    qy = c*c + 2*c*d - u
    raw = (2*a**6+b**6+2*c**6+d**6
           +30*a**4*u+30*a*a*u*u+4*u**3
           +30*c**4*u+30*c*c*u*u
           +S.Rational(5,7)*qx**2*qy+S.Rational(10,7)*qx*qy**2)
    actual = S.Poly(S.expand(S.Rational(7,13)*raw), *variables)
    # Bind the model to the untouched instance record, not just a repeated
    # hand transcription of its compact formula.
    fields = {}; key = None
    for line in INSTANCE.read_text().splitlines():
        if line.startswith('  '):
            if key is not None: fields[key] += ' '+line.strip()
        elif ':' in line and not line.startswith('#'):
            key,value = line.split(':',1); fields[key] = value.strip()
    assert fields['id'] == 'symmetric-sextic-residual' and fields['q'] == '1'
    original_variables = S.symbols('X0 X1 X2 Y0 Y1 Y2')
    local = dict(zip(map(str,original_variables),original_variables))
    F = S.sympify(fields['F'],locals=local)
    source = S.sympify(fields['A'],locals=local)
    z = S.Symbol('z')
    substitution = dict(zip(original_variables,(a+z,a-z,b,c+z,c-z,d)))
    assert S.expand(F.subs(substitution)-raw.subs(u,z*z)) == 0
    assert S.expand(source.subs(substitution)-b*d*(a*a-z*z)*(c*c-z*z)) == 0
    data = json.loads(CIRCUIT.read_text())
    nodes = data['nodes']

    @lru_cache(None)
    def evaluate(k):
        op, z = nodes[k]['op'], nodes[k]['data']
        if op == 'rational': return Fraction(*z)
        if op == 'variable':
            assert z == 'lam'
            return Fraction(1)
        if op == 'add': return sum(map(evaluate, z), Fraction())
        if op == 'multiply':
            out = Fraction(1)
            for j in z: out *= evaluate(j)
            return out
        if op == 'power': return evaluate(z[0])**z[1]
        if op == 'inverse': return 1/evaluate(z)
        raise ValueError(op)

    circuit_terms = {tuple(t['exponent']): S.Rational(evaluate(t['coefficient_node']))
                     for t in data['polynomials']['G']}
    circuit = S.Poly.from_dict(circuit_terms, variables)
    assert actual == circuit
    basis = sorted(e+(j,) for j in range(4)
                   for e in product(range(7-2*j), repeat=4)
                   if sum(e) == 6-2*j and (e[2]+e[3]) % 2 == 1)
    assert len(basis) == 60
    descriptions = [(0,c),(0,d),(1,c),(1,d),
                    (2,a),(2,b),(3,a),(3,b),
                    (4,a*c),(4,a*d),(4,b*c),(4,b*d)]
    columns = [S.Poly(actual.diff(variables[i]).as_expr()*m, *variables)
               for i,m in descriptions]
    assert all(set(p.monoms()) <= set(basis) for p in columns)
    matrix = S.Matrix([[p.coeff_monomial(e) for p in columns] for e in basis])

    def mod5(q):
        n,d = map(int, S.Rational(q).as_numer_denom())
        return (n*pow(d,-1,5)) % 5

    reduced = [[mod5(matrix[i,j]) for j in range(12)] for i in range(60)]
    pivots = []
    diagonal = []
    for j in range(12):
        support = [i for i in range(60) if reduced[i][j]]
        assert len(support) == 1
        pivots.append(support[0]); diagonal.append(reduced[support[0]][j])
    assert len(set(pivots)) == 12
    minor = matrix.extract(pivots, range(12))
    determinant = minor.det(method='domain-ge')
    assert determinant != 0 and mod5(determinant) == 1
    for j in range(12):
        for i in range(12):
            assert mod5(minor[i,j]) == (diagonal[j] if i == j else 0)

    # Weighted homogeneity and the involution determine all multipliers:
    # G_a,G_b require c,d; G_c,G_d require a,b; G_u requires ac,ad,bc,bd.
    degrees = [1,1,1,1,2]
    parities = [0,0,1,1,0]
    expected = []
    for i in range(5):
        for e in product(range(degrees[i]+1), repeat=5):
            if sum(x*w for x,w in zip(e,degrees)) == degrees[i] and \
                    (e[2]+e[3]+parities[i]) % 2 == 1:
                expected.append((i, S.prod(v**n for v,n in zip(variables,e))))
    assert set(expected) == set(descriptions)
    receipt = {
        'status':'PASS',
        'target':'symmetric-sextic-residual', 'lambda':'1',
        'instance_sha256':hashlib.sha256(INSTANCE.read_bytes()).hexdigest(),
        'circuit_sha256':hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'normalizing_coefficient':'13/7',
        'exact_target_circuit_binding':True,
        'negative_weight_six_dimension':60,
        'complete_jacobian_column_count':12,
        'selected_rows':pivots,
        'selected_monomials':[basis[i] for i in pivots],
        'column_descriptions':[[str(variables[i]),str(m)] for i,m in descriptions],
        'mod5_diagonal':diagonal,
        'mod5_determinant':1,
        'exact_determinant':str(determinant),
        'jacobian_rank':12, 'quotient_dimension':48,
        'Lean_proof':False, 'full_certificate_proved':False,
        'scope':'Exact polynomial binding, complete degree-six negative Jacobian ideal, and rank only.'
    }
    path = HERE/'actual_target_jacobian_receipt.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__': main()
