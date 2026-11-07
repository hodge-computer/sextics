#!/usr/bin/env python3
"""Replay one complete source/connection specialization over Q(i), without mod p."""
from pathlib import Path
import json
import sympy as s

root = Path(__file__).resolve().parent
data = json.loads((root/'gauss_manin_circuit.json').read_text())['expressions']
point = (0, 1, 0)
u = s.symbols('u')


def evaluate(name, derivatives=(0, 0, 0)):
    out = []
    for expression in data[name]:
        value = 0
        for powers, (ar, ad, bi, bd) in expression:
            monomial = 1
            for coordinate, degree, order in zip(point, powers, derivatives):
                if order > degree:
                    monomial = 0
                    break
                for t in range(order):
                    monomial *= degree-t
                monomial *= coordinate**(degree-order)
            value += monomial*(s.Rational(ar, ad)+s.I*s.Rational(bi, bd))
        out.append(s.expand(value))
    return out


def poly(values):
    return s.Poly(sum(v*u**j for j, v in enumerate(values)), u, domain=s.QQ_I)


H = poly(evaluate('H'))
Hp = H.diff()
inv = s.invert(Hp, H)
c = evaluate('c')


def reduce(P):
    V = (P*inv).mul_ground(-2).rem(H)
    half_V_Hp = (V*Hp).mul_ground(s.Rational(1, 2))
    Q, remainder = (P+half_V_Hp).div(H)
    assert remainder.is_zero
    Q -= V.diff()
    assert P == H*(Q+V.diff())-half_V_Hp
    values = [Q.nth(j) for j in range(7)]
    assert s.expand(values[3]+sum(c[j]*values[j+4] for j in range(3))) == 0
    return [values[j] for j in (0, 1, 2, 4, 5, 6)]


source = reduce(poly(evaluate('source')))
basis = [poly([1]), poly([0, 1]), poly([0, 0, 1])]
for j in range(3):
    values = [0]*(j+5)
    values[3], values[j+4] = -c[j], 1
    basis.append(poly(values))

matrices = []
for direction in range(3):
    Hb = poly(evaluate(f'Hb{direction}'))
    cb = evaluate(f'cb{direction}')
    columns = []
    for j, f in enumerate(basis):
        P = (f*Hb).mul_ground(-s.Rational(1, 2))
        # The derivative of the basis vector must be included before projecting.
        if j >= 3:
            P += H*poly([0, 0, 0, -cb[j-3]])
        columns.append(reduce(P))
    matrices.append(list(map(list, zip(*columns))))


def derivative_index(*directions):
    result = [0, 0, 0]
    for direction in directions:
        result[direction] += 1
    return tuple(result)


Hfirst = [poly(evaluate('H', derivative_index(a))) for a in range(3)]
Hsecond = [[poly(evaluate('H', derivative_index(a, b))) for b in range(3)] for a in range(3)]
cfirst = [evaluate('c', derivative_index(a)) for a in range(3)]
csecond = [[evaluate('c', derivative_index(a, b)) for b in range(3)] for a in range(3)]
for direction in range(3):
    assert Hfirst[direction] == poly(evaluate(f'Hb{direction}'))
    assert cfirst[direction] == evaluate(f'cb{direction}')
inverse_quotient = (poly([1])-Hp*inv).exquo(H)
inverse_first = [(-inv*(Hb.diff()*inv+Hb*inverse_quotient)).rem(H) for Hb in Hfirst]


def reduce_jet(P, Pa, direction):
    Ha, inva = Hfirst[direction], inverse_first[direction]
    product = (P*inv).mul_ground(-2)
    V = product.rem(H)
    L = (product-V).exquo(H)
    Va = ((Pa*inv+P*inva).mul_ground(-2)-Ha*L).rem(H)
    W = (P+(V*Hp).mul_ground(s.Rational(1, 2))).exquo(H)
    Wa = (Pa+(Va*Hp+V*Ha.diff()).mul_ground(s.Rational(1, 2))-Ha*W).exquo(H)
    Q, Qa = W-V.diff(), Wa-Va.diff()
    qv, qav = ([t.nth(j) for j in range(7)] for t in (Q, Qa))
    assert s.expand(qav[3]+sum(cfirst[direction][j]*qv[j+4]+c[j]*qav[j+4] for j in range(3))) == 0
    return [qav[j] for j in (0, 1, 2, 4, 5, 6)]


matrix_derivatives = [[None]*3 for _ in range(3)]
for a in range(3):
    for b in range(3):
        columns = []
        for j, f in enumerate(basis):
            fa = poly([0]) if j < 3 else poly([0, 0, 0, -cfirst[a][j-3]])
            fb = poly([0]) if j < 3 else poly([0, 0, 0, -cfirst[b][j-3]])
            fab = poly([0]) if j < 3 else poly([0, 0, 0, -csecond[a][b][j-3]])
            P = (f*Hfirst[b]).mul_ground(-s.Rational(1, 2))+H*fb
            Pa = (fa*Hfirst[b]+f*Hsecond[a][b]).mul_ground(-s.Rational(1, 2))+Hfirst[a]*fb+H*fab
            columns.append(reduce_jet(P, Pa, a))
        matrix_derivatives[a][b] = s.Matrix(list(map(list, zip(*columns))))
for a in range(3):
    for b in range(a):
        Ma, Mb = s.Matrix(matrices[a]), s.Matrix(matrices[b])
        curvature = matrix_derivatives[a][b]-matrix_derivatives[b][a]+Ma*Mb-Mb*Ma
        assert all(s.expand(value) == 0 for value in curvature)


def gaussian(value):
    re, im = s.expand(value).as_real_imag()
    return [int(re.p), int(re.q), int(im.p), int(im.q)]


def mod101(value):
    a, ad, b, bd = gaussian(value)
    return (a*pow(ad, -1, 101)+10*b*pow(bd, -1, 101)) % 101


previous = json.loads((root/'gauss_manin_audit.json').read_text())['first_specializations'][0]
assert list(point) == previous['point']
assert [mod101(t) for t in source] == previous['source']
assert [[[mod101(t) for t in row] for row in M] for M in matrices] == previous['connection']
receipt = dict(field='Q(i)', point=list(point), source=[gaussian(t) for t in source],
               source_pretty=[str(s.factor(t)) for t in source],
               connection=[[[gaussian(t) for t in row] for row in M] for M in matrices],
               H=[gaussian(H.nth(j)) for j in range(9)],
               inverse_of_Hprime_mod_H=[gaussian(inv.nth(j)) for j in range(8)],
               agrees_with_mod101_audit=True,
               all_three_curvature_matrices_exactly_zero=True,
               scope='Exact arithmetic verification, not a Lean proof or certificate.')
(root/'gauss_manin_exact_fiber.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k: v for k, v in receipt.items() if k in ('field', 'point', 'source_pretty', 'agrees_with_mod101_audit', 'all_three_curvature_matrices_exactly_zero', 'scope')}, indent=2))
