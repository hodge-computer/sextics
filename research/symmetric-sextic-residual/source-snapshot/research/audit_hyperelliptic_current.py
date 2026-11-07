#!/usr/bin/env python3
"""Exact new moving-current identities and an auxiliary-cover trace cancellation.

This audits formulas, not a certificate. It does not repeat the previous PDE
or fiber-primitive searches.
"""
from pathlib import Path
import json
import sympy as s

ROOT = Path(__file__).resolve().parent
u, alpha, beta, H, Hu, Ha, Hua, J, Ja, Z = s.symbols('u alpha beta H Hu Ha Hua J Ja Z')
Dbeta = (Hua*Z+Ja)/(2*beta)
div_flux = -Dbeta/(u-alpha)
weighted_div = div_flux+beta*(Hu*Z+J)/(2*H*(u-alpha))
c = (Hua*Z+Ja)/(beta*beta)
expected = beta*(J+Hu*Z-H*c)/(2*H*(u-alpha))
assert s.cancel(weighted_div-expected) == 0

# Actual polynomial division, retaining all eight source coefficients.
h = s.symbols('h0:9')
j = s.symbols('j0:8')
c0 = s.symbols('c')
hp = sum(h[k]*u**k for k in range(9))
jp = sum(j[k]*u**k for k in range(8))
numerator = jp+s.diff(hp, u)*Z-c0*hp
coefficients = [j[k] if k < 8 else 0 for k in range(9)]
coefficients = [coefficients[k]+((k+1)*h[k+1]*Z if k < 8 else 0)-c0*h[k]
                for k in range(9)]
quotient = sum(sum(coefficients[k]*alpha**(k-r-1) for k in range(r+1, 9))*u**r
               for r in range(8))
assert s.expand(numerator-(u-alpha)*quotient-numerator.subs(u, alpha)) == 0

# Independent finite-algebra replay of the zero trace for a generic level set.
packet = json.loads((ROOT/'gauss_manin_circuit.json').read_text())['expressions']
q0, P0, Q0 = s.symbols('q P Q')
top_source = 0
for powers, (ar, ad, bi, bd) in packet['source'][8]:
    term = s.Rational(ar, ad)+s.I*s.Rational(bi, bd)
    for variable, degree in zip((q0, P0, Q0), powers):
        term *= variable**degree
    top_source += term
lx, ly = -4+18*q0, -4*P0**3+18*P0*Q0
assert s.expand(top_source-s.Rational(3, 128)*(lx-s.I*ly)) == 0
h8 = -s.Rational(729, 16)
v1 = (lx-s.I*ly)/5832
assert s.expand(top_source-(-3*h8*v1)) == 0
point = (1, 2, 3)

def evaluate(name):
    result = []
    for expression in packet[name]:
        value = 0
        for powers, (ar, ad, bi, bd) in expression:
            monomial = 1
            for coordinate, degree in zip(point, powers):
                monomial *= coordinate**degree
            value += monomial*(s.Rational(ar, ad)+s.I*s.Rational(bi, bd))
        result.append(s.expand(value))
    return result

t = s.symbols('t')
hc = evaluate('H')
jc = evaluate('Hb2')  # The Q direction. The auxiliary level f(q,P) has f_Q=0.
H_u = sum(v*u**k for k, v in enumerate(hc))
H_t = sum(v*t**k for k, v in enumerate(hc))
J_u = sum(v*u**k for k, v in enumerate(jc))
J_t = sum(v*t**k for k, v in enumerate(jc))
f = s.Integer(1+point[0]**6+point[1]**6)
A_u, A_t = H_u-f, H_t-f
Ap = s.Poly(A_t, t, domain=s.QQ_I)
assert s.gcd(Ap, Ap.diff()).degree() == 0
resolvent_numerator = s.Poly(A_u-A_t, t, domain=s.QQ_I.poly_ring(u)).exquo(
    s.Poly(u-t, t, domain=s.QQ_I.poly_ring(u)))
modulus = s.Poly(A_t, t, domain=s.QQ_I.poly_ring(u))
first = (resolvent_numerator*s.Poly(s.diff(A_t, t), t,
          domain=s.QQ_I.poly_ring(u))).rem(modulus).nth(7)/hc[8]
second = (resolvent_numerator*s.Poly(J_t, t,
           domain=s.QQ_I.poly_ring(u))).rem(modulus).nth(7)/hc[8]
assert s.expand(first-s.diff(H_u, u)) == 0
assert s.expand(second-J_u) == 0
assert s.expand(J_u*first-s.diff(H_u, u)*second) == 0

receipt = dict(
    universal_flux_identity=True,
    exact_degree_eight_division_identity=True,
    contribution_numerator_degree_bound=7,
    exact_target_leading_coefficient='3*(lX-i*lY)/128',
    exact_fiber_correction='V=(lX-i*lY)*u/5832; replace B by B-(H*Vprime-Hprime*V/2)',
    corrected_target_degree_bound=7,
    exact_source_field='Q(i)',
    target_base_point=list(point),
    auxiliary_level=f'1+q^6+P^6, specialized to {f}',
    finite_algebra_rank=8,
    finite_algebra_separable=True,
    first_trace_identity='Tr(1/(u-alpha))=Hprime(u)/(H(u)-f)',
    second_trace_identity='Tr(H_Q(alpha)/(Hprime(alpha)*(u-alpha)))=H_Q(u)/(H(u)-f)',
    resulting_normalized_source='identically zero',
    scope='Actual moving-current identity and a specific trace-cancellation obstruction. No full certificate, no unrestricted primitive obstruction, and no Lean claim.'
)
(ROOT/'hyperelliptic_current_audit.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
