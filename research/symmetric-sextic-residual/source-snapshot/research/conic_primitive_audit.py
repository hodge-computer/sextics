#!/usr/bin/env python3
"""Exact obstruction to integrating the symmetric target along one conic fiber.

This is not a certificate and does not exclude primitives with base derivatives.
The quotient coordinates are e1(X)=e1(Y)=1, e2(X)=e2(Y)=0,
z=e3(X)+1, w=e3(Y)+1. The protected F restricts to 3(z*z+w*w)-4.

Requires SymPy only to build the exact rational-function coefficient system.
The reported minor determinant is checked by ordinary integer modular arithmetic.
"""

from pathlib import Path
import json
import sympy as sp


def rref_pivots(rows, prime):
    a = [[int(v) % prime for v in row] for row in rows]
    nrows, ncols = len(a), len(a[0])
    row = 0
    pivots = []
    for col in range(ncols):
        p = next((i for i in range(row, nrows) if a[i][col]), None)
        if p is None:
            continue
        a[row], a[p] = a[p], a[row]
        inv = pow(a[row][col], -1, prime)
        a[row] = [(v * inv) % prime for v in a[row]]
        for i in range(nrows):
            if i != row and a[i][col]:
                c = a[i][col]
                a[i] = [(v - c*w) % prime for v, w in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
        if row == nrows:
            break
    return pivots


def determinant_mod(rows, prime):
    a = [[int(v) % prime for v in row] for row in rows]
    determinant = 1
    for j in range(len(a)):
        p = next((i for i in range(j, len(a)) if a[i][j]), None)
        if p is None:
            return 0
        if p != j:
            a[j], a[p] = a[p], a[j]
            determinant = -determinant
        pivot = a[j][j]
        determinant = determinant * pivot % prime
        inv = pow(pivot, -1, prime)
        for i in range(j+1, len(a)):
            c = a[i][j] * inv % prime
            a[i] = [(v-c*w) % prime for v, w in zip(a[i], a[j])]
    return determinant % prime


def main():
    u = sp.symbols('u')
    z = (u + sp.Rational(4, 3)/u)/2
    w = (u - sp.Rational(4, 3)/u)/(2*sp.I)
    r, R = z-1, w-1
    dx, dy = -4*r-27*r*r, -4*R-27*R*R
    discriminant = sp.factor(dx*dy)
    assert sp.cancel(3*(z*z+w*w)-4) == 0
    # Choose h=F as normal coordinate and u=z+i*w as the fixed fiber coordinate.
    # dr wedge dR=i/(6u) du wedge dh; r_h=1/(6u), R_h=i/(6u).
    # Differentiate i*r*R/(6u*delta) in h, where delta^2=dx*dy.
    source = sp.factor(sp.I/(36*u*u) *
                       (R+sp.I*r-r*R*((-4-54*r)/dx+sp.I*(-4-54*R)/dy)/2))
    # d(S/delta)=(S' - D'/2D*S)/delta du.
    coeff = sp.factor(-sp.diff(discriminant, u)/(2*discriminant))
    unknowns = sp.symbols('a0:5')
    # Exhaustive pole bounds: at most 2 at u=0, no other finite poles,
    # and growth at most u^2 at infinity. Branch poles of the source are simple.
    trial = sum(unknowns[j]*u**j for j in range(5))/(u*u)
    numerator = sp.together(sp.diff(trial, u)+coeff*trial-source).as_numer_denom()[0]
    equations = sp.Poly(numerator, u).all_coeffs()
    matrix, rhs = sp.linear_eq_to_matrix(equations, unknowns)
    augmented = matrix.row_join(rhs)
    pairs = []
    for i in range(augmented.rows):
        row_pairs = []
        for j in range(augmented.cols):
            a, b = sp.expand(augmented[i, j]).as_real_imag()
            assert a.is_Integer and b.is_Integer
            row_pairs.append([int(a), int(b)])
        pairs.append(row_pairs)
    witness = None
    for prime, root_i in [(5, 2), (13, 5), (17, 4), (29, 12), (37, 6)]:
        assert (root_i*root_i+1) % prime == 0
        reduced = [[(a+root_i*b) % prime for a, b in row] for row in pairs]
        coefficient_rank = len(rref_pivots([row[:-1] for row in reduced], prime))
        augmented_rank = len(rref_pivots(reduced, prime))
        if augmented_rank == 6:
            selected_rows = rref_pivots(list(map(list, zip(*reduced))), prime)
            assert len(selected_rows) == 6
            minor = [reduced[j] for j in selected_rows]
            det = determinant_mod(minor, prime)
            assert det != 0
            witness = dict(prime=prime, image_of_i=root_i,
                           coefficient_rank_mod_prime=coefficient_rank,
                           augmented_rank_mod_prime=augmented_rank,
                           selected_rows=selected_rows, determinant_mod_prime=det)
            break
    assert witness is not None
    polynomial_part = sp.together(discriminant).as_numer_denom()[0]
    assert sp.degree(polynomial_part, u) == 8
    assert sp.degree(sp.gcd(polynomial_part, sp.diff(polynomial_part, u)), u) == 0
    receipt = dict(
        scope='No primitive in the twisted conic function field for this exact fiber; not a full-target nonexistence result.',
        protected_parameters=dict(e1X=1, e1Y=1, e2X=0, e2Y=0),
        z=str(z), w=str(w), discriminant=str(discriminant),
        branch_polynomial_degree=8, branch_polynomial_squarefree=True,
        source=str(source), ode='S\' - (D\'/2D) S = source',
        trial_denominator='u^2', trial_numerator_degree_bound=4,
        matrix_shape=list(matrix.shape),
        augmented_gaussian_integer_matrix=pairs,
        exact_minor_witness=witness,
        rank_upper_bound=5,
        conclusion='The nonzero 6x6 augmented minor contradicts coefficient rank <= 5 over Q(i), hence over C.'
    )
    output = Path(__file__).with_name('conic_primitive_audit.json')
    output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k: v for k, v in receipt.items()
                      if k != 'augmented_gaussian_integer_matrix'}, indent=2))


if __name__ == '__main__':
    main()
