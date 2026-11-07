#!/usr/bin/env python3
"""Exact finite circuit for the rank-six projective genus-three connection.

The three independent base directions are q, P, Q on the chart p=1.
This computes a sufficient primitive ansatz, not a full certificate. A primitive
with new fiber poles may require an enlarged logarithmic connection.
"""

from pathlib import Path
import json
import random
import itertools
import sympy as sp

HERE = Path(__file__).resolve().parent


def build_symbolic():
    u, q, P, Q, h = sp.symbols('u q P Q h')
    p = sp.Integer(1)
    a, b = p**3-2*p*q, P**3-2*P*Q
    remainder = lambda p, q: -2*p**6+6*p**4*q-3*p*p*q*q-2*q**3
    K = remainder(p, q)+remainder(P, Q)+sp.Rational(5, 7)*q*q*Q+sp.Rational(10, 7)*q*Q*Q
    k = -K/3
    rx = (u*u+k)/2-a*u
    ry = (u*u-k)/(2*sp.I)-b*u
    cx, cy = p*p*q*q-4*q**3, P*P*Q*Q-4*Q**3
    lx, ly = -4*p**3+18*p*q, -4*P**3+18*P*Q
    dx = cx*u*u+lx*u*rx-27*rx*rx
    dy = cy*u*u+ly*u*ry-27*ry*ry
    H = sp.Poly(sp.expand(dx*dy), u)
    source = sp.Poly(sp.expand(sp.I/72 *
        (ry*(2*cx*u+lx*rx)*dy+sp.I*rx*dx*(2*cy*u+ly*ry))), u)
    assert H.degree() == 8 and H.LC() == -sp.Rational(729, 16)
    assert source.degree() <= 8
    print('Built the generic degree-eight curve and source.', flush=True)
    h8, h7, h6, h5 = (H.nth(j) for j in (8, 7, 6, 5))
    c = [-h7/(2*h8), 3*h7*h7/(8*h8*h8)-h6/(2*h8),
         -5*h7**3/(16*h8**3)+3*h7*h6/(4*h8*h8)-h5/(2*h8)]
    base = (q, P, Q)
    expr = {'H': [H.nth(j) for j in range(9)],
            'source': [source.nth(j) for j in range(9)],
            'c': c,
            'k': [k]}
    for j, parameter in enumerate(base):
        expr[f'Hb{j}'] = [sp.diff(H.nth(t), parameter) for t in range(9)]
        expr[f'cb{j}'] = [sp.diff(t, parameter) for t in c]
    data = {}
    for name, values in expr.items():
        data[name] = []
        for value in values:
            terms = []
            for powers, coefficient in sp.Poly(sp.expand(value), *base).terms():
                re, im = sp.expand(coefficient).as_real_imag()
                assert re.is_Rational and im.is_Rational
                terms.append([list(powers), [int(re.p), int(re.q), int(im.p), int(im.q)]])
            data[name].append(terms)
    print('Encoded the generic coefficient circuits.', flush=True)
    # Independently check the geometric coordinate and source-density formulas.
    aa, bb, kk = sp.symbols('aa bb kk')
    r = (u+(kk+h/3)/u)/2-aa
    R = (u-(kk+h/3)/u)/(2*sp.I)-bb
    p6 = lambda p, q, r: p**6-6*p**4*q+9*p*p*q*q-2*q**3+6*p**3*r-12*p*q*r+3*r*r
    pp, qq, rr = sp.symbols('pp qq rr')
    assert sp.expand(p6(pp, qq, rr)-3*(rr+pp**3-2*pp*qq)**2-remainder(pp, qq)) == 0
    assert sp.expand(3*((r+aa)**2+(R+bb)**2-kk)-h) == 0
    determinant = sp.diff(r, u)*sp.diff(R, h)-sp.diff(r, h)*sp.diff(R, u)
    assert sp.cancel(determinant-sp.I/(6*u)) == 0
    # Avoid expanding a rational square root: differentiate its square D instead.
    rr, RR, ccx, ccy, llx, lly = sp.symbols('rr RR ccx ccy llx lly')
    Dx, Dy = ccx+llx*rr-27*rr*rr, ccy+lly*RR-27*RR*RR
    rh, Rh = 1/(6*u), sp.I/(6*u)
    Dh = (llx-54*rr)*rh*Dy+Dx*(lly-54*RR)*Rh
    differentiated_times_D = sp.I/(6*u)*(rh*RR+rr*Rh)*Dx*Dy-sp.I/(12*u)*rr*RR*Dh
    compact_source = sp.I/72*u**4*(RR*(2*ccx+llx*rr)*Dy+sp.I*rr*Dx*(2*ccy+lly*RR))
    assert sp.expand(u**6*differentiated_times_D-compact_source) == 0
    packet = dict(
        coefficient_field='Q(i)(q,P,Q), i^2=-1; p=1',
        variables=['q', 'P', 'Q'],
        coefficient_encoding='Sparse monomials q^a P^b Q^c with Gaussian rational coefficients',
        expressions=data,
        verified_identities=['protected F becomes h', 'Jacobian dr,dR / du,dh = i/(6u)',
                             'actual double-pole residue equals source/(H*y), y^2=H'],
        connection_formula="Reduce(-f_j*partial_b H/2) + partial_b f_j, where Reduce(P) uses V=-2P*(H')^(-1) mod H and Q=(P+VH'/2)/H-V'.",
        basis=['1', 'u', 'u^2', 'u^4-c1*u^3', 'u^5-c2*u^3', 'u^6-c3*u^3'],
        residue_constraint='q3+c1*q4+c2*q5+c3*q6=0',
        primitive_equation='v = partial_q U + Mq U + partial_P V + MP V + partial_Q W + MQ W',
        scope='Sufficient rank-six second-kind ansatz. New horizontal poles can require logarithmic residue classes outside this module.'
    )
    (HERE/'gauss_manin_circuit.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


class FiniteCircuit:
    def __init__(self, packet, prime=101, image_i=10):
        self.data = packet['expressions']
        self.p, self.ii = prime, image_i
        assert (image_i*image_i+1) % prime == 0

    def add(self, a, b):
        return trim([
                         ((a[j] if j < len(a) else 0)+(b[j] if j < len(b) else 0)) % self.p
                         for j in range(max(len(a), len(b)))])

    def scale(self, a, c):
        return trim([x*c % self.p for x in a])

    def mul(self, a, b):
        if not a or not b:
            return []
        out = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i+j] = (out[i+j]+x*y) % self.p
        return trim(out)

    def divmod(self, a, b):
        a = trim([x % self.p for x in a]); b = trim(b)
        assert b
        out = [0]*max(0, len(a)-len(b)+1)
        inv = pow(b[-1], -1, self.p)
        while len(a) >= len(b):
            j = len(a)-len(b); c = a[-1]*inv % self.p
            out[j] = c
            for k, v in enumerate(b):
                a[j+k] = (a[j+k]-c*v) % self.p
            a = trim(a)
        return trim(out), a

    def rem(self, a, h):
        return self.divmod(a, h)[1]

    def diff(self, a):
        return trim([j*a[j] % self.p for j in range(1, len(a))])

    def inverse(self, a, h):
        r0, r1, s0, s1 = h, self.rem(a, h), [], [1]
        while r1:
            q, r = self.divmod(r0, r1)
            r0, r1 = r1, r
            s0, s1 = s1, self.add(s0, self.scale(self.mul(q, s1), -1))
        if len(r0) != 1:
            raise ValueError('Singular fiber')
        return self.rem(self.scale(s0, pow(r0[0], -1, self.p)), h)

    def evaluate(self, key, point):
        out = []
        for expr in self.data[key]:
            value = 0
            for powers, (ar, ad, bi, bd) in expr:
                coefficient = (ar*pow(ad, -1, self.p)+self.ii*bi*pow(bd, -1, self.p)) % self.p
                for parameter, degree in zip(point, powers):
                    coefficient = coefficient*pow(parameter, degree, self.p) % self.p
                value = (value+coefficient) % self.p
            out.append(value)
        return out

    def reduction(self, numerator, h, hp, invhp):
        v = self.scale(self.rem(self.mul(numerator, invhp), h), -2)
        q, remainder = self.divmod(self.add(numerator, self.scale(self.mul(v, hp), pow(2, -1, self.p))), h)
        assert not remainder
        q = self.add(q, self.scale(self.diff(v), -1))
        # Exact Hermite identity, independently reconstructed in the polynomial ring.
        rhs = self.add(self.mul(h, self.add(q, self.diff(v))),
                       self.scale(self.mul(v, hp), -pow(2, -1, self.p)))
        assert trim(numerator) == rhs
        assert len(q) <= 7
        return q+[0]*(7-len(q))

    def determinant(self, matrix):
        a = [list(row) for row in matrix]; det = 1
        for j in range(len(a)):
            selected = next((i for i in range(j, len(a)) if a[i][j] % self.p), None)
            if selected is None:
                return 0
            if selected != j:
                a[selected], a[j] = a[j], a[selected]; det = -det
            pivot = a[j][j] % self.p; det = det*pivot % self.p
            inv = pow(pivot, -1, self.p)
            for i in range(j+1, len(a)):
                c = a[i][j]*inv % self.p
                a[i] = [(v-c*w) % self.p for v, w in zip(a[i], a[j])]
        return det % self.p

    def norm(self, t, h):
        columns = []
        for j in range(8):
            c = self.rem([0]*j+t, h)
            columns.append(c+[0]*(8-len(c)))
        return self.determinant(list(map(list, zip(*columns))))

    def trace(self, t, h):
        value = 0
        for j in range(8):
            c = self.rem([0]*j+t, h)
            value += c[j] if len(c) > j else 0
        return value % self.p

    def at(self, point):
        h = self.evaluate('H', point); hp = self.diff(h)
        invhp = self.inverse(hp, h)
        c = self.evaluate('c', point)
        basis = [[1], [0, 1], [0, 0, 1]]
        for j in range(3):
            t = [0]*(j+5); t[3] = -c[j] % self.p; t[j+4] = 1
            basis.append(t)
        def project(v):
            assert (v[3]+sum(c[j]*v[j+4] for j in range(3))) % self.p == 0
            return [v[j] for j in (0, 1, 2, 4, 5, 6)]
        source = project(self.reduction(self.evaluate('source', point), h, hp, invhp))
        matrices = []; logarithmic_derivatives = []
        for direction in range(3):
            hb = self.evaluate(f'Hb{direction}', point)
            cb = self.evaluate(f'cb{direction}', point)
            columns = []
            for j, f in enumerate(basis):
                v = self.reduction(self.scale(self.mul(f, hb), -pow(2, -1, self.p)), h, hp, invhp)
                if j >= 3:
                    v[3] = (v[3]-cb[j-3]) % self.p
                columns.append(project(v))
            matrices.append(list(map(list, zip(*columns))))
            # d log Norm(H') = trace(H'_b/H' - H'' H_b/(H')^2).
            t = self.add(self.mul(self.diff(hb), invhp), self.scale(
                self.mul(self.mul(self.diff(hp), hb), self.mul(invhp, invhp)), -1))
            logarithmic_derivatives.append(self.trace(self.rem(t, h), h))
        return dict(point=list(point), source=source, connection=matrices,
                    discriminant_norm=self.norm(hp, h),
                    discriminant_log_derivatives=logarithmic_derivatives,
                    c=c, H=h, source_numerator=self.evaluate('source', point))


def monomials(degree):
    return [m for d in range(degree+1) for m in itertools.product(range(d+1), repeat=3) if sum(m) == d]


def incremental_system(rows, rhs, pivots, nvars, prime):
    """Insert exact field equations; report rank and the first inconsistency."""
    for row, value in zip(rows, rhs):
        row = list(row)+[value]
        for pivot in sorted(pivots):
            c = row[pivot]
            if c:
                row = [(v-c*w) % prime for v, w in zip(row, pivots[pivot])]
        pivot = next((j for j in range(nvars) if row[j]), None)
        if pivot is None:
            if row[-1]:
                return False
            continue
        inv = pow(row[pivot], -1, prime)
        pivots[pivot] = [v*inv % prime for v in row]
    return True


def search(circuit, samples, degree, denominator_power):
    ms = monomials(degree); nvars = 18*len(ms); pivots = {}
    for count, data in enumerate(samples, 1):
        point = data['point']; delta = data['discriminant_norm']
        rows = [[0]*nvars for _ in range(6)]
        column = 0
        for direction in range(3):
            M = data['connection'][direction]
            logd = data['discriminant_log_derivatives'][direction]
            for component in range(6):
                for m in ms:
                    value = 1
                    for a, b in zip(point, m):
                        value = value*pow(a, b, circuit.p) % circuit.p
                    derivative = 0
                    if m[direction]:
                        derivative = m[direction]
                        for j, (a, b) in enumerate(zip(point, m)):
                            derivative = derivative*pow(a, b-(j == direction), circuit.p) % circuit.p
                    for row in range(6):
                        entry = M[row][component]*value
                        if row == component:
                            entry += derivative-denominator_power*logd*value
                        rows[row][column] = entry % circuit.p
                    column += 1
        rhs = [v*pow(delta, denominator_power, circuit.p) % circuit.p for v in data['source']]
        if not incremental_system(rows, rhs, pivots, nvars, circuit.p):
            return dict(numerator_total_degree=degree, discriminant_pole_power=denominator_power,
                        unknowns=nvars, samples_used=count, coefficient_rank=len(pivots),
                        outcome='inconsistent over the stated finite field',
                        characteristic_zero_exclusion_by_full_column_rank=(len(pivots) == nvars))
    return dict(numerator_total_degree=degree, discriminant_pole_power=denominator_power,
                unknowns=nvars, samples_used=len(samples), coefficient_rank=len(pivots),
                outcome='no inconsistency found; not a verified primitive')


def main():
    path = HERE/'gauss_manin_circuit.json'
    packet = json.loads(path.read_text()) if path.exists() else build_symbolic()
    c = FiniteCircuit(packet)
    rng = random.Random(218)
    samples = []
    for point in [(0, 1, 0), (1, 2, 3), (2, 1, 1)]:
        try:
            samples.append(c.at(point))
        except ValueError:
            pass
    while len(samples) < 100:
        point = tuple(rng.randrange(c.p) for _ in range(3))
        try:
            samples.append(c.at(point))
        except ValueError:
            continue
    trials = [search(c, samples, degree, power) for power in (0, 1)
              for degree in (0, 1, 2, 3)]
    receipt = dict(prime=c.p, image_of_i=c.ii,
                   exact_specialization_count=len(samples),
                   checked_at_every_sample=['Hermite polynomial identities', 'all source and connection residues vanish'],
                   first_specializations=samples[:3],
                   compact_primitive_trials=trials,
                   scope='Finite-field searches in specified ansatzes; no unrestricted nonexistence claim and no Lean certificate.')
    (HERE/'gauss_manin_audit.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'first_specializations'}, indent=2))


if __name__ == '__main__':
    main()
