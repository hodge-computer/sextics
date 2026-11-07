#!/usr/bin/env python3
"""Build/audit the exact symmetric target's 25+2 norm-contact equations.

Portable inputs: symmetric_norm_contact_inputs.json, copied from protected
instance.rec and the adjacent general_cubic_current.py. Build/audit needs
SymPy. Evaluating the generated rational circuit uses only Python's stdlib.
No incidence point, dominance, finiteness, etaleness, or trace identity is
asserted. The 19x19 inverse is retained as an explicit linear-solve gate.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import ast
import hashlib
import json
import random
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'python_deps'))


class Circuit:
    def __init__(self):
        self.nodes = []
        self.memo = {}
        self.solves = []
        self.zero = self.const(0)
        self.one = self.const(1)

    def node(self, op, data):
        key = (op, tuple(data) if isinstance(data, list) else data)
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append({'op': op, 'data': data})
        return self.memo[key]

    def const(self, value):
        value = Fraction(value)
        return self.node('rational', [value.numerator, value.denominator])

    def var(self, name):
        return self.node('variable', name)

    def add(self, *args):
        pending = []
        rational = Fraction(0)
        for a in args:
            n = self.nodes[a]
            if n['op'] == 'rational':
                rational += Fraction(*n['data'])
            elif n['op'] == 'add':
                pending.extend(n['data'])
            else:
                pending.append(a)
        if rational:
            pending.append(self.const(rational))
        if not pending:
            return self.zero
        if len(pending) == 1:
            return pending[0]
        return self.node('add', sorted(pending))

    def mul(self, *args):
        pending = []
        rational = Fraction(1)
        for a in args:
            n = self.nodes[a]
            if n['op'] == 'rational':
                rational *= Fraction(*n['data'])
            elif n['op'] == 'multiply':
                pending.extend(n['data'])
            else:
                pending.append(a)
        if not rational:
            return self.zero
        if rational != 1:
            pending.append(self.const(rational))
        if not pending:
            return self.one
        if len(pending) == 1:
            return pending[0]
        return self.node('multiply', sorted(pending))

    def neg(self, a):
        return self.mul(self.const(-1), a)

    def pow(self, a, degree):
        if degree == 0:
            return self.one
        if degree == 1:
            return a
        n = self.nodes[a]
        if n['op'] == 'rational':
            return self.const(Fraction(*n['data'])**degree)
        return self.node('power', [a, degree])

    def inv(self, a):
        return self.node('inverse', a)


def monomials(degree, parity=None):
    return sorted(e for e in product(range(degree+1), repeat=4)
                  if sum(e) == degree and
                  (parity is None or (e[2]+e[3]) % 2 == parity))


QBASE = [(2,0,0,0), (0,2,0,0), (0,0,2,0), (0,0,1,1), (0,0,0,2)]
ABASE = [(3,0,0,0), (0,3,0,0), (1,0,2,0), (1,0,1,1),
         (1,0,0,2), (0,1,2,0), (0,1,1,1), (0,1,0,2)]
BBASE = [(2,0,1,0), (2,0,0,1), (0,2,1,0), (0,2,0,1),
         (0,0,3,0), (0,0,2,1), (0,0,1,2), (0,0,0,3)]
AB = (1,1,0,0)


def build_circuit(inputs):
    C = Circuit()

    def add(*polynomials):
        out = {}
        for p in polynomials:
            for e, v in p.items():
                out[e] = C.add(out.get(e, C.zero), v)
        return {e: v for e, v in out.items() if v != C.zero}

    def scale(p, c):
        return {e: C.mul(v, c) for e, v in p.items() if C.mul(v, c) != C.zero}

    def mul(p, q):
        out = {}
        for e, v in p.items():
            for f, w in q.items():
                k = tuple(a+b for a, b in zip(e, f))
                out[k] = C.add(out.get(k, C.zero), C.mul(v, w))
        return {e: v for e, v in out.items() if v != C.zero}

    def power(p, n):
        out = {(0,)*len(next(iter(p))): C.one}
        for _ in range(n):
            out = mul(out, p)
        return out

    def coordinate(n, i):
        return {tuple(int(k == i) for k in range(n)): C.one}

    def evaluate(p, values):
        return C.add(*(C.mul(v, *(C.pow(x, d) for x, d in zip(values, e)))
                       for e, v in p.items()))

    def encode(p):
        return [{'exponent': list(e), 'coefficient_node': p[e]} for e in sorted(p)]

    lam = C.var('lam')
    rho = [C.var(f'rho{i}') for i in range(5)]
    mu = [C.var(f'mu{i}') for i in range(5)]
    aa = [C.var(f'A{i}') for i in range(8)]
    bb = [C.var(f'B{i}') for i in range(8)]
    Q1 = dict(zip(QBASE, rho))
    Q2 = {AB: C.one, **dict(zip(QBASE, mu))}
    A, B = dict(zip(ABASE, aa)), dict(zip(BBASE, bb))
    a, b, c, d, u = [coordinate(5, i) for i in range(5)]
    qx = add(power(a, 2), scale(mul(a, b), C.const(2)), scale(u, C.const(-1)))
    qy = add(power(c, 2), scale(mul(c, d), C.const(2)), scale(u, C.neg(C.pow(lam, 2))))
    raw = add(
        scale(power(a, 6), C.const(2)), power(b, 6),
        scale(power(c, 6), C.const(2)), power(d, 6),
        scale(mul(power(a, 4), u), C.const(30)),
        scale(mul(power(a, 2), power(u, 2)), C.const(30)),
        scale(power(u, 3), C.const(2)),
        scale(mul(power(c, 4), u), C.mul(C.const(30), C.pow(lam, 2))),
        scale(mul(power(c, 2), power(u, 2)), C.mul(C.const(30), C.pow(lam, 4))),
        scale(power(u, 3), C.mul(C.const(2), C.pow(lam, 6))),
        scale(mul(power(qx, 2), qy), C.const(Fraction(5, 7))),
        scale(mul(qx, power(qy, 2)), C.const(Fraction(10, 7))))
    ell = raw[(0,0,0,0,3)]
    monic = scale(raw, C.inv(ell))
    lift = lambda p: {e+(0,): v for e,v in p.items()}
    h2 = {e[:4]: v for e,v in monic.items() if e[4] == 2}
    h4 = {e[:4]: v for e,v in monic.items() if e[4] == 1}
    q1_weighted = add(u, lift(Q1))
    g1_weighted = add(power(u,2), mul(lift(h2),u),
        scale(mul(lift(Q1),u),C.const(-1)),lift(power(Q1,2)),
        scale(lift(mul(h2,Q1)),C.const(-1)),lift(h4))
    powers = [power(scale(Q1, C.const(-1)), k) for k in range(4)]
    substituted = add(*(mul({e[:4]: v}, powers[e[4]]) for e, v in monic.items()))
    R = add(substituted, scale(power(A, 2), C.const(-1)), power(B, 2))
    mult = monomials(4, 0)
    output = monomials(6, 0)
    pivot = [tuple(x+y for x, y in zip(AB, e)) for e in mult]
    free = [e for e in output if not (e[0] and e[1])]
    assert len(mult) == 19 and len(output) == 44 and len(free) == 25
    assert set(R) <= set(output)
    assert set(ABASE) == {e for e in monomials(3, 0) if not(e[0] and e[1])}
    assert set(BBASE) == {e for e in monomials(3, 1) if not(e[0] and e[1])}

    def matrix(rows):
        return [[Q2.get(tuple(x-y for x, y in zip(e, m)), C.zero) for m in mult]
                for e in rows]

    M, Mf = matrix(pivot), matrix(free)
    Rp, Rf = [R.get(e, C.zero) for e in pivot], [R.get(e, C.zero) for e in free]
    C.solves.append({'matrix_nodes': M, 'rhs_nodes': Rp,
                     'meaning': '19 quartic quotient coefficients, M*v=R_pivot'})
    v = [C.node('solve_entry', [0, j]) for j in range(19)]
    equations = [C.add(t, C.neg(C.add(*(C.mul(a, b) for a, b in zip(row, v)))))
                 for t, row in zip(Rf, Mf)]
    z = C.mul(mu[0], mu[1])
    cubic_delta = C.add(C.one, C.neg(z))
    delta = C.mul(cubic_delta, C.add(C.one, C.mul(C.const(-3), z)),
                  C.pow(C.add(C.one, C.mul(C.const(-2), z)), 3))
    r, ss, alpha = [C.var(t) for t in ('r', 's', 'alpha')]
    point = [C.one, r, alpha, C.mul(ss, alpha)]
    qpoint = evaluate(Q2, point)
    apoint, bpoint = evaluate(A, point), evaluate(B, point)
    hpoint = C.add(apoint, bpoint)
    kpoint = C.add(apoint, C.neg(bpoint))
    beta = C.neg(evaluate(Q1, point))
    point_g = evaluate(monic, point+[beta])
    quotient_point = evaluate(dict(zip(mult, v)), point)
    remainder_point = evaluate(dict(zip(free, equations)), point)
    point_rhs = C.add(remainder_point, C.mul(qpoint, quotient_point), C.mul(hpoint, kpoint))
    names = [f'rho{i}' for i in range(5)]+[f'mu{i}' for i in range(5)]+\
            [f'A{i}' for i in range(8)]+[f'B{i}' for i in range(8)]
    return {
        'schema': 'symmetric-norm-contact-arithmetic-circuit-v1',
        'input_snapshot': inputs,
        'coefficient_field_norm_chart': 'Q(lam)',
        'coefficient_field_moving_point': 'Q(lam,r,s)',
        'ambient_variables': ['a','b','c','d','u'],
        'ambient_weights': [1,1,1,1,2],
        'involution': '(a,b,c,d,u) -> (a,b,-c,-d,u)',
        'parameter_order': names,
        'moving_unknown_order': names+['alpha'],
        'normalization': 'G=G_raw/ell; G_raw is exactly the protected F after the reflection-pencil substitution.',
        'polynomials': {name: encode(p) for name, p in [('G_raw',raw),('G',monic),
            ('Q1',Q1),('Q2',Q2),('A',A),('B',B),('R',R),
            ('f1_weighted',q1_weighted),('g1_weighted',g1_weighted),
            ('g2_quartic',dict(zip(mult,v)))]},
        'ell_node': ell,
        'localization_Delta_node': delta,
        'cubic_reduction_determinant_node': cubic_delta,
        'required_opens': ['ell != 0','Delta != 0'],
        'quartic_multiplier_basis': [list(e) for e in mult],
        'sextic_pivot_basis': [list(e) for e in pivot],
        'sextic_free_basis': [list(e) for e in free],
        'M_pivot': M, 'M_free': Mf,
        'R_pivot': Rp, 'R_free': Rf,
        'quartic_quotient_nodes': v,
        'norm_equation_nodes': equations,
        'point_q_node': qpoint, 'point_h_node': hpoint, 'point_beta_node': beta,
        'point_conjugate_h_node': kpoint,
        'all_equation_nodes': equations+[qpoint,hpoint],
        'point_binding': {'left_G_at_point_node': point_g,
            'right_equation_combination_node': point_rhs,
            'quartic_quotient_at_point_node': quotient_point,
            'norm_remainder_at_point_node': remainder_point,
            'identity': 'G(1,r,alpha,s*alpha,beta) = sum E_i*m_i(point) + Q2(point)*quartic_quotient(point) + (A+B)(point)*(A-B)(point)',
            'current_coordinates': 'w=beta, x=alpha^2 in the exact monic cubic from general_cubic_current.py'},
        'full_presentation_identity': 'G = (u+Q1)*g1 + Q2*g2 + A^2-B^2 + sum_i E_i*m_i(a,b,c,d)',
        'g1_formula': 'G=u^3+h2*u^2+h4*u+h6; g1=u^2+(h2-Q1)*u+(Q1^2-h2*Q1+h4)',
        'norm_equation_count':25, 'moving_equation_count':27,
        'nodes': C.nodes, 'linear_solves': C.solves,
        'scope': 'Explicit equation circuit only. No nonempty component, dominance, finite/etale algebra, closed residue form, trace/source identity, or certificate is asserted.'}


def linear_solve(matrix, rhs):
    a = [[Fraction(x) for x in row]+[Fraction(b)] for row, b in zip(matrix, rhs)]
    for j in range(len(a)):
        p = next((i for i in range(j,len(a)) if a[i][j]), None)
        if p is None:
            raise ValueError('Outside the inverse-matrix chart: Delta=0')
        a[p], a[j] = a[j], a[p]
        c = a[j][j]; a[j] = [v/c for v in a[j]]
        for i in range(len(a)):
            if i != j and a[i][j]:
                c = a[i][j]; a[i] = [v-c*w for v,w in zip(a[i],a[j])]
    return [row[-1] for row in a]


def evaluate_circuit(packet, assignments):
    """Stdlib-only exact rational evaluator for the portable circuit JSON."""
    values, solutions = [], {}
    for node in packet['nodes']:
        op, data = node['op'], node['data']
        if op == 'rational': v = Fraction(*data)
        elif op == 'variable': v = Fraction(assignments[data])
        elif op == 'add': v = sum((values[i] for i in data), Fraction(0))
        elif op == 'multiply':
            v = Fraction(1)
            for i in data: v *= values[i]
        elif op == 'power': v = values[data[0]]**data[1]
        elif op == 'inverse': v = 1/values[data]
        elif op == 'solve_entry':
            sid, index = data
            if sid not in solutions:
                solve = packet['linear_solves'][sid]
                M = [[values[i] for i in row] for row in solve['matrix_nodes']]
                rhs = [values[i] for i in solve['rhs_nodes']]
                solutions[sid] = linear_solve(M, rhs)
                assert all(sum(a*b for a,b in zip(row,solutions[sid])) == v for row,v in zip(M,rhs))
            v = solutions[sid][index]
        else: raise ValueError(op)
        values.append(v)
    return values


def arithmetic_expression(source, names, sp):
    """Parse only arithmetic; never execute source text."""
    def visit(n):
        if isinstance(n, ast.Constant) and type(n.value) is int: return sp.Integer(n.value)
        if isinstance(n, ast.Name) and n.id in names: return names[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub): return -visit(n.operand)
        if isinstance(n, ast.BinOp):
            a,b=visit(n.left),visit(n.right)
            if isinstance(n.op, ast.Add): return a+b
            if isinstance(n.op, ast.Sub): return a-b
            if isinstance(n.op, ast.Mult): return a*b
            if isinstance(n.op, ast.Div): return a/b
            if isinstance(n.op, ast.Pow): return a**b
        raise ValueError(ast.dump(n))
    return visit(ast.parse(source, mode='eval').body)


def audit(packet):
    import sympy as sp
    inputs=packet['input_snapshot']
    a,b,c,d,u,z,lam,r,ss,t,w,x=sp.symbols('a b c d u z lam r s t w x')
    coords=(a,b,c,d)
    qx=a*a+2*a*b-u; qy=c*c+2*c*d-lam**2*u
    Graw=2*a**6+b**6+2*c**6+d**6+30*a**4*u+30*a*a*u*u+2*u**3+\
        30*lam**2*c**4*u+30*lam**4*c*c*u*u+2*lam**6*u**3+\
        sp.Rational(5,7)*qx*qx*qy+sp.Rational(10,7)*qx*qy*qy
    ell=sp.expand(Graw).coeff(u,3)
    symbolic_cache={}
    def symbolic_node(index):
        if index in symbolic_cache:return symbolic_cache[index]
        node=packet['nodes'][index];op,data=node['op'],node['data']
        if op=='rational':value=sp.Rational(*data)
        elif op=='variable':value=sp.Symbol(data)
        elif op=='add':value=sum(symbolic_node(j) for j in data)
        elif op=='multiply':value=sp.prod(symbolic_node(j) for j in data)
        elif op=='power':value=symbolic_node(data[0])**data[1]
        elif op=='inverse':value=1/symbolic_node(data)
        else:raise ValueError('Do not symbolically expand the inverse-matrix gate')
        symbolic_cache[index]=value;return value
    dag_raw=sum(symbolic_node(term['coefficient_node'])*sp.prod(
        v**e for v,e in zip((a,b,c,d,u),term['exponent']))
        for term in packet['polynomials']['G_raw'])
    assert sp.expand(dag_raw-Graw)==0
    names=dict(zip(('X0','X1','X2','Y0','Y1','Y2'),sp.symbols('X0 X1 X2 Y0 Y1 Y2')))
    protected=arithmetic_expression(inputs['protected_F'],names,sp)
    physical=[a+z,a-z,b,c+lam*z,c-lam*z,d]
    assert sp.expand(protected.subs(dict(zip(names.values(),physical)), simultaneous=True)-Graw.subs(u,z*z))==0
    source=arithmetic_expression(inputs['protected_A'],names,sp)
    assert sp.expand(source.subs(dict(zip(names.values(),physical)), simultaneous=True)-
                     (a*a-z*z)*b*(c*c-lam*lam*z*z)*d)==0
    n={'r':r,'s':ss,'lam':lam,'x':x,'w':w,'kappa':sp.Rational(5,7)}
    n['Q']=arithmetic_expression(inputs['current_Q'],n,sp)
    n['P']=arithmetic_expression(inputs['current_P'],n,sp)
    current=arithmetic_expression(inputs['current_exact_G'],n,sp)
    chart=Graw.subs({a:1,b:r,c:t,d:ss*t,u:w},simultaneous=True)
    assert sp.expand(chart-current.subs(x,t*t))==0
    assert sp.expand(ell-arithmetic_expression(inputs['current_leading_coefficient'],n,sp))==0
    monic=w**3+sum(arithmetic_expression(value,n,sp)*w**int(key[1])*x**int(key[2])
                   for key,value in inputs['current_monic_coefficients'].items())
    assert sp.cancel(current-ell*monic)==0
    uu,qq,cc2,cc4,cc6=sp.symbols('uu qq cc2 cc4 cc6')
    generic_cubic=uu**3+cc2*uu**2+cc4*uu+cc6
    generic_g1=uu**2+(cc2-qq)*uu+qq**2-cc2*qq+cc4
    assert sp.expand(generic_cubic-generic_cubic.subs(uu,-qq)-(uu+qq)*generic_g1)==0
    rho=sp.symbols('rho0:5');mu=sp.symbols('mu0:5')
    aa=sp.symbols('A0:8');bb=sp.symbols('B0:8')
    mon=lambda e: sp.prod(v**n for v,n in zip(coords,e))
    Q1=sum(v*mon(e) for v,e in zip(rho,QBASE))
    Q2=a*b+sum(v*mon(e) for v,e in zip(mu,QBASE))
    A=sum(v*mon(e) for v,e in zip(aa,ABASE)); B=sum(v*mon(e) for v,e in zip(bb,BBASE))
    def dag_polynomial(name,variables):
        return sum(symbolic_node(term['coefficient_node'])*sp.prod(v**e for v,e in
            zip(variables,term['exponent'])) for term in packet['polynomials'][name])
    for name,literal in [('Q1',Q1),('Q2',Q2),('A',A),('B',B)]:
        assert sp.expand(dag_polynomial(name,coords)-literal)==0
    # Bind every emitted remainder coefficient symbolically, without opening
    # the inverse matrix or introducing giant rational contact equations.
    literal_R_numerator=sp.Poly(sp.expand(Graw.subs(u,-Q1)-ell*A*A+ell*B*B),*coords).as_dict()
    dag_R={tuple(term['exponent']):term['coefficient_node']
           for term in packet['polynomials']['R']}
    for e in set(literal_R_numerator)|set(dag_R):
        actual=ell*symbolic_node(dag_R[e]) if e in dag_R else 0
        assert sp.cancel(actual-literal_R_numerator.get(e,0))==0
    h2=sp.expand(Graw).coeff(u,2)/ell
    h4=sp.expand(Graw).coeff(u,1)/ell
    literal_g1=u*u+(h2-Q1)*u+Q1*Q1-h2*Q1+h4
    assert sp.cancel(dag_polynomial('g1_weighted',coords+(u,))-literal_g1)==0
    assert sp.expand(dag_polynomial('f1_weighted',coords+(u,))-(u+Q1))==0
    qdict=sp.Poly(Q2,*coords).as_dict()
    mult=[tuple(e) for e in packet['quartic_multiplier_basis']]
    piv=[tuple(e) for e in packet['sextic_pivot_basis']]
    free=[tuple(e) for e in packet['sextic_free_basis']]
    M=sp.Matrix([[qdict.get(tuple(a-b for a,b in zip(e,m)),0) for m in mult] for e in piv])
    for rows,nodes in [(piv,packet['M_pivot']),(free,packet['M_free'])]:
        for e,row in zip(rows,nodes):
            for m,node in zip(mult,row):
                assert sp.expand(symbolic_node(node)-qdict.get(tuple(x-y for x,y in zip(e,m)),0))==0
    groups={}
    for i,e in enumerate(mult):groups.setdefault((e[2],e[3]),[]).append(i)
    ordered=sorted(groups,key=lambda cd:(sum(cd),cd))
    for gi,key in enumerate(ordered):
        for other in ordered[gi+1:]:
            assert all(M[i,j]==0 for i in groups[key] for j in groups[other])
    det=sp.prod(M.extract(groups[key],groups[key]).det() for key in ordered)
    delta=(1-mu[0]*mu[1])*(1-3*mu[0]*mu[1])*(1-2*mu[0]*mu[1])**3
    assert sp.expand(det-delta)==0
    cubic_mult=monomials(1)
    Mc=sp.Matrix([[qdict.get(tuple(x-y for x,y in zip(tuple(a+b for a,b in zip(AB,e)),m)),0)
                  for m in cubic_mult] for e in cubic_mult])
    assert sp.expand(Mc.det()-(1-mu[0]*mu[1]))==0
    # Universal multiplication-map verification, independent of the target.
    vv=sp.symbols('v0:19')
    qprod=sp.Poly(sp.expand(Q2*sum(v*mon(e) for v,e in zip(vv,mult))),*coords).as_dict()
    for e in monomials(6,0):
        predicted=sum(qdict.get(tuple(x-y for x,y in zip(e,m)),0)*v for m,v in zip(mult,vv))
        assert sp.expand(qprod.get(e,0)-predicted)==0
    numeric=[];rng=random.Random(218219)
    symbolicR=(Graw/ell).subs(u,-Q1)-A*A+B*B
    for trial in range(4):
        env={name:Fraction(rng.randrange(-2,3)) for name in packet['parameter_order']}
        env.update(lam=Fraction(trial),r=Fraction(trial+1),s=Fraction(2-trial),alpha=Fraction(trial+2))
        env['mu0'],env['mu1']=[(0,0),(1,Fraction(1,4)),(2,-1),(-1,1)][trial]
        values=evaluate_circuit(packet,env)
        assert values[packet['ell_node']] and values[packet['localization_Delta_node']]
        substitutions={sp.Symbol(k):sp.Rational(v.numerator,v.denominator) for k,v in env.items()}
        rawR=sp.expand(symbolicR.subs(substitutions))
        literal=sp.Poly(rawR,*coords).as_dict()
        for e,node in zip(piv,packet['R_pivot']):assert literal.get(e,0)==values[node]
        for e,node in zip(free,packet['R_free']):assert literal.get(e,0)==values[node]
        quotient=sum(sp.Rational(values[v].numerator,values[v].denominator)*mon(e)
                     for v,e in zip(packet['quartic_quotient_nodes'],mult))
        actual_remainder=sp.Poly(sp.expand(rawR-Q2.subs(substitutions)*quotient),*coords).as_dict()
        assert all(actual_remainder.get(e,0)==0 for e in piv)
        for e,node in zip(free,packet['norm_equation_nodes']):
            assert actual_remainder.get(e,0)==values[node]
        binding=packet['point_binding']
        assert values[binding['left_G_at_point_node']]==values[binding['right_equation_combination_node']]
        for name in ('f1_weighted','g1_weighted'):
            assert all(sum(term['exponent'][:4])+2*term['exponent'][4] ==
                       (2 if name=='f1_weighted' else 4) for term in packet['polynomials'][name])
        numeric.append({'trial':trial,'ell':str(values[packet['ell_node']]),
                        'Delta':str(values[packet['localization_Delta_node']]),
                        'remainder_identity':True,'point_binding_identity':True,
                        'norm_equations_all_zero':all(values[i]==0 for i in packet['norm_equation_nodes'])})
    return {'protected_F_reflection_pencil_binding':True,'protected_A_binding':True,
        'arithmetic_DAG_weighted_target_symbolically_bound':True,
        'general_cubic_current_raw_chart_binding':True,'all_nine_monic_coefficients_bound':True,
        'universal_u_division_g1_identity_checked':True,
        'emitted_g1_polynomial_symbolically_bound':True,
        'all_remainder_DAG_coefficients_symbolically_bound':True,
        'all_reduction_matrix_DAG_entries_symbolically_bound':True,
        'G_raw_leading_coefficient':str(sp.factor(ell)),
        'symbolic_cubic_reduction_determinant':str(1-mu[0]*mu[1]),
        'symbolic_sextic_reduction_determinant':str(delta),
        'determinant_proof':'Verified block lower triangular structure; exact 5x5, three 3x3, and five 1x1 determinants.',
        'universal_quartic_multiplication_coefficient_map_checked':True,
        'exact_rational_remainder_replays':numeric,
        'point_binding_proof':'Universal coefficient decomposition R=Q2*v+remainder, M*v=R_pivot, and A^2-B^2=(A+B)(A-B).',
        'norm_parameters':26,'norm_equations':25,'moving_unknowns':27,'moving_equations':27,
        'scope':'All replay assignments are arbitrary arithmetic controls, not contact solutions. No incidence existence, dominance, finiteness, etaleness, source trace, or certificate asserted.'}


def main():
    inputs_path=HERE/'symmetric_norm_contact_inputs.json'
    inputs=json.loads(inputs_path.read_text())
    packet=build_circuit(inputs)
    print(f"Built {len(packet['nodes'])} arithmetic nodes and one 19x19 solve gate.",flush=True)
    receipt=audit(packet)
    output=HERE/'symmetric_norm_contact_circuit.json'
    output.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    receipt.update(circuit_file=output.name,circuit_bytes=output.stat().st_size,
                   arithmetic_nodes=len(packet['nodes']),
                   circuit_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
                   inputs_sha256=hashlib.sha256(inputs_path.read_bytes()).hexdigest())
    (HERE/'symmetric_norm_contact_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)


if __name__=='__main__':main()
