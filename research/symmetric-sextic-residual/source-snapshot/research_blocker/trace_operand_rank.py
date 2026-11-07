#!/usr/bin/env python3
"""Rank of universal moving-point source coefficients for the exact sextic.

This computes identities before imposing the contact family. It does not
evaluate a finite-incidence trace. A nonzero exact minor rules out additional
coefficient-only linear dependencies that follow from the universal point
and motion equations alone.
"""
from pathlib import Path
import hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
try:
    import sympy as sp
except ModuleNotFoundError:
    for candidate in (HERE.parent/'research_workaround/python_deps',
                      HERE.parent/'proof_attempt3/python_deps'):
        if candidate.exists(): sys.path.insert(0, str(candidate))
    import sympy as sp


def main():
    start = time.monotonic()
    x, w, r, s, lam = sp.symbols('x w r s lam')
    alpha, beta, U, V, Z, Y = sp.symbols('alpha beta U V Z Y')
    Q, P = 1+2*r-w, (1+2*s)*x-lam**2*w
    raw = sp.expand(r**6+s**6*x**3+2+30*w+30*w**2+2*w**3
                    +2*x**3+30*lam**2*x**2*w+30*lam**4*x*w**2
                    +2*lam**6*w**3+sp.Rational(5,7)*Q**2*P
                    +sp.Rational(10,7)*Q*P**2)
    ell = raw.coeff(w,3)
    exact = sp.Poly(raw,w).monic().as_expr()
    spec = {lam:1,r:1,s:1}
    ff = [sp.expand(exact.coeff(w,i)) for i in (2,1,0)]
    rr = [sp.expand((U*sp.diff(f,s)-V*sp.diff(f,r)).subs(spec)) for f in ff]
    aa,bb,cc = [sp.expand(f.subs(spec)) for f in ff]
    ra,rb,rc = rr
    da,db,dc = [-2*x*Z*sp.diff(f,x)-alpha*rf for f,rf in zip((aa,bb,cc),rr)]
    t = alpha**2
    aq,bq = aa.subs(x,t),bb.subs(x,t)
    dq,eq = beta+aq,beta**2+aq*beta+bq
    am = ra.subs(x,t)+2*alpha*Z*sp.diff(aa,x).subs(x,t)
    bm = rb.subs(x,t)+2*alpha*Z*sp.diff(bb,x).subs(x,t)
    dd = -alpha*(Y+am)
    de = -alpha*((2*beta+aq)*Y+beta*am+bm)
    N1 = (da*(aa*bb*dq-2*bb**2-2*bb*eq+3*cc*dq)
          +db*(aa*bb-2*bb*dq+3*cc)+dc*(-2*bb+6*eq)
          +dd*(-aa**2*bb-3*aa*cc+4*bb**2)+de*(aa*bb-9*cc))
    N2 = (da*(aa**2*dq-2*aa*bb-2*aa*eq+6*cc)
          +db*(aa**2-2*aa*dq+3*eq)+dc*(-2*aa+3*dq)
          +dd*(-aa**3+4*aa*bb-9*cc)+de*(aa**2-3*bb))
    P1,rem1 = sp.div(sp.expand(N1),x-t,x)
    P2,rem2 = sp.div(sp.expand(N2),x-t,x)
    gp = beta**3+aq*beta**2+bq*beta+cc.subs(x,t)
    gw = sp.diff(gp,beta)
    discriminant_at_alpha_one = sp.factor(sp.discriminant(gp.subs(alpha,1),beta))
    assert discriminant_at_alpha_one != 0
    ym = -(2*alpha*Z*(sp.diff(aa,x).subs(x,t)*beta**2
           +sp.diff(bb,x).subs(x,t)*beta+sp.diff(cc,x).subs(x,t))
           +ra.subs(x,t)*beta**2+rb.subs(x,t)*beta+rc.subs(x,t))

    def clear_reduce(e):
        p = sp.Poly(sp.expand(e),Y)
        assert p.degree() <= 1
        cleared = sp.expand(p.coeff_monomial(1)*gw+p.coeff_monomial(Y)*ym)
        return sp.Poly(cleared,beta).rem(sp.Poly(gp,beta)).as_expr().expand()

    assert clear_reduce(rem1)==0 and clear_reduce(rem2)==0
    rows = [clear_reduce(sp.expand(P1).coeff(x,i)) for i in range(5)]
    rows += [clear_reduce(sp.expand(P2).coeff(x,i)) for i in range(4)]
    variables = (alpha,beta,U,V,Z)
    polys = [sp.Poly(e,*variables,domain=sp.QQ) for e in rows]
    mons = sorted(set().union(*(set(p.monoms()) for p in polys)))
    M = sp.Matrix([[p.coeff_monomial(e) for e in mons] for p in polys])
    _,pivot_rows = M.T.rref()
    _,pivot_cols = M[list(pivot_rows),:].rref()
    sub = M[list(pivot_rows),list(pivot_cols)]
    determinant = sub.det()
    rank = len(pivot_rows)
    null = M.T.nullspace()
    expected = sp.zeros(9,1)
    expected[4] = sp.Rational(13396320,2197)
    expected[8] = -sp.Rational(5773320,2197)
    assert M.T*expected == sp.zeros(len(mons),1)
    assert rank==8 and len(null)==1 and determinant!=0
    # Both prescribed target entries in the unique relation vanish.
    cf = (2*r*s/ell**2).subs(spec)
    targets = [sp.expand(cf*x*(bb-3*x)).coeff(x,i) for i in range(5)]
    targets += [sp.expand(cf*x*(3*x+3+2*aa)/2).coeff(x,i) for i in range(4)]
    assert (sp.Matrix(targets).T*expected)[0]==0
    receipt = {
        'status':'PASS','coefficient_field':'Q','base_specialization':{'lambda':1,'r':1,'s':1},
        'clearing_denominator':'G_w(alpha^2,beta)',
        'point_cubic_discriminant_at_alpha_one':str(discriminant_at_alpha_one),
        'point_cubic_squarefree_over_Q_alpha':True,
        'reduction_equations':['G(alpha^2,beta)=0','G_w Y+2 alpha G_x Z+U G_s-V G_r=0'],
        'motion_remainders_zero':True,'source_rows':9,'monomial_columns':len(mons),
        'exact_rank':rank,'independent_row_indices':list(pivot_rows),
        'nonzero_minor_column_monomials':[list(mons[i]) for i in pivot_cols],
        'nonzero_minor':str(determinant),
        'unique_relation_vector':[str(v) for v in null[0]],
        'target_obeys_unique_relation':True,
        'generic_conclusion':'The nine universal source coefficients have exactly one coefficient-field linear relation over Q(lambda,r,s); the known highest-coefficient relation supplies the upper bound and this exact nonzero specialized minor supplies the lower bound.',
        'scope':'This rules out further linear dependencies derived solely from the generic point and motion equations. Contact-family-specific trace cancellations remain possible and are not tested here.',
        'full_trace_evaluated':False,'full_certificate_proved':False,
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds':time.monotonic()-start}
    (HERE/'trace_operand_rank.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__': main()
