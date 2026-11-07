#!/usr/bin/env python3
"""Exact computation of the dependence between the two highest trace targets.

This proves that both highest source coefficients are scalar multiples of
the single trace moment <alpha U>. It does NOT assert that this moment is
zero. The displayed scalar multiples are the exact protected target's.
"""
from pathlib import Path
import json, sys
HERE=Path(__file__).resolve().parent
try:
    import sympy as sp
except ModuleNotFoundError:
    for parent in ('research_workaround','proof_attempt3'):
        dependency_dir=HERE.parent/parent/'python_deps'
        if dependency_dir.exists():sys.path.insert(0,str(dependency_dir))
    import sympy as sp

def main():
    A,B,C,Ar,Br,Cr,Z,alpha=sp.symbols('A B C Ar Br Cr Z alpha')
    da=-2*Z*A-alpha*Ar
    db=-4*Z*B-alpha*Br
    dc=-6*Z*C-alpha*Cr
    # Highest coefficients of the already verified general-cubic source.
    n15=-2*B**2*da+(A*B+3*C)*db-2*B*dc
    n24=(-2*A*B+6*C)*da+A**2*db-2*A*dc
    q1=2*B**2*Ar-(A*B+3*C)*Br+2*B*Cr
    q2=(2*A*B-6*C)*Ar-A**2*Br+2*A*Cr
    assert sp.expand(n15-alpha*q1)==0
    assert sp.expand(n24-alpha*q2)==0
    s,lam=sp.symbols('s lam')
    den=14*lam**6-10*lam**4-5*lam**2+14
    aa=5*(42*lam**4+8*lam**2*s+4*lam**2+2*s+1)/den
    bb=-10*(-21*lam**2+4*s**2+4*s+1)/den
    cc=7*(s**6+2)/den
    substitution={A:aa,B:bb,C:cc,Ar:sp.diff(aa,s),Br:sp.diff(bb,s),Cr:sp.diff(cc,s)}
    c1=sp.factor(q1.subs(substitution));c2=sp.factor(q2.subs(substitution))
    value1=sp.factor(c1.subs({lam:1,s:1}));value2=sp.factor(c2.subs({lam:1,s:1}))
    assert value1==sp.Rational(5773320,2197)
    assert value2==sp.Rational(13396320,2197)
    # Exact resultant eliminating the inner selected point alpha.
    Q0,Qc,E0,E2,O1,O3,t=sp.symbols('Q0 Qc E0 E2 O1 O3 t')
    E=E0*Qc-E2*Q0;O=O1*Qc-O3*Q0
    D=Qc*E**2+Q0*O**2
    assert sp.expand(sp.resultant(Q0+Qc*t*t,E0+E2*t*t+O1*t+O3*t**3,t)-D)==0
    Er,Or,Q0r=sp.symbols('Er Or Q0r')
    Dr=2*Qc*E*Er+Q0r*O**2+2*Q0*O*Or
    numerator=O*(E*Q0r-2*Q0*Er)+2*Q0*E*Or
    assert sp.expand(E*Dr-2*Er*D-O*numerator)==0
    receipt={
      'status':'PASS',
      'generic_highest_coefficient_identities':True,
      'exact_target_leading_coefficients':{'a1':str(aa),'b2':str(bb),'c3':str(cc)},
      'multipliers':{'C1':str(c1),'C2':str(c2)},
      'lambda_s_equal_one':{'C1':str(value1),'C2':str(value2)},
      'computed_trace_relation':'C2 * <[x^4]M1> - C1 * <[x^3]M2> = 0',
      'minimal_remaining_moment':'m=<alpha U>; <[x^4]M1>=C1*m, <[x^3]M2>=C2*m',
      'moment_value_computed':False,
      'inner_point_resultant':'Res_alpha(Q0+Qc*alpha^2,E0+E2*alpha^2+O1*alpha+O3*alpha^3)=Qc*(E0*Qc-E2*Q0)^2+Q0*(O1*Qc-O3*Q0)^2',
      'point_on_resultant_open':'alpha=-(E0*Qc-E2*Q0)/(O1*Qc-O3*Q0)',
      'curve_residue_numerator':'O*(E*Q0_r-2*Q0*E_r)+2*Q0*E*O_r',
      'curve_residue_identity':'(E/O)*(D_r/D)-2*E_r/O = curve_residue_numerator/D',
      'scope':'One exact relation between the requested traces; not their individual evaluation. Euler-Jacobi zero would require additional boundary control.'}
    (HERE/'trace_top_moment.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
