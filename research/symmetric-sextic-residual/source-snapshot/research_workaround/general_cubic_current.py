#!/usr/bin/env python3
"""Exact algebraic check of a general-cubic moving-point current.

This does not claim a primitive for symmetric-sextic-residual.  It checks a
general-cubic source formula needed before a norm-contact trace could be used.
The moving point and closed one-form remain explicit inputs, not existence
assertions.  All computations are over characteristic zero.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "python_deps"))
import sympy as sp

w, x, alpha, beta, Y, Z = sp.symbols("w x alpha beta Y Z")
indices = [(i, j) for i in range(3) for j in range(4-i)]
p = {(i,j): sp.Symbol(f"p{i}{j}") for i,j in indices}
R = {(i,j): sp.Symbol(f"R{i}{j}") for i,j in indices}
A = alpha**2
G = w**3 + sum(p[i,j]*w**i*x**j for i,j in indices)
RG = sum(R[i,j]*w**i*x**j for i,j in indices)
g = sp.diff(G,w)
a = sum(p[2,j]*x**j for j in range(2))
b = sum(p[1,j]*x**j for j in range(3))
aa, bb = a.subs(x,A), b.subs(x,A)
H = w**2 + (beta+aa)*w + beta**2+aa*beta+bb
assert sp.expand((w-beta)*H - (G.subs(x,A)-G.subs({x:A,w:beta}))) == 0

# z=-t Z D_t + alpha V D_r - alpha U D_s, with x=t^2.
# Y=U beta_s-V beta_r, Z=U alpha_s-V alpha_r,
# R_ij=U (p_ij)_s-V (p_ij)_r.  The subscript 0 freezes w.
zG0 = -2*x*Z*sp.diff(G,x)-alpha*RG
zg0 = sp.diff(zG0,w)
ra = sum(R[2,j]*A**j for j in range(2))
rb = sum(R[1,j]*A**j for j in range(3))
zH0 = -alpha*((w+2*beta+aa)*Y
    +(w+beta)*(ra+2*alpha*Z*sp.diff(a,x).subs(x,A))
    +(rb+2*alpha*Z*sp.diff(b,x).subs(x,A)))
N = sp.expand(g**2*zH0-g*H*zg0-(g*sp.diff(H,w)-H*sp.diff(g,w))*zG0)

print("Reducing the source numerator modulo the monic cubic.",flush=True)
Nbar = sp.Poly(N,w).rem(sp.Poly(G,w)).as_expr()
print("Dividing out the apparent moving-point denominator.",flush=True)
quotient, remainder = sp.div(Nbar,x-A,x)
point_sub = {p[0,0]: -sp.expand(G.subs({x:A,w:beta})-p[0,0])}
motion = (sp.diff(G,w).subs({x:A,w:beta})*Y
          +2*alpha*sp.diff(G,x).subs({x:A,w:beta})*Z
          +RG.subs({x:A,w:beta}))
motion_sub = {R[0,0]: -sp.expand(motion-R[0,0])}
checked_remainder = sp.expand(remainder.subs(motion_sub).subs(point_sub))
assert checked_remainder == 0
M = sp.expand(quotient.subs(motion_sub).subs(point_sub))

# A reduced second-pole normal source has the form g d_w L-G_ww L.
# On quadratic L its image has the following nontrivial cokernel relation.
Mcoeff = [sp.expand(M.coeff(w,i)) for i in range(3)]
cokernel = sp.factor(3*Mcoeff[0]-a*Mcoeff[1]+b*Mcoeff[2])
assert cokernel == 0
normal_source = -Mcoeff[1]/3-2*Mcoeff[2]*w/3
assert sp.expand(g*sp.diff(normal_source,w)-sp.diff(g,w)*normal_source-2*M) == 0

# The actual two-reflection quotient, on a=1,b=r,c=t,d=s*t.
r,s,lam = sp.symbols("r s lam")
kappa = sp.Rational(5,7)
Q = 1+2*r-w
P = (1+2*s)*x-lam**2*w
exact_G = sp.expand(r**6 + s**6*x**3 + 2+30*w+30*w**2+2*w**3
    +2*x**3+30*lam**2*x**2*w+30*lam**4*x*w**2+2*lam**6*w**3
    +kappa*Q**2*P+2*kappa*Q*P**2)
lead = exact_G.coeff(w,3)
assert not lead.has(r,s,x,w)
exact_coeffs = {f"p{i}{j}": str(sp.factor(exact_G.coeff(w,i).coeff(x,j)/lead))
                for i,j in indices}
assert sp.cancel(exact_G-lead*(w**3+sum(
    sp.sympify(exact_coeffs[f"p{i}{j}"])*w**i*x**j for i,j in indices))) == 0

# The exact Jacobian of the two reflections and the pencil, including signs.
scale,b0,c0,d0,u,z = sp.symbols("scale b0 c0 d0 u z")
physical = [scale+u,scale-u,b0,c0+lam*u,c0-lam*u,d0]
reflection_vars = [scale,b0,c0,d0,u,lam]
reflection_jacobian = sp.det(sp.Matrix([
    [sp.diff(f,v) for v in reflection_vars] for f in physical]))
assert sp.expand(reflection_jacobian-4*u) == 0
weighted_chart = [scale,scale*r,scale*z,scale*z*s,scale**2*w]
weighted_vars = [scale,r,z,s,w]
weighted_jacobian = sp.det(sp.Matrix([
    [sp.diff(f,v) for v in weighted_vars] for f in weighted_chart]))
assert sp.expand(weighted_jacobian-scale**5*z) == 0

exact_a = sp.cancel(exact_G.coeff(w,2)/lead)
exact_b = sp.cancel(exact_G.coeff(w,1)/lead)
exact_monic = sp.cancel(exact_G/lead)
exact_g = sp.diff(exact_monic,w)
target_C = 2*r*s*x/lead**2
target_protected = target_C*(1-w)*(x-lam**2*w)
target_R0 = target_C*(x-lam**2*exact_b/3)
target_R1 = -target_C*(x+lam**2+2*lam**2*exact_a/3)
assert sp.cancel(target_protected-target_C*lam**2*exact_g/3
                 -target_R0-target_R1*w) == 0
assert sp.cancel(exact_g*sp.diff(target_protected,w)-sp.diff(exact_g,w)*target_protected
    -(exact_g*target_R1-sp.diff(exact_g,w)*(target_R0+target_R1*w))) == 0

target_pair = {
    "abbreviation":"x=z^2; the differential volume remains dz wedge dr wedge ds wedge d(lambda)",
    "C":"2*r*s*x/ell^2",
    "protected_R":"C*(1-w)*(x-lambda^2*w)",
    "linear_R0":"C*(x-lambda^2*b(x)/3)",
    "linear_R1":"-C*(x+lambda^2+2*lambda^2*a(x)/3)",
    "required_normalized_trace_M1":"-C*(3*x-lambda^2*b(x))",
    "required_normalized_trace_M2":"C/2*(3*x+3*lambda^2+2*lambda^2*a(x))",
    "residue_orientation":"dz wedge dr wedge ds wedge d(lambda)",
    "cone_Jacobian":"2*scale^5*z",
    "normal_source_gauge_checked":True
}
(HERE/"general_cubic_target_pair.json").write_text(json.dumps(target_pair,indent=2)+"\n")

receipt = {
    "field":"Q with algebraically independent coefficients",
    "cubic_form":"w^3 + p21*x*w^2+p20*w^2+p12*x^2*w+p11*x*w+p10*w+p03*x^3+p02*x^2+p01*x+p00",
    "kernel":"H/G_w * (dlog(t-alpha)-dlog(t+alpha))",
    "source":"2*M/G_w^3 dt wedge dr wedge ds",
    "moving_point_pole_cancels": True,
    "source_w_degree":sp.degree(M,w),
    "source_x_degree":sp.degree(M,x),
    "M1_x_degree":sp.degree(Mcoeff[1],x),
    "M2_x_degree":sp.degree(Mcoeff[2],x),
    "source_terms":len(sp.Add.make_args(M)),
    "quadratic_normal_source_cokernel":str(cokernel),
    "linear_normal_source_identity_checked":True,
    "exact_target_Jacobian_and_gauge_checked":True,
    "exact_symmetric_cubic_leading_coefficient":str(sp.factor(lead)),
    "exact_symmetric_monic_coefficients":exact_coeffs,
    "scope":"General-cubic algebraic current only. No norm-contact existence, closed-form construction, final trace/source inverse, or certificate is asserted."
}
(HERE/"general_cubic_current_receipt.json").write_text(json.dumps(receipt,indent=2,default=str)+"\n")
(HERE/"general_cubic_current_source.txt").write_text(str(M)+"\n")
print(json.dumps(receipt,indent=2,default=str),flush=True)
