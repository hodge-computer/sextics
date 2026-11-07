# A general-cubic current and the exact symmetric target

## Scope

This repairs the cyclic-cover restriction of the moving-point current in the
PR219 discussion packet. It is a literal algebraic differential identity for
a general cubic in the weight-two coordinate. It does **not** construct a
norm-contact family on the exact symmetric sextic, evaluate its trace, or prove
`HasCertificate`. The remaining exact source equations are given below.

`GeneralCubicCurrent.lean` checks the polynomial reduction, its automatic
cokernel relation, the moving-point cancellation, the normal-source conversion,
and the target gauge reduction. `general_cubic_current.py` independently checks
the complete characteristic-zero symbolic calculation and the coordinate
Jacobian. No Hodge-theoretic identification is used in these calculations.

## 1. The general cubic and its selected-point current

Work over a characteristic-zero field with parameters `r,s`. Write

\[
G(t,w)=w^3+a(x)w^2+b(x)w+c(x),\qquad x=t^2,
\]

where `deg a <= 1`, `deg b <= 2`, and `deg c <= 3`. Put
`g = G_w = 3w²+2aw+b`. Let `(alpha,beta)` be a moving point in a finite
separable coefficient extension, satisfying `G(alpha,beta)=0`. Set

\[
q=\alpha^2,\quad d=\beta+a(q),\quad
e=\beta^2+a(q)\beta+b(q),\quad H=w^2+dw+e.
\]

Thus `(w-beta)H=G(alpha,w)-G(alpha,beta)`. The current is

\[
\Theta={H\over g}
\left(d\log(t-\alpha)-d\log(t+\alpha)\right)
={2H\over (x-q)g}(\alpha\,dt-t\,d\alpha).
\]

It selects the points `(alpha,beta)` and `(-alpha,beta)`: at the selected roots
`H/g=1`, whereas it is zero at the other roots above `t=+/-alpha`. In a cyclic
cubic the packet's `beta²/w²` current is a deck-character component of this
general selected-point kernel, rather than a formula valid unchanged for a
general cubic.

Let `eta=U dr+V ds` be closed and define

\[
Z=U\alpha_s-V\alpha_r,\qquad Y=U\beta_s-V\beta_r,
\qquad R_f=U f_s-V f_r.
\]

The coefficient derivatives below hold `w` fixed:

\[
\begin{aligned}
\dot a&=-2xZ a_x-\alpha R_a(x),&
\dot b&=-2xZ b_x-\alpha R_b(x),&
\dot c&=-2xZ c_x-\alpha R_c(x),\\
\dot d&=-\alpha\{Y+R_a(q)+2\alpha Z a_x(q)\},\\
\dot e&=-\alpha\{(2\beta+a(q))Y+
\beta[R_a(q)+2\alpha Z a_x(q)]+R_b(q)+2\alpha Zb_x(q)\}.
\end{aligned}
\]

The vector `zeta=(-tZ,alpha V,-alpha U)` satisfies
`div(zeta/(x-q))=0`, because `eta` is closed. Hence

\[
\eta\wedge\Theta={\iota_{2H\zeta/(x-q)}
  (dt\wedge dr\wedge ds)\over g},\qquad
d(\eta\wedge\Theta)={2N\over(x-q)g^3}
 dt\wedge dr\wedge ds
\]

on `G=0`, where

\[
N=g^2(\dot d\,w+\dot e)-gH(2\dot a\,w+\dot b)
 -(g(2w+d)-H(6w+2a))(\dot a\,w^2+\dot b\,w+\dot c).
\]

## 2. A small exact source formula

Reduce `N` by the monic cubic:
`N = G Q + N0 + N1 w + N2 w²`. The two needed coefficients are

\[
\begin{aligned}
N_1={}&\dot a(abd-2b^2-2be+3cd)
 +\dot b(ab-2bd+3c)+\dot c(-2b+6e)\\
 &+\dot d(-a^2b-3ac+4b^2)+\dot e(ab-9c),\\[2mm]
N_2={}&\dot a(a^2d-2ab-2ae+6c)
 +\dot b(a^2-2ad+3e)+\dot c(-2a+3d)\\
 &+\dot d(-a^3+4ab-9c)+\dot e(a^2-3b).
\end{aligned}
\]

The reduced coefficients always satisfy

\[
3N_0-aN_1+bN_2=0.
\]

This is an identity for arbitrary `a,b,c,d,e` and their dotted values, before
using the moving-point equations. It is proved by `source_cokernel` in Lean.

At `x=q`, put `v=-alpha Y`. The moving-point equation and its derivative give

\[
\begin{aligned}
c&=-\beta^3-a\beta^2-b\beta, &d&=\beta+a,&e&=\beta^2+a\beta+b,\\
\dot c&=-\dot a\beta^2-\dot b\beta-g(\beta)v,&
\dot d&=\dot a+v,&
\dot e&=\beta\dot a+\dot b+(2\beta+a)v.
\end{aligned}
\]

Substitution makes each `Ni` zero, as checked by the Lean theorem
`moving_point_remainder`. Consequently

\[
M_i=N_i/(x-q)\in L[x],\qquad
3M_0-aM_1+bM_2=0,
\]

and the apparent moving-point pole has canceled. The degree bounds are
`deg M1 <= 4` and `deg M2 <= 3`. Define

\[
R_*=-M_1/3-(2M_2/3)w.
\]

Then there is the exact identity

\[
\boxed{g\,\partial_w R_*-G_{ww}R_*
       =2(M_0+M_1w+M_2w^2)},
\]

so the current gives a literal second-pole normal source with no introduced
cubic-discriminant denominator. This is `linear_normal_source` in Lean.
Normalized coefficient trace commutes with this identity. The trace source
is therefore obtained by replacing each `Mi` by `Tr(Mi)/[L:K]`.

## 3. The exact two-reflection coordinate map

Use the original ordered variables `(X0,X1,X2,Y0,Y1,Y2)` and set

\[
X=(a+u,a-u,ar),\qquad
Y=(az+\lambda u,az-\lambda u,asz),\qquad
w=u^2/a^2,\quad x=z^2.
\]

**Here `x` is an abbreviation for `z²`; the differential variable remains
`z`. No change `dz -> dx` is being made.**

The reflection/pencil determinant in coordinates `(a,b,c,d,u,lambda)` is
`+4u`. Replacing `u²` by the physical weight-two coordinate gives determinant
`+2`. The weighted affine chart then gives

\[
dX_0\wedge dX_1\wedge dX_2\wedge dY_0\wedge dY_1\wedge dY_2
=2a^5z\,da\wedge dr\wedge dz\wedge ds\wedge dw\wedge d\lambda.
\]

For the Euler form `Omega=i_E(volume)`, putting `w` first and using residue
orientation `dz wedge dr wedge ds wedge d(lambda)` therefore gives protected
numerator `+2z A_hat`, not a missing-Jacobian version of `A_hat`.

Let

\[
Q=1+2r-w,\qquad P=(1+2s)x-\lambda^2w.
\]

The exact unnormalized quotient is

\[
\begin{aligned}
G_{\rm orig}={}&r^6+s^6x^3+2+30w+30w^2+2w^3\\
&+2x^3+30\lambda^2x^2w+30\lambda^4xw^2+2\lambda^6w^3
+\tfrac57Q^2P+\tfrac{10}7QP^2.
\end{aligned}
\]

Its leading cubic coefficient is

\[
\ell=(14\lambda^6-10\lambda^4-5\lambda^2+14)/7.
\]

Put `G=G_orig/ell`, and use its coefficient polynomials `a(x),b(x),c(x)` in
the preceding construction. Their exact coefficients are recorded in
`general_cubic_current_receipt.json`. The original numerator becomes

\[
\widehat A=rsz(1-w)(x-\lambda^2w).
\]

After normalization of `G`, the protected target is consequently

\[
\boxed{R_{*,\rm target}=C(1-w)(x-\lambda^2w),\qquad
C=2rsx/\ell^2.}
\]

This sign uses precisely the residue orientation stated above. The normalized
residue-equation vector in the existing Lean clearing theorem has the opposite
sign to a primitive whose exterior derivative equals this residue; negate the
current flux when using that convention.

## 4. The remaining exact trace equations

Adding a multiple of `g=G_w` independent of `w` does not change the normal
source. Subtracting `(C lambda²/3)g` reduces the target to

\[
R_{0,\rm target}=C(x-\lambda^2b/3),\qquad
R_{1,\rm target}=-C(x+\lambda^2+2\lambda^2a/3).
\]

The Lean theorem `target_quadratic_reduction` proves this identity after
clearing the integer denominator. Write `<f>=Tr(f)/[L:K]`. An actual trace of
closed forms which satisfies the two polynomial identities

\[
\boxed{
\begin{aligned}
\langle M_1\rangle&=-C(3x-\lambda^2b(x)),\\
\langle M_2\rangle&=\tfrac C2(3x+3\lambda^2+2\lambda^2a(x))
\end{aligned}}
\]

would give the required normal residue primitive on the generic pencil. Wedge
the current with `d(lambda)`; additional lambda derivatives then vanish.
The existing finite-residue clearing machinery can handle descent and legal
homogeneous clearing once the genuine primitive is supplied.

The source is automatically polynomial in `x,w`: the pair has at most nine
coefficients over `K=C(r,s,lambda)`. Its coefficients need not be polynomials
in `r,s`, and the calculation does **not** make the operator a constant
matrix. A parameter-dependent linear combination of closed forms may cease to
be closed. No global trace evaluation or source-matching solution is currently
present in these files or in the PR219 packet.

## 5. Substitution into the literal norm-contact finite algebra

The source formula can use the packet's intrinsic incidence without requiring
a cyclic equation. Let its 25 norm equations define a parameter curve, and
write `tau` for a local parameter. After substituting the moving point, put

\[
q=Q_2(1,r,\alpha,s\alpha),\quad
h=(A+B)(1,r,\alpha,s\alpha),\quad
\beta=-Q_1(1,r,\alpha,s\alpha).
\]

In the following formulas, subscripts `r,s,alpha` hold the parameter curve's
coordinates fixed. If `v2=D(Q2)` and `v3=D(h)`, define

\[
\begin{aligned}
j&=v_2h_\alpha-v_3q_\alpha,\\
E_r&=q_\alpha h_r-h_\alpha q_r,&
E_s&=q_\alpha h_s-h_\alpha q_s,\\
E_Z&=q_rh_s-q_sh_r,&
E_Y&=E_r\beta_s-E_s\beta_r+\beta_\alpha E_Z.
\end{aligned}
\]

For an algebraic one-form `eta=ell(tau) d(tau)` on the parameter curve,
implicit differentiation gives exactly

\[
U={\ell\over j}E_r,\quad V={\ell\over j}E_s,\quad
Z={\ell\over j}E_Z,\quad Y={\ell\over j}E_Y,
\qquad R_f={\ell\over j}(E_rf_s-E_sf_r).
\]

Every dotted expression, every `Ni`, and every `Mi` above is linear in these
inputs. Thus one may compute polynomials `M1_tilde,M2_tilde` simply by using
`U=Er,V=Es,Z=EZ,Y=EY` and then multiplying the result by `ell/j`:

\[
M_i=(\ell/j)\widetilde M_i.
\]

This is a direct general-cubic replacement for the cyclic three-coefficient
trace in the public packet. The canonical choice
`ell_R=tau_(f1,f2,h,g1,g2)(R D(h))` is algebraic when the displayed regular
sequence and its residue normalization are verified; closedness follows from
being a one-form on a curve. Establishing or evaluating that choice on the
exact symmetric incidence has not been done here.

The resulting computation is finite in principle: use the 25 norm equations
plus `q=h=0`, saturate by the chart and regularity denominators, establish that
the relevant algebra over `C(r,s,lambda)` is nonzero and finite separable, and
evaluate the two traces of `(ell/j) Mi_tilde`. The two identities in Section 4
are literal identities which must be checked. A nonzero finite-jet spanning
minor on another threefold does not supply these traces or their inverse.
