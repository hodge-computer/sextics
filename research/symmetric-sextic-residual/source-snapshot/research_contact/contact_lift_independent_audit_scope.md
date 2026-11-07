# Independent audit of the exact contact incidence

## What was checked

`contact_lift_independent_audit.py` reconstructs the target from the six
original coordinates

\[
X=(a+v,a-v,b),\qquad Y=(c+v,c-v,d)
\]

and the original coefficients `5/7` and `10/7`. It does not import the circuit,
homotopy arithmetic, or certificate generator. Replacing `v²` by `u` gives
leading coefficient `13/7`; the checker then normalizes the cubic.

It constructs the coefficient equations by substituting `u=-Q1` and comparing

\[
G(a,b,c,d,-Q_1)=A^2-B^2+Q_2g_2.
\]

The 44 invariant sextic coefficients are followed by the two moving-point
equations

\[
Q_2(1,r,\alpha,\alpha)=0,\qquad
(A+B)(1,r,\alpha,\alpha)=0.
\]

Thus the check binds the rational witness to the actual symmetric sextic at
`lambda=1`, rather than merely to the numerical continuation's coefficient
array. The independent coefficient polynomials are saved in
`contact_lift_independent_equations.json`.

The witness has 47 ambient coordinates. For existence, `rho0=1/4` is fixed and
the 46 active coordinates are indices `1,...,46`. For moving-incidence
regularity, `r` is held fixed and the columns are `0,...,44,46`.

## Exact rational outcome

The independent checker reproduces:

| Quantity | Certified upper bound |
|---|---:|
| Radius | `10^-35` |
| `||B F(x0)||` | `10^-72` |
| `||I-B J(x0)||` | `10^-68` |
| Incidence inverse defect at center | `10^-68` |
| Coordinate bound on ball | `100` |
| Hessian bound | `1201804` |
| Contraction constant on ball | `10^-25` |
| Incidence inverse defect on ball | `10^-26` |

The self-mapping inequality is strict. The factors
`1-mu0*mu1`, `1-2*mu0*mu1`, and `1-3*mu0*mu1` remain nonzero, so both the cubic
and sextic remainder charts remain valid. `alpha` also remains nonzero.

All acceptance decisions use exact `Fraction` arithmetic. Numerical singular
values are supplementary: approximately `0.0022515` and `0.0047478` for the
existence and moving-incidence matrices respectively.

## Why the bounds prove existence

Use the real norm `|Re z|+|Im z|` on each complex coordinate and the maximum
of these norms on vectors. This is a complete real normed space; multiplication
is submultiplicative in the scalar norm. Hence a complex matrix's row sum of
scalar norms bounds its operator norm, with no missing factor of two.

For each polynomial equation, the sum of the absolute values of all ordered
second partials on the ball is bounded by

\[
\sum_m |c_m|\,d_m(d_m-1)M^{d_m-2},
\]

with zero contribution from degrees zero and one. Taking the maximum over rows
gives the recorded Hessian bound `H`. Along a line segment this bounds
`||J(x)-J(x0)||` by `H*||x-x0||`.

For `T(x)=x-B F(x)`, put

\[
\eta=\|BF(x_0)\|,\quad z=\|I-BJ(x_0)\|,\quad
q=z+\|B\|Hr.
\]

The checker verifies `q<1` and `eta+q*r<r`. Thus `T` is a contraction mapping
the closed ball into itself. Its unique fixed point is a zero of `F`: since
`z<1`, the square matrix `BJ(x0)` is invertible, so `B` is invertible. The
separate incidence bound proves that the moving-incidence Jacobian is
invertible at this exact zero, and indeed throughout the same ball.

This is a classical Banach fixed-point proof backed by exact rational
inequalities. It has not been formalized in Lean.

## Algebraic consequence and limits

The equations and the fixed value `rho0=1/4` are rational. The nonsingular
isolated root therefore has algebraic coordinates, lying in a finite
extension of the rationals.

For the moving incidence, allow `lambda,r,s` to be external variables, with
`d=s*alpha`. There are 46 equations and 46 remaining unknowns: the 45 contact
coefficients plus `alpha`. The certified nonzero incidence minor at
`(lambda,s)=(1,1)` supplies a locally étale algebraic branch over the three
external variables. Consequently an incidence component dominates
`(lambda,r,s)` and is generically finite; after choosing that component, its
function field is a finite extension of `Q(lambda,r,s)`.

This removes the previously missing existence/dominance premise for an actual
finite moving-point algebra on the symmetric pencil. It does not compute its
normalized trace, construct the canonical residue form, show that a chosen
curve correspondence spans the target source, or prove `HasCertificate`.
Global smoothness of the norm-contact curve is also not asserted by this
local Jacobian check.

## Reproduction

Place the independent checker beside `contact_exact_ball.json` and run:

```bash
python contact_lift_independent_audit.py
```

Only Python 3 and NumPy are required. The input is the explicit rational
center and inverse matrices, not the numerical homotopy output.
