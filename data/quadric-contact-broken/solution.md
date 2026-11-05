# A finite-algebra contact certificate for `quadric-contact-broken`

The theorem entry point is `Submission.certificate`, with the exact target
`HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.d HodgeSubmission.q`.
The construction gives a strict certificate: the residual polynomial in the
cleared identity is zero. The line over a finite coefficient algebra, the
invertible source matrix, and denominator legality are constructed within the proof.

## Cubic reduction

Write the protected coordinates as `(x,a,c,y,b,d)` and put

\[
\alpha=b/a,\quad\beta=d/c,\qquad
S=2(x^2+y^2),\quad T=4xy,\quad B=a^2,\quad C=c^2.
\]

Let

\[
G=2S^3+ST^2+S(pB^2+qBC+sC^2)+kTBC+uB^3+vC^3,
\]

where

\[
(p,q,s,k,u,v)=
\left(40\alpha^2,40\alpha\beta,40\beta^2,
\tfrac{20}{7}\alpha(1+2\beta^2),16(1+\alpha^6),16(1+\beta^6)\right).
\]

After this substitution, the exact composition is `G = 16F`. This identity,
the source composition `BT = 4a²xy`, and the derivative identities are supplied
by the Lean modules.

## The line and its finite coefficient algebra

Work over the localization `O` of `ℚ[α,β]` at all polynomials nonzero at `(1,2)`.
Evaluation at that point is a total ring homomorphism `O → ℚ`; every element
with nonzero evaluation is a unit.

A line is written

\[
S=\xi B+\eta C,\qquad T=\zeta B+\omega C.
\]

Set `η=rξ`, `ω=rζ+(v−ur³)/(kr)`. Eliminating `ζ` leaves a quadratic and a cubic
in `ξ`. Their resultant is `k¹²r⁹` times an explicit degree-27 polynomial.
The leading coefficient of that polynomial is `u¹⁰v`, a unit in `O`.
Normalize it to a monic polynomial `P` and form the finite free algebra
`E=O[r]/(P)`, with basis `1,r,…,r²⁶`.

The resultant and subresultant identities are proved as universal commutative
ring identities. Exact rational polynomial Bézout identities at `(α,β)=(1,2)`
show that `r`, the quadratic leading coefficient, and the relevant linear
subresultant coefficient are units in the specialized algebra. Their
multiplication matrices specialize functorially. Nonzero specialized
determinants therefore lift these units to `E`. The subresultant formula then
constructs `ξ`, and the chart constructs `η,ζ,ω`.
All four coefficients of the restriction of `G` to this line are proved zero.
Neither irreducibility nor squarefreeness of `P` is needed.

## A strict cubic certificate

Put

\[
L=S-\xi B-\eta C,
\]
\[
U=\eta T+(2\xi\omega+\eta\zeta+k)B+3\eta\omega C,
\qquad
V=\xi T+3\xi\zeta B+(\xi\omega+2\eta\zeta+k)C.
\]

The polynomial vector `(ξU−ηV, ζU−ωV, U, −V)` has zero divergence, is tangent
to `L`, and sends `G` to `LJ` for a quadratic polynomial `J`.
The monomials spanning `J`, in order, are
`SB, SC, T², TB, TC, B², BC, C²`.

Take the first eight power-basis coordinates of these eight source coefficients.
The resulting square matrix has an explicitly supplied rational inverse on the
good fiber. Lean checks both the source reductions modulo `P` and the matrix
inverse. This proves that its generic determinant is a unit in `O`.
The corresponding inverse column defines an `O`-linear functional that sends
`J` to `TB` when applied to its coefficients.

Apply the regular representation of `E` and clear the matrix pencil `L` by its
adjugate. The scalar denominator is its determinant `D₀`; the four scalar
numerators are obtained by the functional applied to the numerator matrices
times that adjugate. Differentiating the adjugate identity proves

\[
\sum_i N_{0,i}\partial_iG=D_0BT,\qquad
D_0\sum_i\partial_iN_{0,i}=\sum_iN_{0,i}\partial_iD_0.
\]

The denominator and all four numerators are homogeneous of degree 27.
The denominator is nonzero because the pencil evaluates to the identity at
`(S,T,B,C)=(1,0,0,0)`.

## Homogeneous clearing and the sextic lift

Only finitely many coefficients occur. Clear their denominators simultaneously
in `O`, then homogenize their substitution `α=b/a, β=d/c` using a common power
of `ac`. This produces polynomials `Q,P_S,P_T,P_B,P_C` homogeneous of a common degree
`h=2(n+27)` for some natural number `n`. In the fraction field, they are the
substituted `D₀,N₀` multiplied by one polynomial clearing factor `H`. On
`b=a,d=2c`, this factor is `κ(ac)^n` for a rational scalar `κ≠0`.

Let `δ=x²−y²`. The final denominator and numerators, in protected order, are

\[
D=a^2c^2Q,
\]
\[
N=\bigl(
a^2c^2(xP_S-yP_T),\;
2\delta ac^2P_B,\;
2\delta ca^2P_C,\;
a^2c^2(-yP_S+xP_T),\;
2\delta bc^2P_B,\;
2\delta da^2P_C
\bigr).
\]

The horizontal derivations are
`x∂x−y∂y`, `−y∂x+x∂y`, `a∂a+b∂b`, and `c∂c+d∂d`.
They are extended to the actual fraction field and proved to kill the parameter
coefficient ring. Their chain rule has scales `4δ,4δ,2a²,2c²`.
Together with `G=16F`, this makes the rational field `N/D` send `F` to
`(δ/4)BT=δa²xy=A`.
In each divergence cross term the derivative of the common
clearing factor cancels. These facts prove the exact strict equations
`directional F N = A*D` and `divergenceNumerator D N = 0`.
The denominator is homogeneous of degree `2n+58`, and every numerator is
homogeneous of degree `2n+59`, as required for `q=1`. These statements also
cover a component that vanishes identically.

## Denominator legality

Specialize `(a,c,y,b,d)=(1,1,0,1,2)`, leaving `x` free. The protected sextic
becomes `x⁶+35x²+67`. The final denominator becomes `κ` times

\[
\det(2x^2I-M_{\xi+\eta}).
\]

An exact polynomial Bézout identity in the specialized degree-27 quotient
proves that `M³+140M+536I` is invertible for `M=M_{ξ+η}`. A matrix polynomial
Bézout identity gives relative primality of the displayed determinant and
`x⁶+35x²+67`, using `(2x²)³+140(2x²)+536=8(x⁶+35x²+67)`.
The protected sextic is monic in `x`, so the repository's
specialization theorem lifts this relative primality to the full polynomial
ring. In particular, the final denominator is nonzero.

Finally, coefficient extension from `ℚ` to `ℂ` preserves the polynomial
identities and homogeneity. `Solution.lean` binds the resulting sextic and
numerator to the exact protected target. The final transitive axiom audit must
allow only `propext`, `Classical.choice`, and `Quot.sound`; printed axiom reports
from individual modules do not replace that audit.

## Attribution

This work develops the supplied private draft, whose notes credit earlier
discussions and the hodge.computer documentation for the reflection observation
and cubic-surface strategy, and record ChatGPT assistance. OpenAI Codex assisted
with the present mathematical development, Lean implementation, checking, and
exposition. The certificate contract and polynomial differential framework use
the repository's `HodgeTestbed` and `HodgeComputer` work; credit belongs to their
authors and contributors. The general algebraic and formal results used here
come from Lean and mathlib and their authors and contributors. The determinant,
adjugate, resultant, subresultant, and polynomial Bézout identities needed for
this construction are supplied explicitly or proved using those libraries.
