# Cycle-q2 — Attempt 72: online-guided global test of the weighted-Euler construction

Date: 2026-11-03. **Status: no original certificate and no Lean existence proof.**

This was a fresh research attempt. The work uses the exact target below, primary online sources, the attached attempt70 report, and the explicitly displayed cubic model of the preceding attempts. The new calculations are exact characteristic-zero calculations on a source-bound scaling curve. They are not a new denominator sweep, a Taylor truncation, or a finite-field failure.

## 1. Exact target and boundary

In order `(X0,X1,X2,Y0,Y1,Y2)`,

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\tfrac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),
\]
\[
A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,\qquad q=2.
\]

The sought witness is nonzero homogeneous D, coprime to F over C, six Ni homogeneous of degree deg(D)+7, and a polynomial Q with

\[
AD^2-2D\sum_iN_iF_i+F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]

No such tuple was constructed. The curve currents below must not be passed to the original verifier as a certificate. No full original polynomial-identity check was claimed in the absence of a tuple. The exact original *source transport*, which is different from a certificate check, was checked.

The residue character remains zeta6^2 under weights (2,1,0,3,2,1). No invariant averaging is performed. Original source, all cyclic couplings, and the q=2 second-normal differentiation are retained.

## 2. What the online research supplies—and does not supply

The exact upstream instance and its mathematical context distinguish this target from the accepted q=1 cycle-three construction. The latter supplies cubic-to-Jacobian transport and polynomial-family integration for its own source; its proof does not automatically handle the nontrivial character of the present numerator. The HigherResidues library offers second-normal transport once an actual compatible polynomial family and its derivative data are supplied. Neither document gives the missing family/current for this target.

The primary cycle-q2 discussion describes an independently derived character cover with a nonzero vertical remainder and an unresolved transverse connection equation. These are prior authors' research claims, not results independently replayed here.

Chen, Cox and Wang, *Symbolic Integration of Differential Forms: from Abel to Zeilberger* (arXiv:2601.00721v1), discusses residue-based rational integration and the distinction between rational and logarithmic primitives. This informed the decision to test global rational exactness rather than compute more formal coefficients. Its general logarithmic integration statements do not establish this certificate.

The concrete new question was: can the scalar weighted-Euler construction of attempt71 actually be rationalized along a whole scaling orbit?

## 3. Bind the new test to the physical source

Use

\[
R=X_2^2,\quad P=\frac{Y_0Y_1}{X_0X_1},\quad U=\frac{Y_1^3}{X_1^3},\quad Z=\frac{Y_2}{X_2},
\quad a=\frac{X_0^2X_1}{X_2^2Y_1},\quad b=\frac{X_1^3}{X_2^2Y_1}.
\]

Define

\[
L=P^6+U^2,\quad M=PU^2b/2,\quad N=PUZ/2,
\]
\[
K=(U^4+U^2)b^3+U(1+Z^6)+ZU^2b^2/2,
\quad G=La^3+Ma^2+Na+K,\quad h=P^2ZU^4b^2/24.
\]

`bind_original_source.py` checks, by exact rational simplification,

\[
F=(R^3/U)G,
\]
\[
\frac{A\,dX_0\wedge\cdots\wedge dY_2}{F^3}
=\frac{dR}{R}\wedge\frac{ha^2}{G^3}\,dP\wedge dU\wedge dZ\wedge da\wedge db.
\]

The monomial exponent determinant is **+24**. These equalities retain the orientation of the six-form as displayed. Projective contraction contributes the usual nonzero factor 2; changing residue order can change an overall sign. Neither changes the exactness test, and neither changes the original physical numerator.

Put g=G_a. The second-normal scalar is

\[
\rho=\frac12(g^{-1}\partial_a)^2(ha^2/g)
=\frac{h}{g^5}\bigl(N^2-15LNa^2-12LMa^3-2M^2a^2-2MNa\bigr).
\]

This is the same explicit source formula, but the entire scaling-curve substitution below is new. The differentiation and the curve's root-frame representation were checked independently.

## 4. The global scaling curve

Consider the actual orbit

\[
P=s,\quad U=s^3,\quad Z=1,\quad b=1,\quad a=c/s.
\]

Then, identically,

\[
G=s^3 C(s,c),\qquad
C=2c^3+\frac{s^2}{2}c^2+\frac12c+2+\frac32s^3+s^9.
\]

The scalar Euler current has components JP=P Phi and JU=3U Phi. Its divergence is `(S+4)Phi`, with S the moving-root lift of `P partial_P+3U partial_U`. Along this orbit it would require

\[
\frac{d}{ds}(s^4\Phi)=f(s,c),
\]

where

\[
f=\frac{s^5}{24}\frac{H}{g_C^5},\quad
 g_C=6c^2+s^2c+\tfrac12,
\]
\[
H=\tfrac14-15c^2-12s^2c^3-\tfrac12s^4c^2-\tfrac12s^2c.
\]

The equality `s^3 rho|orbit=f` is checked symbolically over Q(s,c). Equivalently,

\[
f=\frac{s^5}{48}(g_C^{-1}\partial_c)^2(c^2/g_C).
\]

Thus the test is an exact algebraic-function integration problem on a whole curve, not a finite set of sampled source values.

## 5. Geometry and a complete rational-primitive bound

Set

\[
\theta=c+s^2/12,\quad
p=\tfrac14-s^4/48,\quad
q=1-s^2/48+3s^3/4+s^6/864+s^9/2.
\]

The equation becomes `theta^3+p theta+q=0`. Let Delta=4p^3+27q^2.

Exact polynomial gcd verifies that Delta is squarefree of degree 18. At infinity, theta/s^3 tends to one of the three distinct roots of `2 alpha^3+1=0`. All three infinity points are unramified. Riemann–Hurwitz gives `2g-2=-6+18=12`, hence **genus 7**.

Absolute irreducibility is also justified, not inferred from rational irreducibility. A root in C(s) of the monic cubic would be a polynomial of degree 3. Coefficients of s^9,s^8,s^7,s^6 force

\[
\theta=\alpha s^3+\frac{s}{144\alpha}-\frac1{2592\alpha^2},\qquad \alpha^3=-\tfrac12.
\]

But the s^4 coefficient in `theta^3+p theta+q` is

\[
-\frac1{124416\alpha^2}\ne0.
\]

So the curve is geometrically irreducible. Squarefree discriminant implies smooth finite points; the displayed infinity charts complete its smooth compactification.

If `f ds=dv` for rational v, then v can have poles only where f ds does. At a simple ramification point, g_C is a uniformizer up to a unit and ds has a simple zero. Thus f ds has pole order at most 4 and v at most 3. At infinity, f=O(s^-14), so v has no pole.

Consequently `Delta^2 v` is regular on the smooth affine curve. Because its coordinate ring is normal, it is a polynomial in s and theta of theta-degree at most 2. The source has trace zero; subtracting a constant from v makes v trace zero. Therefore every possible primitive has the form

\[
v=\frac{W_0(s)\theta+W_1(s)(\theta^2+2p/3)}{\Delta^2},
\qquad \deg W_0\le33,\quad \deg W_1\le30.
\]

The bounds follow from theta having pole order 3, the second trace-zero basis element having pole order 6, and Delta^2 having pole order 36 at each infinity point. Leading terms cannot cancel at all three infinity points unless both coefficients vanish. These are proved bounds, not a guessed denominator window.

## 6. Exact negative result for that one-direction construction

In the trace-zero basis e=(theta,theta^2+2p/3), let

\[
J_p=\begin{pmatrix}2p^2&-6pq\\9q&4p^2\end{pmatrix},\qquad
J_q=\begin{pmatrix}9q&4p^2\\-6p&18q\end{pmatrix},\qquad
T=J_p p'+J_q q'.
\]

The moving derivative has connection T/Delta. Both columns were verified directly modulo the cubic, retaining the moving root and moving basis.

Write the actual source vector as S/Delta^3. Its exact formulas are in the scripts and JSON; their equality to the direct second-normal expression is checked after clearing denominators and reducing modulo C. A primitive requires

\[
\Delta W'+(T-2\Delta'I)W=S.
\]

The complete coefficient system has **97 equations and 65 unknowns**. Exact rational row reduction gives

\[
\operatorname{rank}(A)=65,\qquad \operatorname{rank}([A\mid S])=66.
\]

An exact rational dual vector y is saved and independently checked to satisfy

\[
y^T A=0,\qquad y^T S=1.
\]

This proves inconsistency over **C**, not merely over Q or a finite field. Together with the pole bounds, it proves **no rational primitive exists on this particular entire scaling curve**.

Scope matters. This is not a nonexistence theorem for the original certificate or for unrestricted multi-direction currents. It also must not be advertised as a generic-parameter no-go without a separate specialization argument addressing possible parameter poles. Its direct conclusion is that this smooth, source-bound Euler orbit has a genuine compact obstruction, despite local formal integrability.

## 7. Positive reconstruction: rational part plus exact compact remainder

A further exact calculation constructs a global decomposition on that curve:

\[
f\,ds=d\left(\frac{W_0\theta+W_1(\theta^2+2p/3)}{\Delta^2}\right)
+\frac{H_0(s)+H_1(s)\theta}{3\theta^2+p}\,ds.
\]

This uses a 109-by-91 rational coefficient system, with rank 91, and verifies every coefficient in the resulting identity. The reconstructed W0,W1 have degree 35 and H0,H1 degree 7. All 16 affine-basis coefficients of the remainder are nonzero. This is not a claim that one vector spans 16 dimensions.

The remainder is regular at finite points. Exact Laurent expansion at all three infinity points shows **zero residues**. Thus it defines a compact de Rham class in the 14-dimensional H1 of the genus-seven curve. The no-primitive proof above shows this class is nonzero.

The full rational coefficients are saved in `EXACT_CURVE_REMAINDER.json`. No numerical fitting or finite-field inference enters these computations. This is a genuine rational decomposition with an explicitly preserved remainder—not an original certificate.

## 8. Exact unresolved task and non-repetition checkpoint

The last formal Euler construction did not settle rationality. The new test shows a real nonzero compact class on the chosen orbit; taking more local Taylor coefficients cannot remove that class on the same curve.

The original target remains unresolved because no globally rational current using the full independent directions has been constructed. In particular, the original P,U components need not be proportional to (P,3U), and Z or b derivatives are also available. Their contributions can matter even when their values are held fixed in a one-dimensional test. The calculation does not rule them out.

A future construction must serve the complete source, preserve any regular remainder, descend and transport to the six physical coordinates, clear a legal homogeneous denominator coprime to F over C, and pass the literal `E=F^3Q` identity. None of those final existence obligations was claimed completed here.

**Do not repeat:** this Euler orbit test, the 97-by-65 no-primitive system, the 109-by-91 exact decomposition, or more Taylor expansions as a proposed resolution of this orbit's rationality. The reusable outputs are the exact dual obstruction, full rational decomposition, source-binding identities, and verified moving connection.

## 9. Execution and access record

Executed locally with Python and SymPy 1.14.0:

- `test_euler_rationality.py`: PASS exact ranks and dual witness.
- `verify_source_and_geometry.py`: PASS normal differentiation, complete root-frame source identity, moving derivatives, squarefree discriminant and irreducibility coefficient obstruction.
- `reconstruct_curve_remainder.py`: PASS full rational decomposition and all infinity residues.
- `bind_original_source.py`: PASS exact original six-form and scaling-orbit source bindings.

The web tool accessed the public project records and research paper. A direct git clone failed because the container could not resolve github.com; no complete checkout or commit hash is claimed. The attached attempt70 archive and report were accessible. No Lean executable was found via `command -v lean`, and no Lean proof was executed. No external messages, repository changes, publications, or scheduled tasks were made.

Primary-source URLs and attribution are in `REFERENCES.md`. This packet saves new scripts, exact witnesses and logs, not a fabricated certificate.
