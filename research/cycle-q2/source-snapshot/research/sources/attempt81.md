# Cycle-q2 attempt 81 — cross-area constructions and an exact original-target test

**Date:** 2026-11-04 UTC (November 3 in America/Chicago).

**Verdict: the original certificate is not established and is not disproved.**

This run explored a chain from the accepted polynomial-curve construction through a character-preserving cubic cover, a genus-two curve, elliptic quotients, a degree-three isogeny, and an A2 surface. The last auxiliary integration step is solved exactly for polynomial sources, including pole order three. The complete original source has **not** been transported into that polynomial-source class. A separate Hessian construction was made directly in the original six variables: it gives a legal denominator and correctly graded numerators, but fails the original identity. A small exact symmetry projector also shows how a certificate for the cyclic sum would yield the specified individual certificate.

These are separate statements with explicit scopes. No auxiliary identity, conditional transport operation, or failed candidate is called a cycle-q2 certificate.

## 1. Immutable target and provenance

Coordinates are `(X0,X1,X2,Y0,Y1,Y2)` and

\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)+\frac12(X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2+X_2^3X_0Y_2Y_0),
\qquad A=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2.
\]

Only a nonzero homogeneous complex-coprime denominator D, degree-(deg D+7) numerators N_i, and a polynomial Q with

\[
E=AD^2-2D\sum_iN_iF_i+F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q
\]

would finish the task. The complete expression, not only its restriction to F=0, is the acceptance test.

The attempt80 report and index, the earlier strategy atlas, and selected parts of the older compact-class report were read to avoid duplicating their tests. Their claimed generic reductions and exclusions were not re-certified or used as a proof of original existence/nonexistence here. The previous plane-cubic source chart is identified below as an input; its **new base-density calculation** was checked symbolically. The Hessian and finite-symmetry calculations start from literal F,A and do not rely on that chart.

Public sources actually consulted include the protected instance, `why.md`, `formal/README.md`, the accepted `cycle-three/solution.md`, HigherResidues, EllipticCompanions, and the split/K3 discussion. The accepted cycle-three proof concerns a different q=1 source. Its polynomial-curve family and the distinction between invariant and character-valued sources motivate the new cover calculation; they do not certify the new application.

A current symbolic-integration paper was also checked. Its logarithmic integration theorem is **not** a theorem that all these forms have rational primitives. The distinction is important here. No withdrawn broad Kuga-Satake claim is used.

## 2. Exact order-three projection: the cyclic sum is sufficient

Put

\[
A_0=X_0^3X_1^2X_2^2Y_0Y_1^2Y_2^2,\quad
A_1=X_0^2X_1^3X_2^2Y_0^2Y_1Y_2^2,\quad A_2=A,
\qquad S=A_0+A_1+A_2.
\]

For a primitive cube root omega, the transformation

\[
h(X_0,X_1,X_2,Y_0,Y_1,Y_2)
=(\omega X_0,\omega X_1,X_2,\omega^2Y_0,Y_1,Y_2)
\]

preserves F. Its determinant is omega. Direct substitution gives raw numerator characters `(omega,1,omega^2)` and residue characters `(omega^2,omega,1)`. Therefore

\[
\boxed{A_2=\frac13\left(S+\omega S\circ h+\omega^2S\circ h^2\right).}
\]

Unlike the familiar diagonal action with all three companion residue characters equal, this action distinguishes them.

### Full certificate transport, including denominators

This is an unconditional operation on a **hypothetical** certificate for S. Let `w=(1,1,0,2,0,0)`, `D_k=D(h^k z)`, and

\[
D_* =\prod_{k=0}^2D_k,
\]
\[
(N_*)_i=\frac13\sum_{k=0}^2\omega^{k(1-w_i)}N_i(h^kz)\prod_{\ell\ne k}D_\ell,
\quad
Q_*=\frac13\sum_{k=0}^2\omega^kQ(h^kz)\prod_{\ell\ne k}D_\ell^2.
\]

Then the transformed tuple is a certificate for A2 whenever the original tuple is a certificate for S. In rational-vector notation, pullback sends v to `h^(-k) v(h^kz)`, which preserves both v(F) and divergence under substitution. Linearity followed by the displayed denominator clearing proves the formula with every derivative of D retained.

If deg D=d, then deg D*=3d and deg N*=3d+7. No factor of D* can divide F because h preserves F and every D_k is coprime to F. Nonzeroness is preserved. For rational-coefficient input, the output is rational too: the two nontrivial summands are exchanged by omega-conjugation. The reverse implication follows by cyclically rotating an individual certificate and adding the three results. Thus existence for S and existence for A are equivalent.

`character_projector.py` verifies the source projection and the complete transport identity on a deliberately non-invariant denominator `D=X0+X1+X2`, with degree-eight test numerators. The test tuple is **not** itself a certificate; it tests the universal algebraic transport law, whose proof is given above. The resulting denominator is `(X0+X1)^3+X2^3`.

A separate finite enumeration finds 72 projective diagonal symmetries of F and confirms that the three characters are distinct. Enumeration is not needed for the proof once h is displayed.

**Limit:** no certificate for S has been found. This removes a separation obligation, not the integration obligation.

## 3. Retaining the character along the accepted quadratic curve

The prior plane-cubic chart uses `z_i=Y_i/X_i` and a relative numerator `(t0 t1 t2)^2`. Its physical base density is `z0^2 z1^2 z2 dz0 dz1 dz2/4`. In the new ratio variables

\[
z_0=v,\quad z_1=cv,\quad z_2=dv,\quad s=v^2,\quad t=s^3,
\]

exact differentiation gives

\[
\boxed{\frac{z_0^2z_1^2z_2}{4}\,dz_0\wedge dz_1\wedge dz_2
=\frac{c^2d}{24}\,s\,dt\wedge dc\wedge dd.}
\]

In particular the coefficient s, with s^3=t, cannot be replaced by 1 or removed by an invariant trace. In the associated ternary cubic, the transformation `s -> omega*s`, `(t0,t1,t2)->(omega^2*t0,omega*t1,t2)` preserves the equation and the relative numerator/form. The surviving factor s therefore carries the required character.

In the accepted auxiliary Jacobian coordinates, t=T/R. Its supplied family has quadratic `R(T)=aT^2+bT+c0`. Retaining the character produces

\[
r^3=\frac{T}{R(T)}.
\]

For `a*c0*(b^2-4ac0) != 0`, with the four branch points distinct, this is a connected genus-two curve: the degree-three map to P1 has four points of ramification index three, so Riemann-Hurwitz gives `2g-2=-6+8=2`.

Define delta=b^2-4ac0 and

\[
y=2ar^3T+br^3-1.
\]

The **off-curve polynomial identity** is

\[
y^2-(1-2br^3+\delta r^6)=4ar^3(r^3R(T)-T).
\]

After the finite algebraic scaling `x=delta^(1/6)r`, `lambda=-2b/sqrt(delta)`, this becomes

\[
\boxed{C_\lambda:\ y^2=x^6+\lambda x^3+1.}
\]

All these displayed identities were checked exactly. The full q=2 normal source and coefficient-family density have **not** been pulled through this chain. The physical base-density calculation identifies the missing character, but is not a substitute for that full transport.

## 4. Two elliptic quotients and an explicit 3-isogeny

The involutions `(x,y)->(1/x,+/-y/x^3)` give

\[
u=x+x^{-1},\qquad v_\pm=y(x\pm1)/x^2,
\]
\[
\boxed{E_\pm:\ v_\pm^2=(u\pm2)(u^3-3u+\lambda).}
\]

The differential pullbacks are exactly

\[
\pi_+^*(du/v_+)=(x-1)dx/y,\qquad
\pi_-^*(du/v_-)=(x+1)dx/y.
\]

Thus the two holomorphic character lines `dx/y` and `x dx/y` are retained in their span; neither is simply the invariant average. This genus-two/elliptic splitting is classical geometry, not a claim of a newly discovered general theorem. The explicit maps and normalization in this construction were verified directly.

The j invariants are

\[
j_+=-\frac{6912(2\lambda+5)^3}{(\lambda-2)^3(\lambda+2)},\quad
j_-=\frac{6912(2\lambda-5)^3}{(\lambda-2)(\lambda+2)^3}.
\]

They are nonconstant. Therefore a theorem requiring a fixed Fermat elliptic companion cannot simply be invoked.

### Exact isogeny and moving derivative

With k=lambda-2, the plus curve is isomorphic to

\[
E_k:\ y^2=x^3+9x^2-6kx+k^2.
\]

The degree-three map with kernel `{O,(0,k),(0,-k)}` is

\[
X=x-12k/x+4k^2/x^2,\qquad
Y=y(1+12k/x^2-8k^2/x^3).
\]

Its target equation is

\[
Y^2=X^3+9X^2+54kX+432k-27k^2.
\]

The substitution `X=-3*x_minus-12`, `Y=3*sqrt(-3)*y_minus` identifies this target with a constant twist of the minus quotient, whose parameter is k+4. This supplies the isogeny explicitly rather than inferring it from matching j invariants.

The code checks the full rational curve identity and `dX/Y=dx/y`. It also checks the moving-k boundary

\[
\phi^*(\partial_k\omega_{target})-\partial_k\omega_{source}
=-d_x((\partial_kX)/Y).
\]

No moving-root term is silently omitted.

## 5. A complete polynomial-source q=2 primitive on the auxiliary A2 surface

This section **solves an auxiliary integration problem, not the original certificate**.

The total moving surface from the plus quotient is

\[
F_e(k,x,y)=y^2-x^3-9x^2+6kx-k^2.
\]

Set

\[
U=y-k+3x,\qquad V=y+k-3x.
\]

Then

\[
\boxed{F_e=UV-x^3.}
\]

This connects the elliptic-family calculation to the elementary A2 surface. More importantly, it gives an explicit **normal coordinate**, not just a birational map on `F_e=0`. Put R=F_e. The inverse formulas are

\[
k=3x+\frac{(x^3+R)/U-U}{2},\qquad
y=\frac{(x^3+R)/U+U}{2},
\]

and

\[
\boxed{dk\wedge dx\wedge dy=\frac{dR\wedge dx\wedge dU}{2U}.}
\]

Let P(k,x,y) be **any polynomial**, with coefficients in any passive characteristic-zero field. Define the finite polynomial-in-R expansion

\[
\frac{P(k(R,x,U),x,y(R,x,U))}{2U}=\sum_n\phi_n(x,U)R^n.
\]

Every phi_n is polynomial in x and Laurent-polynomial in U. Thus H with `H_x=phi_2` is an explicitly computable polynomial-in-x, Laurent-in-U function. The rational 2-form

\[
\boxed{
\beta=\sum_{n\ne2}\frac{\phi_nR^{n-2}}{n-2}\,dx\wedge dU
-\frac{H}{R}\,dR\wedge dU
}
\]

satisfies **literally**

\[
d\beta=\frac{P}{F_e^3}\,dk\wedge dx\wedge dy.
\]

The terms n>2 are retained; no regular remainder is dropped. The primitive has at most order-two poles along F_e. This is not a formal series: the expansion and sum are finite.

For an explicit rational-vector reconstruction, let

\[
B_R=\sum_{n\ne2}\phi_nR^{n-2}/(n-2),\quad B_x=H/R,\quad B_U=0,
\]
\[
v_R=-2UR^2B_R,\qquad v_x=-2UR^2B_x,\qquad v_U=0.
\]

Transport these through the inverse coordinates. The resulting field has denominators only in U and satisfies

\[
\boxed{P-2v(F_e)+F_e\operatorname{div}v=0.}
\]

U is coprime to F_e even over C, since `F_e mod U=-x^3`; irreducibility follows from `UV-x^3`. Therefore clearing a sufficiently large power of U gives an actual polynomial auxiliary identity.

`auxiliary_a2_primitive.py` checks this with the nontrivial example `P=k^2 x^2+y^3+2k`, including its nonzero second-normal coefficient. The script reconstructs all three numerator polynomials with `D=U^4` and verifies the entire auxiliary q=2 expression is the zero polynomial. The full numerators are saved.

**Missing application:** the actual original q=2 source, its normal jets, and the coefficient-family trace/density have not been shown to land in this polynomial-source class. Birational parametrization, isogeny, or a finite cover does not establish that. General rational coefficients may have additional poles and nonzero classes. This is the decisive gap in this branch, not routine bookkeeping that has already been justified.

## 6. Character-valued rational integration: exact remaining channels on the curve

For `r^3=T/R(T)`,

\[
d(rh)=r\left(h'+\frac13(1/T-R'/R)h\right)dT.
\]

For a polynomial phi(T), a rational primitive of `r*phi(T)dT`, if it exists, may be projected to this character and written r*h(T). At an ordinary finite point a pole of h would produce an uncancelled derivative pole. At T=0 the local coefficient is 1/3; at a simple root of R it is -1/3. Since these are not integral resonances, regularity of the polynomial right side forces h to vanish at all three points. Thus h is a polynomial multiple of T R:

\[
h=TRH,\qquad
\mathscr L(H)=TRH'+(4R/3+2TR'/3)H.
\]

For H=T^n, the leading term is `a(n+8/3) T^(n+2)`. Therefore every polynomial phi has a unique reduction

\[
\phi=\mathscr L(H)+c_0+c_1T.
\]

Both residual classes are genuinely nonzero: a nonzero polynomial H has image degree at least two. The projection argument also rules out escaping this test by using the other cubic characters in a rational primitive. This theorem concerns polynomial twisted differentials on this auxiliary curve, not the full original multivariate primitive.

The two-dimensional character cohomology has basis

\[
\omega_0=dx/y,\quad\omega_3=x^3dx/y.
\]

The full moving connection, including explicit exact boundaries `d_x(R_j/y)`, is

\[
\partial_\lambda(\omega_0,\omega_3)
=(\omega_0,\omega_3)\,
\frac1{3(\lambda^2-4)}
\begin{pmatrix}-\lambda&2\\-2&\lambda\end{pmatrix}
+d_x(\text{displayed boundaries}).
\]

The column boundaries are in `CHARACTER_CONNECTION.json`. All cleared identities are verified symbolically. This provides a way to retain and transport the actual character; it does not assert that its two residual coefficients vanish for the original source.

## 7. Direct original-target construction from Hessian geometry

Let H=Hess(F), D=det H and

\[
\boxed{N=\frac5{24}\operatorname{adj}(H)\nabla A.}
\]

D has degree24 and N has degree31, exactly the required grading. Euler's identities give

\[
H z=5\nabla F,\quad z\cdot\nabla A=12A,
\]

so

\[
2N\cdot\nabla F=AD
\]

identically. The complete expression nevertheless is

\[
\boxed{E=\frac5{24}F D^2\operatorname{div}(H^{-1}\nabla A).}
\]

All inverse-matrix derivatives are retained:

\[
\operatorname{div}(H^{-1}\nabla A)
=\operatorname{tr}(H^{-1}\operatorname{Hess}A)
-(\nabla\log D)^TH^{-1}\nabla A.
\]

### Legality and exact failure

F is smooth over C by a direct maximal-modulus argument. At a nonzero common gradient zero, choose a largest coordinate of modulus M. Its pure derivative has modulus 6M^5, whereas the total coupling derivative is bounded by 2M^5 for an X coordinate and M^5 for a Y coordinate. This is impossible. A reducible projective hypersurface in P5 would have intersecting components and be singular, so F is irreducible over C.

Use the exact point

\[
z=(1,1,1,\alpha,\alpha,\alpha),\qquad 2\alpha^6+\alpha^2+2=0.
\]

The degree-six polynomial is irreducible over Q, checked exactly. At this point

\[
D=647522500+901358750\alpha^2+429615000\alpha^4\ne0.
\]

Hence F does not divide D, proving the required **complex** coprimality. The full expression satisfies

\[
\boxed{
(E/F)(z)=\frac{78125\alpha}{12}
\left(8708378758382\alpha^4+7884627577687\alpha^2+719791987078\right)\ne0.
}
\]

Nonzeroness is exact in the degree-six field, not numerical. Thus even F^2 does not divide E, and no Q can make this candidate a certificate. An independent differentiation of the polynomial numerator circuit reproduces the same full remainder.

### A natural density correction was also tested

The alternative field

\[
v_1=-\frac5{24}\operatorname{adj}(H)\nabla(A/D)
\]

also has `2v_1(F)=A`. Together with `v_0=(5/24)H^{-1}grad A`, it yields a natural affine family `(1-t)v_0+t v_1`, with common denominator D^2, degree48.

The exact value of t needed to cancel the residue at the point above is a non-rational element of Q(alpha), saved in `HESSIAN_DENSITY_WITNESS.json`. No constant complex t can solve the generic equation: a linear identity over the rational function field with rational coefficients, if solved by a constant, forces that constant to lie in Q (equivalently inspect any nonzero coefficient after polynomial reduction modulo the rational monic F). Therefore this entire **constant two-density family** fails. Rational function coefficients and other Hessian-supported numerators are not excluded.

## 8. Other explored shortcuts and precise limits

A test of the 48 coordinate inversion/permutation transformations of the three ratio variables found equality of the elliptic j ratio at the exact point `(2,3,5)` only for the three already known cyclic permutations. This excludes those specific proposed rational identities because a single unequal exact value disproves an identity; it does not classify all birational symmetries.

The generic bielliptic splitting and the Hessian construction are mathematically distinct from the older Euler-only or bounded-Z tests. The cyclic-sum projector is a source-specific use of finite representation theory. None of these computations was a blind denominator sweep.

## 9. Exact remaining gap and execution record

The cross-area chain reaches a **complete auxiliary polynomial-source primitive**. What is not known is whether the full original source can be transferred into it, with all source-character factors, changing coefficient-field derivatives, twice-normal terms, regular remainder, and finite trace. No full original current has been produced from this chain. The direct original Hessian current fails by the exact witness above.

No original tuple D,N,Q passed the target test. No Lean existence proof was produced. No claim of global nonexistence is made. There were no external messages, repository modifications, publications, or task changes. A private Math-project checkout was not used. Python/SymPy executed the algebraic checks locally; the final runner records the scripts, return codes and elapsed execution times. The research packet is local unless a separate tool explicitly records a Library upload; no such upload is claimed.

## 10. Primary references

- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-three/solution.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/lean/HodgeComputer/Constructions/HigherResidues/README.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/lean/HodgeComputer/Constructions/EllipticCompanions/README.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/docs/03a-split-and-k3.md
- Chen, Cox, Wang, *Symbolic Integration of Differential Forms: From Abel to Zeilberger*, version3, https://arxiv.org/html/2601.00721v3. Its rational/logarithmic distinction and limits on a fixed-pole decision procedure were inspected; it is not imported as a rational-exactness theorem.
- Shaska and Voelklein, *Elliptic subfields and automorphisms of genus 2 function fields*, https://arxiv.org/abs/math/0107142. Classical context for elliptic subcovers; the formulas used in this run are checked independently in the accompanying scripts.
