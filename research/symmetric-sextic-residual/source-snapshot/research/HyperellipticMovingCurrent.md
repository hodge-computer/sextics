# A moving-point formula and obstructions to the natural pole choices

This is a new algebraic route built on the exact genus-three model. It does
not repeat the earlier fiber-only ODE or bounded Gauss–Manin searches. No full
certificate has been obtained, and no new Lean theorem is claimed.

## 1. An actual current with all three base derivatives

Keep the exact model `y^2=H(u)` over `K=C(q,P,Q)` and the exact target density
`B(u) du dq dP dQ/(H(u)y)` from `DirectCertificateResearch.md`. The leading
coefficient of `H` is the constant `-729/16`.

Let `L/K` be finite separable and let `alpha,beta` in `L` satisfy
`beta^2=H(alpha)` with `beta != 0`. Base derivations extend to `L`.
For a vector `T=(Tq,TP,TQ)`, write

\[
\eta=T_q\,dP\wedge dQ-T_P\,dq\wedge dQ+T_Q\,dq\wedge dP.
\]

Closedness is the actual equation

\[
\partial_qT_q+\partial_PT_P+\partial_QT_Q=0.
\]

Define the rational three-form

\[
\mathcal C=\eta\wedge\frac{\beta}{y}\,d\log(u-\alpha).
\]

The differentials of `alpha` and `beta` are included. Put

\[
Z=T(\alpha),\qquad J(u)=T(H(u)),\qquad
c=\frac{H'(\alpha)Z+J(\alpha)}{H(\alpha)}.
\]

Then the exact identity, in the order `(u,q,P,Q)`, is

\[
d\mathcal C=
\frac{\beta}{2H(u)y}
\frac{J(u)+H'(u)Z-H(u)c}{u-\alpha}
\,du\wedge dq\wedge dP\wedge dQ.
\]

The numerator vanishes at `u=alpha`. Its quotient is a polynomial of degree
at most seven. Thus a genuine moving-point contact supplies an explicit
eight-coefficient source vector.

### Direct flux proof

Write `C=iota_W(du dq dP dQ)/y`. Its four components are

\[
W=-\frac{\beta}{u-\alpha}(Z,T_q,T_P,T_Q).
\]

Closedness cancels the divergence of `T`, and the moving-denominator terms
cancel between the `u` component and the three base components. Hence

\[
\operatorname{div}W=-\frac{T(\beta)}{u-\alpha}.
\]

Differentiating `beta^2=H(alpha)` gives `2T(beta)/beta=c`. Since

\[
W(H)=-\frac{\beta}{u-\alpha}(H'Z+J),
\]

the weighted divergence `div W-W(H)/(2H)` is exactly the displayed source.
This is an elementary rational-function identity, not an appeal to
cohomological spanning.

For a finite algebra of rank `n`, the normalized-trace source is exactly

\[
B_{\mathcal C}(u)=\frac1{2n}\operatorname{Tr}_{L/K}
\left(\beta\frac{J(u)+H'(u)Z-H(u)c}{u-\alpha}\right).
\]

An arbitrary coefficient multiplier need not preserve the closedness of eta.
Selecting one algebraic sheet and then tracing still includes all its
conjugates. Neither operation can be used to assume a desired source.

## 2. The target's degree-eight term has an explicit correction

On `p=1`, let

\[
l_X=-4+18q,\qquad l_Y=-4P^3+18PQ.
\]

The actual leading coefficient of the target numerator is

\[
b_8=\frac3{128}(l_X-i l_Y).
\]

Set

\[
V(u)=\frac{l_X-i l_Y}{5832}\,u.
\]

Then

\[
\widetilde B=B-(HV'-H'V/2)
\]

has degree at most seven, because `h8=-729/16` and
`-3*h8*(lX-i*lY)/5832=b8`. The difference is the explicit fiber-exact term

\[
\frac{B-\widetilde B}{Hy}\,du=d(V/y).
\]

Wedging with all three base differentials removes the base derivatives of
this correction. The trace problem therefore has the precise eight-coefficient
target `Btilde`, without dropping any of the original density.

This is a usable exact-source interface. It still does not supply the
required finite algebra and closed forms realizing those eight coefficients.

## 3. Vandermonde points add no odd logarithmic classes

The relevant character is odd under the hyperelliptic involution
`iota:(u,y)->(u,-y)`. A ramification point is fixed by this involution.
Residue is preserved by pullback, so an odd differential at such a point has

\[
\operatorname{Res}\omega
=\operatorname{Res}\iota^*\omega
=-\operatorname{Res}\omega=0.
\]

Thus allowing poles at the Vandermonde branch points does not enlarge the
odd connection by logarithmic residue classes. Those poles remain of the
second kind and are already handled by Hermite reduction. Substituting
`beta=0` into the current formula is invalid and does not evade this fact.

## 4. Base forms and arbitrary quadratic point covers can trace to zero

If adjoining `beta=sqrt(H(alpha))` is a genuine quadratic extension and eta
descends before that extension, the source is odd under `beta->-beta` while
all the other displayed quantities are fixed. Its normalized trace is zero.
This explains why choosing an arbitrary point on the curve and a base form
is not enough. A genuine contact can avoid this situation by making the
closed form and the chosen point transform together.

The source-zero loci `r=0` and `R=0` do not themselves remove the issue. They
are the original coordinate hyperplanes. The vanishing of `A` on a proposed
pole divisor is not an exact-source identity.

## 5. Even an auxiliary K3 form can cancel under the full trace

There is a stronger obstruction to a tempting construction. Choose

\[
z^2=f(q,P),\qquad \eta=\frac{dq\wedge dP}{z},
\]

with `f` independent of `Q`, and choose `alpha` from

\[
H(\alpha)=f,\qquad \beta=z.
\]

For example `f=1+q^6+P^6` gives the familiar holomorphic two-form on a smooth
double-sextic K3 surface. Eta is closed and need not be exact. Thus this is
not dismissed merely for using an exact parameter form.

Here `T=(0,0,1/z)`, `c=0`, and

\[
\alpha_Q=-H_Q(\alpha)/H'(\alpha).
\]

Before tracing, the source is

\[
\frac12\frac{H_Q(u)-H'(u)H_Q(\alpha)/H'(\alpha)}{u-\alpha}.
\]

Take the full degree-eight algebra defined by `H(alpha)-f=0`. Its two exact
trace identities are

\[
\operatorname{Tr}\frac1{u-\alpha}
=\frac{H'(u)}{H(u)-f},
\]

\[
\operatorname{Tr}\frac{H_Q(\alpha)}{H'(\alpha)(u-\alpha)}
=\frac{H_Q(u)}{H(u)-f}.
\]

The second is Lagrange interpolation; `deg H_Q <= 7` because the leading
coefficient of `H` is constant. The two source terms cancel identically.
The normalized trace is **zero**.

An independent finite-algebra computation verifies these identities over
`Q(i)` for the exact target at `(q,P,Q)=(1,2,3)`, where the auxiliary level
is 66 and the degree-eight algebra is separable. The calculation uses the
polynomial resolvent `(A(u)-A(t))/(u-t)` modulo `A(t)=H(t)-66`, without
numerical roots. The general cancellation follows from the two displayed
identities, not from that single test.

To avoid this cancellation one needs a genuine contact component or a
nonuniform closed residue form, rather than the full unweighted level-set
cover. This is an exact obstruction to that proposed workaround, not a
claim that all finite correspondences fail.

## 6. Exact forms do not create new horizontal residue classes

Taking eta of the form `d zeta` ensures closedness, but

\[
\eta\wedge\Theta=d(\zeta\wedge\Theta)+\zeta\wedge d\Theta.
\]

The residues of Theta at the two moving sections are the constants `+1,-1`.
Locally it is `(+/-1+O(v))dv/v`, so `dTheta` has no pole along those sections.
Consequently this operation removes the new moving-section poles modulo an
exact term. It can produce useful second-kind contributions with other base
denominators, but it does not manufacture the missing logarithmic classes.

## 7. A classical obstruction to poles only on A and the Vandermondes

There is an independent geometric reason those particular supports cannot
carry this source at any pole order. This paragraph is a classical argument,
not a newly formalized Lean theorem.

The twelve relevant hyperplanes are the six coordinate hyperplanes and the
three coordinate-equality hyperplanes within each block. Each cuts a smooth
threefold out of this exact sextic. After reduction of `7F` modulo five, a
coordinate cut is a diagonal Fermat sextic in five variables; a coordinate
equality merely changes one nonzero diagonal coefficient from 2 to 4. Their
gradients have no projective common zero. The same homogeneous determinant
lifting argument used for the full sextic proves characteristic-zero
smoothness of these restrictions.

By weak Lefschetz, each such smooth threefold has `H^{2,0}=0`. The divisor
support/Gysin description therefore gives no `H^{3,1}` contribution from
their union. Intersections and exceptional loci over codimension-two centers
do not repair the missing `(3,1)` component.

The source class is nonzero. Indeed, if `A` were in the degree-six Jacobian
ideal, it would be a sum `sum L_i F_i` with linear `L_i`. In every mixed term
of this F, each individual variable has exponent at most two. Hence the
monomials `X_i^5 X_j` in this sum can come only from the pure sixth-power
derivative `6 X_i^5` times the corresponding coefficient of `L_i`. Those
monomials are absent from A, so all 36 linear coefficients vanish, a
contradiction. Griffiths' residue description identifies this nonzero
degree-six class with the required `(3,1)` class.

Thus a legal denominator whose irreducible factors are only those of
`A*Vandermonde_X*Vandermonde_Y` cannot give the desired certificate, regardless
of their exponents. This does not exclude denominators on genuinely new
contact divisors.

## 8. A further support candidate, still unresolved

The completed square also exhibits the natural cubic factors

\[
U=(r+a)+i(R+b),\qquad V=(r+a)-i(R+b),\qquad UV=k\quad\text{on }F=0.
\]

The degree-six support `k=0` lies outside the earlier scalar subring
`C[sum X_i^6,sum Y_i^6,q,Q]` because it depends on p and P. Its weighted base
is a sextic in `P(1,2,1,2)`, and the split conic makes the generic sign cover
elliptic there. However, the inherited base two-form has trivial permutation
character, whereas the target has sign-times-sign character. That inherited
form alone is insufficient. No source-bearing additional form or full
certificate on this support has been established.

## Reproduction and current limit

Run `audit_hyperelliptic_current.py` with SymPy. It checks the universal flux
identity, the exact degree-eight division formula, the explicit target
degree correction, and the finite-algebra trace cancellation above.
The receipt is `hyperelliptic_current_audit.json`.

The genuine constructive gap is now the exact eight-coefficient trace match
to `Btilde` using actual nonbranch contact points and compatible closed forms.
PR219's norm-contact residue forms are plausible inputs, but their existence
or cohomological span must not be substituted for that rational identity.
