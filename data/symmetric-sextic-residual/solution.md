# A relative primitive for the symmetric sextic

## Target and draft status

Put \(Q_X=X_0X_1+X_0X_2+X_1X_2\) and
\(Q_Y=Y_0Y_1+Y_0Y_2+Y_1Y_2\). The fixed target is
\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)
 +\frac57Q_X^2Q_Y+\frac{10}{7}Q_XQ_Y^2,
\qquad A=X_0X_1X_2Y_0Y_1Y_2,\qquad q=1.
\]
This is an **incomplete proof draft**. The algebra below reduces the target
to a relative rational primitive. The classical existence argument below
uses geometric and de Rham inputs that remain unformalized. This layer's
[Solution](Solution.lean) retains one admitted lemma,
`Submission.relative_primitive_exists`; its `Submission.certificate` is
not a verified certificate. The primitive-to-certificate transport from
PR #223 is included here and has no admissions.

## Reflection chart and residue

Use the chart
\[
X=(1+v,1-v,b),\qquad
Y=(c+\lambda v,c-\lambda v,d).
\]
The substituted equation is \(H=f(\lambda,b,c,d,v^2)\), with \(f\) the exact
`rawWeighted` polynomial in
[WeightedPrimitiveTransportCore](WeightedPrimitiveTransportCore.lean).
Writing
\[
P=b d(1-u)(c^2-\lambda^2u),
\]
the transformed source coefficient is \(A_H=4vP|_{u=v^2}\).
[SymmetricAffineJacobian](SymmetricAffineJacobian.lean) checks the full
six-coordinate map \((a,\lambda,b,c,d,v)\mapsto(aX,aY)\), its determinant
\(4a^5v\), and the sixth-power scaling of \(F\) and \(A\).
The projective source coefficient is consequently \(A_H/H^2\).

[SymmetricAffinePrime](SymmetricAffinePrime.lean) proves \(H\) irreducible.
[SymmetricAffineField](SymmetricAffineField.lean) constructs the function field
\(K=\operatorname{Frac}(\mathbb C[\lambda,b,c,d,v]/(H))\).
The point \((0,0,0,0,i)\) has \(H=0\) and \(H_v=-48i\), proving that
\(g=H_v\) is nonzero in \(K\). Hence the canonical tangent derivatives
\(E_j=\partial_j-(H_j/H_v)\partial_v\), for
\(j\in\{\lambda,b,c,d\}\), are defined on the actual chart field.

The relative residue density is
\[
\rho=\left.\frac{2(f_uP_u-f_{uu}P)}{f_u^3}\right|_{u=v^2}.
\]
The needed two-form is
\[
\beta=\beta_0\,dc\wedge dd-\beta_1\,db\wedge dd
       +\beta_2\,db\wedge dc,
\qquad E_b\beta_0+E_c\beta_1+E_d\beta_2=\rho.
\]
[SymmetricPrimitiveEndpoint](SymmetricPrimitiveEndpoint.lean) packages these
three elements of \(K\) and their equation as `RelativePrimitive`.

## Cubic trace cancellation

[CubicResidueTrace](CubicResidueTrace.lean) proves an exact companion-matrix
trace identity for a cubic equation and quadratic source.
[SymmetricCubicTrace](SymmetricCubicTrace.lean) binds their coefficients to
the protected equation: \(f=\ell u^3+f_2u^2+f_1u+f_0\) and
\(P=p_0+p_1u+p_2u^2\). Its scalar density
\(r(u)=2(f_uP_u-f_{uu}P)/f_u^3\) satisfies \(\rho=r(v^2)\).
The corresponding companion-matrix expression has matrix trace zero;
interpreting its derivative inverse requires nonzero cubic discriminant
and \(\ell\ne0\).

For pairwise distinct \(x,y,z\), assuming \(\ell\ne0\) and the explicit
Vieta identities \(f_2=-\ell(x+y+z)\),
\(f_1=\ell(xy+xz+yz)\), the checked scalar identity gives
\[
r(x)+r(y)+r(z)=0,\qquad r(x)+r(y)=-r(z).
\]
Thus the complementary pair carries the negative third-sheet source.
These are exact source identities under the stated assumptions; they do
not construct a global splitting cover or a rational primitive. They narrow
the trace route but do not prove primitive existence.

Following the [PR #223 exploration](https://github.com/hodge-computer/sextics/pull/223#issuecomment-6712331048),
[CubicSelectorCancellation](CubicSelectorCancellation.lean) proves a local
moving-section identity. For \(q=(u-\beta)h\), \(g=h(\beta)\), and
\(f=q+(t^2-\alpha^2)H\), its cleared selector numerator satisfies
\(N=\alpha fS+(t^2-\alpha^2)R\), with explicit \(S,R\) and both moving-root
chain rules included. On \(f=0\), the density becomes \(2R/(g^2f_u)\),
cancelling the finite-section denominator under the stated nonvanishing
conditions. This does not prove an infinity correction, a traced-source
identity, or primitive existence.

## Exact negative source and regular contact

At \(\lambda=1\), let \(G=\texttt{weightedG}\) in coordinates
\((a,b,c,d,u)\) of weights \((1,1,1,1,2)\), and let \(S_6^-\)
be the weighted sextics odd under \((c,d)\mapsto(-c,-d)\).
[SymmetricNegativeSource](SymmetricNegativeSource.lean) enumerates its
60 monomials. [SymmetricNegativeJacobianIdeal](SymmetricNegativeJacobianIdeal.lean)
identifies the twelve independent Jacobian directions with the entire
intersection \(J(G)\cap S_6^-\), where \(J(G)\) uses all five partials. Thus
\[
\dim S_6^-=60,\qquad \dim(J(G)\cap S_6^-)=12,\qquad
\dim\bigl(S_6^-/(J(G)\cap S_6^-)\bigr)=48.
\]
Contact spanning remains a separate obligation from this dimension statement.

[ContactCubicExistence](ContactCubicExistence.lean) supplies a genuine root
\(x\in\mathbb C^{44}\) of the actual rational contact equations, with
bijective Jacobian. Exact finite row certificates and a certified contraction
prove existence in the specified dyadic-centered closed ball; no approximate
root is assumed.
[ContactCubicTargetBinding](ContactCubicTargetBinding.lean) binds those
equations to the exact norm identity
\[
G=F_1F_2+Q_2B_4+(C_++C_-)(C_+-C_-),
\]
where \(F_1=u+Q_1\),
\(F_2=u^2+(h_2-Q_1)u+h_4-h_2Q_1+Q_1^2\), and
\(G=u^3+h_2u^2+h_4u+h_6\). All factors use the certified root \(x\).
[ContactCubicAlgebraic](ContactCubicAlgebraic.lean) identifies the same
Jacobian with the formal Jacobian over \(\mathbb Q\). Its nonsingularity
proves each \(x_i\) algebraic and \(\mathbb Q(x_0,\ldots,x_{43})\)
finite-dimensional over \(\mathbb Q\).

[ContactCubicTangent](ContactCubicTangent.lean) then solves the linearized
norm identity with the \(a^2\)-coefficient of \(Q_1\) having velocity one.
The resulting \(\dot Q_1\) lies outside the scalar span of \(F_1,Q_2\),
giving a nontrivial first-order polynomial deformation. No integrated family
or contact-to-primitive comparison is supplied by these results.

## Classical existence of the relative primitive

The following argument uses the established
[weighted-threefold support theorem](../../docs/03b-weighted-threefolds.md)
and classical algebraic de Rham theory. These inputs are not yet Lean
theorems in this development. The contact computations above are supporting
results; the argument does not infer support from their ranks.

Put \(k=\mathbb Q(\lambda)\) and homogenize the actual equation and source:
\[
G_\lambda=a^6f(\lambda,b/a,c/a,d/a,u/a^2),\qquad
P_h=bd(a^2-u)(c^2-\lambda^2u).
\]
Both have weighted degree six. Choose \(\tau\in\mathbb C\) transcendental
over \(\mathbb Q\), embedding \(k\) by \(\lambda\mapsto\tau\).
Quasismoothness and avoidance of the weighted vertex hold on a nonempty
\(\mathbb Q\)-defined parameter open, since they hold at \(\lambda=1\).
Every excluded parameter is algebraic, so \(T_\tau=(G_\tau=0)\) is smooth
and geometrically integral. Write \(L_0=k(b,c,d)[u]/(f)\).

On the weighted ambient space with its isolated singular vertex removed,
let \(\Omega_w\) be contraction of
\(da\wedge db\wedge dc\wedge dd\wedge du\) by the weighted Euler field.
The weight-zero horizontal form \(2P_h\Omega_w/G_\tau^2\) has a global
residue class \(\eta\in H^3_{\mathrm{dR}}(T_\tau)\).
On \(a=1\), put \(\theta=db\wedge dc\wedge dd\). Direct differentiation gives
\[
\frac{2P}{f^2}\theta\wedge du
=d\left(\frac{2P}{ff_u}\theta\right)
 +\frac{2(f_uP_u-f_{uu}P)}{ff_u^2}\theta\wedge du.
\]
For the convention \(\operatorname{Res}(\theta\wedge df/f)=\theta\),
this identifies the actual residue with \(r\theta\), where
\(r=2(f_uP_u-f_{uu}P)/f_u^3\). It is therefore the restriction of a
global cohomology class, rather than an arbitrary rational three-form.

The involution \(\sigma:(c,d)\mapsto(-c,-d)\) preserves \(G,\Omega_w\)
and negates \(P_h\). Thus \(\eta\) lies in the negative sector supported
on a divisor by the weighted-threefold theorem. Restrict to a nonempty
affine principal open \(U\) outside that divisor, \(a=0\), and \(f_u=0\).
There \(r\theta\) has zero algebraic de Rham class.
[Grothendieck's comparison theorem and affine de Rham computation](https://www.numdam.org/item/PMIHES_1966__29__95_0.pdf)
give an algebraic two-form \(\beta\) on \(U\) with \(d\beta=r\theta\).
Since \(f_u\ne0\), the differentials \(db,dc,dd\) form a basis at the
function field. Writing \(\beta\) in that basis gives three rational
coefficients satisfying \(\sum_{j=b,c,d}E_j\beta_j=r\), with \(\tau\)
constant throughout.

To descend this primitive, write \(\beta_j=C_j/D\) with polynomials of
\(u\)-degree at most two. Clearing the differential equation gives
\[
f_u^2\sum_j\left[
 f_u(D\partial_jC_j-C_j\partial_jD)
 -f_j(D\partial_uC_j-C_j\partial_uD)\right]
 -2D^2(f_uP_u-f_{uu}P)=fQ.
\]
Fix finite monomial bounds containing these polynomials and invert one
nonzero coefficient of \(D\). This is a finite polynomial system over
\(\mathbb Q(\tau)\) with a complex solution. The weak Nullstellensatz
provides a solution over a finite extension \(k'/k\). Its denominator
remains nonzero because its \(u\)-degree is less than that of \(f\).
Geometric integrality makes \(L'=L_0\otimes_k k'\) a finite field extension
of \(L_0\). The canonical \(E_j\) kill \(k'\) and commute with trace, so
\[
\gamma_j=\frac{1}{[L':L_0]}
 \operatorname{Tr}_{L'/L_0}(C_j/D)
\quad\text{satisfies}\quad \sum_jE_j\gamma_j=r.
\]

Rename \(\tau\) back to the formal parameter \(\lambda\) before extending
constants from \(\mathbb Q\) to \(\mathbb C\); \(\lambda\) remains an
indeterminate. Pulling back by \(u=v^2\) into the actual chart field gives
exactly \(\sum E_j\gamma_j=\rho\), hence a `RelativePrimitive`.
The included [proved transport](SymmetricCertificateTransport.lean)
then gives mathematical certificate existence with homogeneous denominator
degree \(e\), numerator degrees \(e+1\), and the identity below.
A nonzero quotient has degree \(2e-6\). This proof is nonconstructive and
does not yet discharge the corresponding Lean admission.

## Conditional clearing and the certificate

Given such a primitive,
[WeightedPrimitiveTransport](WeightedPrimitiveTransport.lean) constructs the
four-component current \(w=(0,-g\beta_0,-g\beta_1,-g\beta_2)\).
The product rule gives its weighted-divergence equation, without requiring
the coefficients to be independent of \(\lambda\).
Canonical residue clearing then supplies affine polynomial data
\(D,N_v,N_\lambda,N_b,N_c,N_d,Q\), with \(D\ne0\),
\(\gcd(H,D)=1\), and
\[
A_HD^2-D\left(N_vH_v+\sum_jN_jH_j\right)
 +H\left(D\operatorname{div}N-N\cdot\nabla D\right)=H^2Q.
\]
The stronger normalized identities proved by `clear_relative_primitive`
are \(N\cdot\nabla H=A_HD\) and
\(D\operatorname{div}N-N\cdot\nabla D=HQ\); these imply the displayed
affine identity.

[SymmetricPiolaTransport](SymmetricPiolaTransport.lean) transports the
normalized equations through the six-coordinate inverse Jacobian.
[SymmetricChartField](SymmetricChartField.lean) implements the chart in
a rational function field, and
[SymmetricChartClearing](SymmetricChartClearing.lean) clears its common
denominator while preserving relative primality.
[SymmetricCertificateTransport](SymmetricCertificateTransport.lean) proves
`explicit_verify` for the resulting six homogeneous numerators and
denominator. Its `certificate_of_relative_primitive` is the final step
used by `Submission.certificate`. These four helpers are copied without
changes from `benediamond`'s
[PR #223](https://github.com/hodge-computer/sextics/pull/223) at commit
`21d3d74b8b60ded47e8ec9923c2869762b4e5d94`.

The final target requires transport back to the six original coordinates
and legal homogeneous data: a nonzero homogeneous denominator \(D\),
six numerators of degree \(\deg D+1\), coprimality with \(F\), and
\[
AD^2-D\sum_iN_iF_i
 +F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^2Q.
\]
The quotient \(Q\) is unrestricted. No expanded JSON witness is supplied.
[SymmetricRegularCurrent](SymmetricRegularCurrent.lean) proves that the
corresponding regular homogeneous current existence statement
`RegularGameExists` implies the literal protected target.

## Remaining Lean obligation

`Submission.relative_primitive_exists` must prove
`Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive` by formalizing
classical existence or constructing the primitive explicitly. Mathematical
existence follows from the stated geometric inputs; their formal
support-to-exactness comparison is still missing.
[ContactResidueAnnihilator](ContactResidueAnnihilator.lean) and
[WeightedFiberSmoothness](WeightedFiberSmoothness.lean) supply supporting
algebra and smoothness results for that formalization. This is the only
admission in the included certificate proof.

The dependent [PR #223](https://github.com/hodge-computer/sextics/pull/223)
also supplies an alternative residual endpoint. Its
[coefficient-field reduction](https://github.com/hodge-computer/sextics/blob/21d3d74b8b60ded47e8ec9923c2869762b4e5d94/data/symmetric-sextic-residual/SymmetricCoefficientField.lean)
makes primitive existence equivalent to a primitive for \(2\delta/f_u\),
where \(\delta\) is the divergence of its explicit coefficient field.
Its remaining admission is `Submission.residual_primitive_exists`.
The broader [five-component adapter](https://github.com/hodge-computer/sextics/blob/21d3d74b8b60ded47e8ec9923c2869762b4e5d94/data/symmetric-sextic-residual/SymmetricNormalTransport.lean)
also accepts a normal component and any nonzero coefficient-space polynomial
denominator, with unrestricted normal-variable dependence in the numerators.
Neither adapter constructs the missing primitive or a full current solution.
The Lean primitive-existence goal remains unproved in the combined stack,
and the exact protected theorem in this layer still depends on that one
admission.

The intended geometric argument follows the project's
[weighted-threefold and two-reflection construction](../../docs/03b-weighted-threefolds.md),
which adapts Voisin's curve-correspondence method. The algebraic reductions use
the maintained HodgeComputer and HoldoutCover constructions and Mathlib.
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
