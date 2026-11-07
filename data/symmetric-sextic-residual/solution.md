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
to a relative rational primitive and a final transport step. This layer's
[Solution](Solution.lean) retains two admitted lemmas; its
`Submission.certificate` is not a verified certificate. The status below
also records the transport proved in the dependent PR #223.

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
the trace route but close neither of the two proof obligations below.

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
This is the conclusion of `clear_relative_primitive`; it is an affine result.

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

## Unfinished proof obligations

1. `Submission.relative_primitive_exists` must prove
   `Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive`. The intended
   geometric route identifies the actual contact correspondence with the
   relevant cohomology map and proves support-to-function-field exactness.
   Contact identities and a finite rank calculation alone do not supply this
   implication. [ContactResidueAnnihilator](ContactResidueAnnihilator.lean)
   and [WeightedFiberSmoothness](WeightedFiberSmoothness.lean) provide
   supporting algebra and smoothness results, not primitive existence.
2. This layer's `Submission.regular_game_of_relative_primitive` must turn that primitive
   into `SymmetricRegularCurrent.RegularGameExists`, completing the
   affine-to-homogeneous transport. The chart and Jacobian identities do not
   themselves discharge this step.

Both lemmas remain admitted in this layer. The dependent
[PR #223](https://github.com/hodge-computer/sextics/pull/223), at
`21d3d74b8b60ded47e8ec9923c2869762b4e5d94`, proves
[primitive-to-certificate transport](https://github.com/hodge-computer/sextics/blob/21d3d74b8b60ded47e8ec9923c2869762b4e5d94/data/symmetric-sextic-residual/SymmetricCertificateTransport.lean),
closing the second gap in that combined stack. Its
[coefficient-field reduction](https://github.com/hodge-computer/sextics/blob/21d3d74b8b60ded47e8ec9923c2869762b4e5d94/data/symmetric-sextic-residual/SymmetricCoefficientField.lean)
makes primitive existence equivalent to a primitive for \(2\delta/f_u\),
where \(\delta\) is the divergence of its explicit coefficient field.
Its remaining admission is `Submission.residual_primitive_exists`.
The broader [five-component adapter](https://github.com/hodge-computer/sextics/blob/21d3d74b8b60ded47e8ec9923c2869762b4e5d94/data/symmetric-sextic-residual/SymmetricNormalTransport.lean)
also accepts a normal component and any nonzero coefficient-space polynomial
denominator, with unrestricted normal-variable dependence in the numerators.
Neither adapter constructs the missing primitive or a full current solution.
The Lean primitive-existence goal remains unproved in the combined stack, and this layer's
unchanged final theorem still depends on its two admissions.

The intended geometric argument follows the project's
[weighted-threefold and two-reflection construction](../../docs/03b-weighted-threefolds.md),
which adapts Voisin's curve-correspondence method. The algebraic reductions use
the maintained HodgeComputer and HoldoutCover constructions and Mathlib.
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
