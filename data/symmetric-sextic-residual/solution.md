# A relative primitive for the symmetric sextic

## Target and draft status

Put \(Q_X=X_0X_1+X_0X_2+X_1X_2\) and
\(Q_Y=Y_0Y_1+Y_0Y_2+Y_1Y_2\). The fixed target is
\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)
 +\frac57Q_X^2Q_Y+\frac{10}{7}Q_XQ_Y^2,
\qquad A=X_0X_1X_2Y_0Y_1Y_2,\qquad q=1.
\]
This is an **incomplete proof draft**. The algebra below reduces the target to a relative rational primitive. Its finite projective transport is now proved, including denominator legality. The one unfinished lemma in [Solution](Solution.lean) is identified below; `Submission.certificate` is not a verified certificate.

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

[CubicTrace](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/CubicTrace.lean) proves an exact companion-matrix
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
Over the étale open, the unordered-pair cover is canonically the original cubic cover via the remaining root. Its transfer is \(\operatorname{Tr}-\mathrm{id}\), hence acts by \(-1\) on trace-zero elements. This is a self-correspondence, so the complementary-pair identity does not itself provide a new supporting variety. These are exact source identities under the stated assumptions; they do not construct a rational primitive or establish the primitive-existence obligation below.

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
In fact `clear_relative_primitive` supplies the stronger normalized identities
\[
N\cdot\nabla H=A_HD,\qquad
D\operatorname{div}N-N\cdot\nabla D=HQ.
\]
Thus the rational affine field \(w=N/D\) satisfies \(w(H)=A_H\) and \(\operatorname{div}w=HQ/D^2\).

### Explicit transport to the original coordinates

Put \(U=X_0+X_1\), \(S=X_0-X_1\), and \(T=Y_0-Y_1\). The inverse chart is
\[
a=U/2,\qquad
(\lambda,b,c,d,v)=\left(T/S,2X_2/U,(Y_0+Y_1)/U,2Y_2/U,S/U\right).
\]
[SymmetricPiolaTransport](SymmetricPiolaTransport.lean) gives the inverse Jacobian and pushes forward the chart field with radial component zero and remaining components \(w/(4v)\). The resulting original-coordinate field \(V\) satisfies
\[
V(F)=A,\qquad
\operatorname{div}V=F\frac{Q}{4a^6vD^2}.
\]
The factor \(1/(4v)\) is required: the six-dimensional Piola input is \((0,a^5w)\), whose Jacobian denominator is \(4a^5v\). [SymmetricChartField](SymmetricChartField.lean) instantiates the coordinate derivations on the actual ambient fraction field and binds the calculation to the protected \(F,A\).

Choose \(L\ge5\) at least as large as the total degrees of all the affine data. For any such polynomial \(p\), put
\[
\widehat p=(US)^L p\left(T/S,2X_2/U,(Y_0+Y_1)/U,2Y_2/U,S/U\right).
\]
This is a finite polynomial, homogeneous of degree \(2L\), because all five inverse chart coordinates have common denominator \(US\) and homogeneous quadratic numerators. [CommonDenominatorSubstitution](../../formal/lean/HodgeComputer/Constructions/RationalFields/CommonDenominatorSubstitution.lean) proves this generic clearing identity. [SymmetricChartClearing](SymmetricChartClearing.lean) proves legality for the actual chart: an alleged \(F\)-divisibility of \(\widehat D\) pulls back at \(a=1\) to \(H\mid(4v)^LD\), contradicting primality of \(H\), \(H\nmid v\), and \(\gcd(H,D)=1\).

The original denominator and numerators are explicitly
\[
\begin{aligned}
D_0&=8S^2\widehat D,\\
M_0&=U^2S\widehat N_v,&M_1&=-M_0,&M_2&=U^2S\widehat N_b,\\
M_3&=US^2\widehat N_\lambda+U^2S\widehat N_c+U^2T\widehat N_v,\\
M_4&=-US^2\widehat N_\lambda+U^2S\widehat N_c-U^2T\widehat N_v,\\
M_5&=U^2S\widehat N_d.
\end{aligned}
\]
With \(Q_0=1024U^{L-5}S^{L+3}\widehat Q\), [SymmetricCertificateTransport](SymmetricCertificateTransport.lean) proves
\[
M\cdot\nabla F=AD_0,\qquad
D_0\operatorname{div}M-M\cdot\nabla D_0=FQ_0.
\]
The common denominator is nonzero, relatively prime to \(F\), and homogeneous of degree \(2L+2\); all six displayed numerators are homogeneous of degree \(2L+3\). The theorem `explicit_verify` proves that these precise polynomials satisfy the unchanged verifier, without replacing the denominator through a later normalization. Consequently `certificate_of_relative_primitive`, and the corresponding `Submission.regular_game_of_relative_primitive`, have no admitted hypotheses or proof terms beyond their displayed primitive input. No expanded JSON witness is supplied because that primitive has not been constructed.

## Remaining proof obligation

`Submission.relative_primitive_exists` must prove `Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive`. The intended geometric route identifies the actual contact correspondence with the relevant cohomology map and proves support-to-function-field exactness. Contact identities and a finite rank calculation alone do not supply this implication. [ContactResidueAnnihilator](ContactResidueAnnihilator.lean) and [WeightedFiberSmoothness](WeightedFiberSmoothness.lean) provide supporting algebra and smoothness results, not primitive existence.

This primitive is relative over \(\mathbb C(\lambda)\): its equation uses only \(E_b,E_c,E_d\). A global primitive involving a \(\lambda\)-component would not by itself meet that endpoint. The book's weighted-fiber support argument supplies the appropriate mathematical route: spread the anti-projector's supporting divisor over a finite base extension, identify the exact residue density, and obtain relative de Rham exactness on the function field. Finite trace can then descend the primitive. Those geometric comparisons remain unformalized here.

The sole remaining lemma is admitted. The final theorem therefore still depends on `sorryAx` and does not establish the protected certificate independently. The proved transport and coordinate identities depend only on Lean's usual logical axioms.

The intended geometric argument follows the project's
[weighted-threefold and two-reflection construction](../../docs/03b-weighted-threefolds.md),
which adapts Voisin's curve-correspondence method. The algebraic reductions use
the maintained HodgeComputer and HoldoutCover constructions and Mathlib.
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
