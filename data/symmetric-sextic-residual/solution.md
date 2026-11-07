# Reflection-chart reductions for the symmetric sextic

## Target and draft status

Put \(Q_X=X_0X_1+X_0X_2+X_1X_2\) and
\(Q_Y=Y_0Y_1+Y_0Y_2+Y_1Y_2\). The fixed target is
\[
F=\sum_{i=0}^2(X_i^6+Y_i^6)
 +\frac57Q_X^2Q_Y+\frac{10}{7}Q_XQ_Y^2,
\qquad A=X_0X_1X_2Y_0Y_1Y_2,\qquad q=1.
\]
This is an **incomplete proof draft**. The algebra below gives a relative-primitive route and a full affine-current route, with proved projective transports and denominator legality. The full current has a complete polynomial normal form in the variable \(u\), with unrestricted rational coefficients in \((\lambda,b,c,d)\). The one unfinished lemma in [Solution](Solution.lean) belongs to the relative route; `Submission.certificate` is not a verified certificate.

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

## An explicit coefficient field reduces the pole

Write \(f=\ell u^3+f_2u^2+f_1u+f_0\) and
\(P=p_0+p_1u+p_2u^2\), and set
\[
M=\frac{\partial(f_0,f_1,f_2)}{\partial(b,c,d)},\qquad
J=\det M,\qquad Z=\operatorname{adj}(M)(p_0,p_1,p_2)^{\mathsf T},
\qquad W=Z/J.
\]
[SymmetricCoefficientField](SymmetricCoefficientField.lean) defines all these polynomials from the actual equation and source. The adjugate identity proves \(W(f)=P\), and normal independence gives \(W(f_u)=P_u\). The denominator is nonzero in \(K\): at \((\lambda,b,c,d)=(0,1,1,2)\), it specializes to \(-564000/49\), while \(H\) remains a degree-six polynomial in \(v\). Thus \(H\) cannot divide \(J\).

Put \(\delta=\partial_bW_b+\partial_cW_c+\partial_dW_d\). The quotient rule gives the exact identity
\[
\sum_{j=b,c,d}E_j\left(-\frac{2W_j}{f_u}\right)
=\rho-\frac{2\delta}{f_u}.
\]
All expressions here are evaluated at \(u=v^2\). The general identity is proved in [CoefficientReduction](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/CoefficientReduction.lean), and [SymmetricCoefficientReduction](SymmetricCoefficientReduction.lean) binds its tangent derivations to this function field.

Consequently the original relative-primitive problem is **equivalent** to
\[
\sum_{j=b,c,d}E_j\gamma_j=\frac{2\delta}{f_u},\qquad \gamma_j\in K.
\]
The theorem `primitive_iff_residual` proves both directions without restricting the poles of \(\gamma\). The original primitive is explicitly \(\beta_j=-2W_j/f_u+\gamma_j\), and `certificate_of_residual` constructs the protected certificate from such a \(\gamma\). This removes the explicit third-order normal denominator from the remaining source, while allowing poles along the coefficient Jacobian. It does not prove existence of the remaining primitive.

## The full affine current and its polynomial normal form

Put \(E=\mathbb C(\lambda,b,c,d)\). A full current has four coefficient components \(W\) and a normal component \(V\partial_u\). Its ordinary equation is
\[
W(f)+Vf_u-f\bigl(\operatorname{div}_{\lambda,b,c,d}W+V_u\bigr)=P.
\]
The ordinary divergence here is essential. The physical chart has volume factor \(4a^5v\); changing to \(u=v^2\) gives \(2a^5\). There is no remaining weight in the five affine coordinates.

The book's [polynomial normal-form theorem](https://github.com/hodge-computer/sextics/blob/4865499f5418a6c73d71539acfd4d27b618533f1/docs/05-computation.md#a-polynomial-normal-form-in-one-variable), presented in the independent [book PR 224](https://github.com/hodge-computer/sextics/pull/224), shows that every legal rational current for this equation, including one whose defect is only divisible by \(f^2\), can be replaced by
\[
W=W_0+uW_1+u^2W_2,\qquad
V=v_0+uv_1+u^2v_2,
\qquad W_i\in E^4,\quad v_i\in E,
\]
with an exact identity. This degree bound is complete, rather than a chosen search cutoff. It follows by reducing all five components modulo the cubic: the change \(fT\) contributes only \(-f^2\operatorname{div}T\), while the reduced defect has degree at most five. The general positive-pole-order statement is proved in [NormalRemainder](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/NormalRemainder.lean), including inversion of the original denominator modulo the required power of \(f\).

For this target, simultaneous interchange of \(X_0,X_1\) and \(Y_0,Y_1\) preserves \(F,A\). Averaging a homogeneous certificate under that symmetry, descending through \(u=v^2\), and cancelling the radial component places it in the ordinary affine equation above. These geometric coordinate comparisons give a mathematical equivalence with the full certificate problem; their necessity direction has not yet been composed into a Lean theorem. The complete form has fifteen rational coefficient functions. Its three normal coefficients can be eliminated algebraically, leaving three first-order linear differential equations for the twelve coefficient components. Rational dependence on the four remaining coordinates is still unrestricted, and no solution of that system has been supplied.

The constructive direction is already available in [SymmetricNormalTransport](SymmetricNormalTransport.lean). Write \(W=Z/D\), \(V=N_u/D\), where \(D\ne0\) is any polynomial in the four coefficient coordinates. The theorem `certificate_of_weighted_game` constructs the protected certificate from the cleared ordinary identity. It uses the reflected numerator
\[
\bigl(4vZ_\lambda,4vZ_b,4vZ_c,4vZ_d,2N_u\bigr)\big|_{u=v^2}
\]
over \(D\), then the existing homogeneous transport. All five components are retained, denominator legality is automatic, and the resulting quotient is zero. The polynomial coefficient identities and remaining differential system are recorded in the PR research discussion.

### The subsystem with zero normal component

[SymmetricBalancedTransport](SymmetricBalancedTransport.lean) supplies a separate endpoint that permits a nonzero \(\lambda\)-component. Seek a rational field
\[
W=W_\lambda\partial_\lambda+W_b\partial_b+W_c\partial_c+W_d\partial_d
\]
and a rational function \(h\) satisfying
\[
W(f)=P+hf,\qquad \operatorname{div}W=h.
\]
These are sufficient identities in the ambient weighted coordinate field. Their coefficients may depend on \(u\), although this subsystem has no \(\partial_u\)-component. They do not have to be interpreted as a three-component relative primitive. In particular, the \(\lambda\)-component is retained throughout the proof.

Write \(W=Z/D\) and \(h=H_0/D\). The exact polynomial obligations are
\[
\sum_{i=\lambda,b,c,d}Z_i\partial_i f=DP+H_0f,
\qquad
D\sum_i\partial_iZ_i-\sum_iZ_i\partial_iD=DH_0.
\]
The theorem `certificate_of_base_coefficients` proves the protected certificate from these two identities and any nonzero polynomial denominator \(D\) in \((\lambda,b,c,d)\). The numerators \(Z_i,H_0\) may depend polynomially on \(u\). The denominator is not restricted to the earlier determinant \(J\). Extra coefficient-space divisors are allowed. Their legality is proved uniformly: the irreducible chart equation depends on \(v\), so it cannot divide a nonzero polynomial independent of \(v\). The existing homogeneous transport then proves legality in the original coordinates.

The direct affine current is
\[
w=4v\,(W_\lambda,W_b,W_c,W_d,0)|_{u=v^2}.
\]
It satisfies the ordinary affine game
\[
A_H-w(H)+H\operatorname{div}w=0.
\]
Its physical pushforward is
\[
V=(0,0,aW_b,a(W_c+vW_\lambda),a(W_c-vW_\lambda),aW_d)|_{u=v^2},
\]
which satisfies \(V(F)=A+hF\) and \(\operatorname{div}V=h\). The theorem `ordinary_current_transport` proves the underlying contraction and divergence formulas, and `explicit_verify_game` proves a literal homogeneous certificate with \(Q=0\) after the displayed chart clearing below. This construction needs no intermediate exact-normalization hypothesis. If a normalized field is desired, the general [radial-normalization theorem](../../formal/lean/HodgeComputer/Constructions/RationalFields/RadialNormalization.lean) applies while retaining the denominator and zero quotient.

### The scalar correction and its exact obstruction

The reusable [CoefficientBalance](../../formal/lean/HodgeComputer/Constructions/ResidueTransport/CoefficientBalance.lean) module makes one scalar reduction precise. Suppose a base field \(W_0\) and a correction direction \(C\) satisfy
\[
W_0(f)=P,\qquad C(f)=\alpha f,\qquad
C(\ell)=\alpha\ell,\qquad \operatorname{div}C=4\alpha,
\qquad \ell\ne0.
\]
Then
\[
W=W_0+\frac{s}{\ell^3}C,\qquad h=\frac{\alpha s}{\ell^3}
\]
has the required matching automatically, and its divergence is balanced **if and only if**
\[
C(s)=-\ell^3\operatorname{div}W_0.
\]
The generic theorem works for any number of coordinates and any exponent \(r\), with \(\operatorname{div}C=(r+1)\alpha\). It does not assert that the scalar equation has a rational solution. `certificate_of_scalar_correction` combines this reduction with the exact target transport, assuming the displayed identities and a common-denominator representation. Only nonvanishing and independence of the normal variable are required of that denominator; its degree and extra base divisors are unrestricted.

For the explicit \(u\)-independent coefficient-fiber direction fixing \(f_0/\ell,f_1/\ell,f_2/\ell\), the scalar equation has no rational solution. A [nonzero local contour period](https://github.com/hodge-computer/sextics/pull/223#issuecomment-6711115729) proves this for every rational denominator, including arbitrary extra invariant divisors. The argument excludes the whole \(u\)-independent four-component ansatz. It does not exclude \(u\)-dependent coefficient components, a normal component, or the original relative primitive. The full polynomial form above retains precisely those additional freedoms. The conditional Lean balance theorem remains general; the period obstruction and its exact computation are recorded separately in the PR discussion.

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

`Submission.residual_primitive_exists` must construct a primitive for the explicit density \(2\delta/f_u\). The checked equivalence above then proves `Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive`. The intended geometric route identifies the actual contact correspondence with the relevant cohomology map and proves support-to-function-field exactness. Contact identities and a finite rank calculation alone do not supply this implication. [ContactResidueAnnihilator](ContactResidueAnnihilator.lean) and [WeightedFiberSmoothness](WeightedFiberSmoothness.lean) provide supporting algebra and smoothness results, not primitive existence.

This primitive is relative over \(\mathbb C(\lambda)\): its equation uses only \(E_b,E_c,E_d\). A global primitive involving a \(\lambda\)-component would not by itself meet that endpoint. The full ordinary-current construction above has its own independently proved endpoint and can be used if its complete coefficient system is solved. The book's weighted-fiber support argument supplies a mathematical route to the original relative primitive: spread the anti-projector's supporting divisor over a finite base extension, identify the exact residue density, and obtain relative de Rham exactness on the function field. Finite trace can then descend the primitive. Those geometric comparisons remain unformalized here.

The sole remaining lemma is admitted. The final theorem therefore still depends on `sorryAx` and does not establish the protected certificate independently. The proved transport and coordinate identities depend only on Lean's usual logical axioms.

The intended geometric argument follows the project's
[weighted-threefold and two-reflection construction](../../docs/03b-weighted-threefolds.md),
which adapts Voisin's curve-correspondence method. The algebraic reductions use
the maintained HodgeComputer and HoldoutCover constructions and Mathlib.
Prepared for `fqlx` with OpenAI ChatGPT and Codex assistance.
