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

## Normalized selector and the conditional trace endpoint

Set \(b=r,\ c=t,\ d=st,\ x=t^2\), holding \(\lambda\) fixed, and write

\[
f(x,u)=\ell u^3+B(x)u^2+C(x)u+D(x).
\]

For a moving point \((\alpha,\beta_*)\) with
\(f(\alpha^2,\beta_*)=0\), put
\[
q_\alpha(u)=\frac{f(\alpha^2,u)}{u-\beta_*},\qquad
h_\alpha=q_\alpha-\frac13f_u(\alpha^2,u),\qquad
\Theta=\frac{h_\alpha}{f_u(x,u)}
 \bigl(d\log(t-\alpha)-d\log(t+\alpha)\bigr).
\]
The subtraction makes \(h_\alpha\) linear in \(u\).
On the distinct-sheet open with \(\alpha\ne0\), the logarithmic residues
at \(t=\alpha\) are \(2/3\) on the selected sheet and \(-1/3\) on each
other sheet; the signs reverse at \(t=-\alpha\).
[CubicSelectorCurrent](CubicSelectorCurrent.lean) proves the paired-current
divergence formula, its full chain rule, and local cancellation identities.
These apply to \(\eta\wedge\Theta\) when \(\eta=U\,dr+V\,ds\) is closed
and the stated coordinate and derivation hypotheses hold.

[CubicSourceReconstruction](CubicSourceReconstruction.lean) proves the exact
companion-matrix trace test and source reconstruction. For a reduced numerator
\(C_0+C_1u+C_2u^2\), nonzero discriminant and \(\ell\ne0\) give the
trace-zero condition
\[
3\ell C_0-BC_1+CC_2=0.
\]
Under this condition, \(S=S_0+S_1u\), with
\(S_0=-C_1/(6\ell)\) and \(S_1=-C_2/(3\ell)\), satisfies
\[
f_uS_u-f_{uu}S=C_0+C_1u+C_2u^2.
\]
For the proposed normalized contact current, the written polynomial argument
gives \(\deg_xS_0\le3\), \(\deg_xS_1\le2\).
[CubicSelectorSource](CubicSelectorSource.lean) now proves these bounds for
its explicit source polynomials, given divided-difference and motion
coefficient degrees \((2,1,0)\). Its evaluation theorems bind those
polynomials to the scalar source formula. The bounds concern the formal
fibre variable \(x\); they do not bound rational \(r,s\) denominators or
establish a global weighted-sextic source.

[CubicTraceDescent](CubicTraceDescent.lean) proves descent of a supplied
current through finite normalized trace. The target-bound
[SymmetricTraceEndpoint](SymmetricTraceEndpoint.lean) defines two functions
directly in the actual chart field \(K\):
\[
\kappa=\frac{p_2}{3\ell},\qquad
T_1=P_u-\kappa f_{uu},\qquad
T_0=P-\kappa f_u-T_1u,
\]
with every expression evaluated at \(u=v^2\). It proves \(\ell\ne0\) there
and the literal density identity
\[
\rho=\frac{2\bigl(f_uT_1-f_{uu}(T_0+T_1u)\bigr)}{f_u^3}.
\]
The endpoint treats \(T_0,T_1\) as elements of \(K\); no separate
coefficient-subfield membership is asserted.
For a finite extension \(L/K\), let \(\widetilde E_j\) extend
\(E_b,E_c,E_d\) compatibly. A supplied upstairs current must satisfy
\[
\sum_{j=1}^3\widetilde E_j(w_j)
 =\frac{2\bigl(f_us_1-f_{uu}(s_0+s_1u)\bigr)}{f_u^3},
\qquad w_j,s_0,s_1\in L,
\]
with the base quantities mapped to \(L\). The two exact conditions
\[
\overline{\operatorname{Tr}}_{L/K}(s_0)=T_0,\qquad
\overline{\operatorname{Tr}}_{L/K}(s_1)=T_1,
\qquad
\overline{\operatorname{Tr}}_{L/K}
 =\frac{1}{[L:K]}\operatorname{Tr}_{L/K}
\]
let `relativePrimitiveOfTrace` construct the existing `RelativePrimitive`
by tracing the three current components.

The same descent module also proves a relative bridge from the ordinary game
\[
\sum_{j=b,c,d}W_jf_j+Vf_u
 -f\left(\sum_{j=b,c,d}\partial_jW_j+\partial_uV\right)=P:
\qquad \beta_j=\left.-\frac{2W_j}{f_u}\right|_{u=v^2}.
\]
It retains the normal component \(V\) and normal dependence of every \(W_j\).
The actual field, a family of closed forms, and the selector jet bindings
are constructed below. Applying this route still requires choosing a
form with the two full normalized source-trace matches.
A single branch or the rank-48 contact span supplies none of these equalities.
These trace modules contain no admissions; they leave the one existing
primitive-existence admission unchanged.

### The explicit selector source and its chart transport

[CubicSelectorSource](CubicSelectorSource.lean) computes the source of the
closed paired current, rather than assuming a source for an unnamed
current. At the moving point, write \(z=u-\beta_*\) and

\[
f(\alpha^2,u)=\ell z^3+az^2+gz,\qquad
f(x,u)=f(\alpha^2,u)+(x-\alpha^2)H(x,u),\qquad
q=\frac{az+2g}{3}.
\]

Let \(D=U\partial_s-V\partial_r\), \(Z=D\alpha\), and put
\(A=2xZf_x+\alpha Df\). The differentiated current numerator is

\[
N=(f_uq_u-qf_{uu})A+f_uqA_u-\alpha f_u^2Dq.
\]

The definitions `sourceZeroNumerator` and `sourceOneNumerator` give
explicit polynomial expressions \(n_0,n_1\) in the moving-point jets and
the coefficients of \(H\) and its motion. The checked identity is

\[
18\ell^2N=(x-\alpha^2)
 \left[f_u(2n_1)-f_{uu}(n_0+2n_1z)\right]+fQ,
\]

with an explicit polynomial \(Q\). Thus
\(S_0=n_0/(18\ell^2)\), \(S_1=n_1/(9\ell^2)\) give the entire density
on \(f=0\). `current_density` proves that the explicit paired current
has this density when the one-form is closed and the moving-point jet
chain rules hold. More precisely, for
\(Y=tZ T+\alpha(U S-V R)\), these rules are

\[
Y(q)=\alpha D_{\mathrm{coeff}}q-\frac{q_uA}{f_u},
\qquad Y(f_u)=A_u-\frac{f_{uu}A}{f_u}.
\]

Here \(D_{\mathrm{coeff}}\) holds \(x,u\) fixed and includes the moving
\(\alpha,\beta_*\) coefficients. Its source in the original normal coordinate is

\[
S_0+S_1(u-\beta_*)=(S_0-\beta_*S_1)+S_1u.
\]

The constant coefficient must therefore be unshifted **before** tracing;
the trace of \(\beta_*S_1\) is not replaced by a product of traces.

[SymmetricRatioCurrent](SymmetricRatioCurrent.lean) binds the ratio
coordinates and their canonical derivations to the actual chart field.
Writing \(B=E_b,C=E_c,D=E_d,t=c\), it proves \(t\ne0\) and constructs

\[
T=C+\frac dtD,\qquad R=B,\qquad S=tD.
\]

The required commutation and coordinate identities also hold for their
canonical finite extensions. The volume change
\(db\wedge dc\wedge dd=-t\,dt\wedge dr\wedge ds\) gives the cofactor map

\[
(w_t,w_r,w_s)\longmapsto
 \left(-\frac{w_r}{t},-\frac{w_t}{t},-\frac{d\,w_t}{t^2}-w_s\right),
\qquad
\sum E_j\gamma_j=-\frac{Tw_t+Rw_r+Sw_s}{t}.
\]

Consequently `relativePrimitiveOfClosedSelector` constructs the existing
`RelativePrimitive` from supplied closed moving-point data and the exact
normalized-trace identities

\[
\overline{\operatorname{Tr}}(S_0-\beta_*S_1)=-tT_0,
\qquad \overline{\operatorname{Tr}}(S_1)=-tT_1.
\]

These selector and ratio helpers contain no admissions. The actual
closed-form and jet construction below discharges their differential
hypotheses. The two trace identities and the protected primitive-existence
theorem remain unproved.

### A finite moving-point field in the actual chart

[SymmetricRatioCurrent](SymmetricRatioCurrent.lean) also proves that the
integral parameter ring \(\mathbb Z[\lambda,r,s]\) embeds in the actual
chart field \(K\), by its coordinate derivations. The time derivative
\(T\) kills this ring.

[SymmetricContactField](SymmetricContactField.lean) constructs a finite
separable extension \(L/K\) containing a norm contact and a moving point.
The underlying 73-variable incidence has 70 coefficient corrections, a contact parameter
\(\tau\), and the point coordinates \(\alpha,\beta_*\). The six
contact forms have coefficients

\[
z_j=c_j+v_j\tau+(E x)_j,
\]

where \(c,v\) are explicit balanced integral lifts of the maintained
norm-contact seed and tangent, and \(E\) selects its 70 pivot columns.
The first 70 equations are every coefficient of \(7\Phi(z)-7G_\lambda\).
The other three are

\[
f_1(1,r,\alpha,s\alpha,\beta_*)=
f_2(1,r,\alpha,s\alpha,\beta_*)=
(A+B)(1,r,\alpha,s\alpha,\beta_*)=0.
\]

At \((\lambda,r,s)=(1,3,13)\) modulo 37, the explicit seed
\((x,\tau,\alpha,\beta_*)=(0,0,27,4)\) solves all 73 equations.
Sparse integer arithmetic and an explicit inverse matrix prove that its
Jacobian is invertible over \(\mathbb F_{37}\). The maintained
`square_system_generic_lift`, together with the injective parameter map,
supplies the finite separable field factor. The modular seed itself is
not asserted to solve the characteristic-zero equations.

The chosen factor also retains two explicit nonvanishing conditions.
The 70-by-70 coefficient minor is a unit at the seed: the first 70 rows
of the seed Jacobian have zero \(\tau,\alpha,\beta_*\) columns, so its
invertibility follows from that of the full Jacobian. The ambient point
minor, with columns \(r,\alpha,\beta_*\), is

\[
\begin{pmatrix}23&14&34\\27&15&14\\24&24&12\end{pmatrix},
\qquad \det=8\pmod{37}.
\]

Flattening the parameter and unknown polynomial rings proves that this
is the actual derivative matrix of the three point equations. Put
\(q\) equal to the product of these two symbolic minors. The field is
constructed from the **74-variable** system consisting of the original
73 equations and \(qz-1=0\). Its seed Jacobian is block triangular and
invertible. Every field factor of this augmented incidence therefore
retains both minors as units; their characteristic-zero nonvanishing is
not inferred from the modular seed alone.

`norm_identity` proves the full polynomial identity for the unchanged
weighted sextic. The three point equations therefore imply

\[
f(\lambda,r,\alpha,s\alpha,\beta_*)=0
\]

in \(L\); this is `movingEvaluation_equation`. Differentiating the
square system with the canonical extension of \(T\) and using its
invertible Jacobian proves that every incidence coordinate is constant
in that direction. In particular \(T\alpha=T\beta_*=0\). Since
\(Tt=1\), the equation \(t^2-\alpha^2=0\) would imply \(2t=0\),
contradicting \(t\ne0\). Thus `movingSection_nonzero` establishes the
selector's section denominator in this actual extension.

### Closed contact forms and actual selector jets

The first 70 incidence equations depend only on \(\lambda\) among the
base parameters and only on the 71 contact coefficients among the unknowns.
The full nonsingular 73-variable Jacobian therefore makes the contact
block a surjective map \(L^{71}\to L^{70}\). Its kernel has dimension
one. The two vectors of relative derivatives of the contact coordinates
lie in this kernel, so all their two-by-two minors vanish. This proves
closedness from the kernel condition in the selected field factor.

Let \(E\subset L\) be the subfield generated by \(\lambda\) and all
71 contact coordinates, including \(\tau\). For every \(H\in E\), set

\[
\eta_H=H\,d\tau=U\,dr+V\,ds,
\qquad U=H R\tau,\quad V=H S\tau.
\]

The wedge identities extend from the generators to the entire subfield,
including inverses. Commutation of \(R,S\) gives \(RV=SU\).
Time differentiation kills \(E\), so \(TU=TV=0\) as well. These are
`contact_form_closed` and `contact_form_time_zero`. They construct a
family of actual closed forms; they do not yet choose the form needed for
the target or assert holomorphy. The additional minors give a stronger
nonvanishing statement below.

The nonvanishing of the coefficient minor gives the exact implicit chain
rule. Write \(A_c\) for that 70-by-70 matrix and \(b_c\) for the
\(\tau\) column, and put \(v=-A_c^{-1}b_c\). For every derivation
\(D\) killing \(\lambda\),

\[
D x_i=v_i D\tau.
\]

If \(R\tau=0\), all contact-coordinate derivatives in the \(r\)
direction would vanish. Differentiating the three point equations would
then put \((1,R\alpha,R\beta_*)\) in the kernel of the invertible
ambient point matrix, a contradiction. Thus `movingR_tau_nonzero`
proves \(R\tau\ne0\). Consequently \(H\ne0\) implies
\(U=H R\tau\ne0\). The normalized contact derivative

\[
\partial_\tau=(R\tau)^{-1}R
\]

satisfies \(\partial_\tau\tau=1\) and
\(\partial_\tau x_i=v_i\). These statements concern the actual lifted
field and its chosen contact parameter.

The actual ratio pencil has the shape

\[
f(x,u)=\ell u^3+B(x)u^2+C(x)u+D(x),
\qquad \deg B\le1,\quad\deg C\le2,\quad\deg D\le3.
\]

`pencilJet` in [CubicSelectorSource](CubicSelectorSource.lean) constructs
its complete shifted jet. At \(x=\alpha^2\), its two coefficients are
\(a=3\ell\beta_*+B(\alpha^2)\) and
\(g=f_u(\alpha^2,\beta_*)\). Its \(h_i\) are the literal polynomial
divided differences, and its \(k_i\) include all derivatives of the
moving point. `pencilJet_chain_rules` derives both selector chain rules
by differentiating the physical equation and the moving-point equation.
It does not assume those rules for an unnamed jet.

`actual_jet_chain_rules` binds this construction to the unchanged
`rawWeighted`, the actual field normal derivative and its second normal
derivative, and the proved moving point. Consequently
`relativePrimitiveOfCurveSource` takes only \(H\in E\) and the two
normalized source-trace equalities as inputs; it supplies every other
field, closedness, jet, and denominator hypothesis internally.
The selector source is linear in the contact motion: writing its two
source coefficients at \(H=1\) as \(A_0,A_1\), the new identities
`curveSourceZero_weight` and `curveSourceOne_weight` express the required
matches as \(\operatorname{nTr}(HA_0)=-tT_0\) and
\(\operatorname{nTr}(HA_1)=-tT_1\). The multiplier must still lie in
the contact subfield \(E\), which ensures the resulting form is closed.

No \(H\) satisfying those two equalities has yet been constructed.
The trace comparison, including any necessary correspondence inversion
and differential correction, remains necessary to remove
`Submission.relative_primitive_exists`'s admission.

An independent reduction in [SymmetricRatioCurrent](SymmetricRatioCurrent.lean)
uses the subfield \(K_0\) generated by the complex constants and
\(\lambda^2,b,d/c,c^2,v^2\). The actual chart field is finite over \(K_0\),
and the ratio derivatives \(D_r,D_s,D_x\), with \(x=c^2\), preserve it.
The theorem `SquarePrimitive.primitive_iff_square_equation` proves that the
missing primitive exists exactly when there are \(a,b_0,c_0\in K_0\) with
\[
D_r a+D_s b_0+c_0+2xD_xc_0=c\,\rho.
\]
The forward direction descends by normalized finite trace; the reverse
direction constructs the chart current explicitly. This equivalence does not
provide a solution of the displayed equation.

The same helper proves a first exact pole reduction for the actual cubic
\(f(x,u)\). Put \(r=b\), \(s=d/c\), and
\(Q=rs(1-u)(x-\lambda^2u)\). With \(C_0=-Q/(f_xf_u)\),
`HermiteBinding.actual_hermite_decomposition` proves
\[
c\rho=C_0+2xD_xC_0+
\frac{2x(Q_xf_x-Qf_{xx})+Qf_x}{f_x^2f_u}.
\]
The proof establishes that both \(f_x\) and \(f_u\) are nonzero in the
actual chart field. Thus `primitive_iff_hermite_remainder` replaces the
original source by the displayed lower-pole remainder, but still requires
three rational functions solving its differential equation.

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

## Exact base-coordinate trace targets

`SymmetricTraceCoefficients` in [SymmetricTraceEndpoint](SymmetricTraceEndpoint.lean) identifies the
existing endpoint's two targets as rational functions of the four coefficient
coordinates. Write the exact weighted equation and source as
\[
f=\ell u^3+Bu^2+Cu+D,\qquad P=p_0+p_1u+p_2u^2,
\]
where
\[
p_0=bdc^2,\qquad p_1=-bd(c^2+\lambda^2),\qquad p_2=bd\lambda^2.
\]
The canonical coefficients are
\[
T_0=\frac{3\ell p_0-p_2C}{3\ell},\qquad
T_1=\frac{3\ell p_1-2p_2B}{3\ell}.
\]
The module binds these expressions to `rawWeighted`, `rawSource`,
`targetSource0`, and `targetSource1` in the actual chart function field.
It proves that both targets belong to the subfield generated by the images
of the four base coordinates. Every lifted coefficient polynomial omits the
normal variable, and nonvanishing of \(\ell\) follows from the existing
smooth-point witness.

The [scalar theorem](SymmetricCubicTrace.lean) also proves the
literal cubic expansion, the two identities
\[
P-\frac{p_2}{3\ell}f_u=T_0+T_1u,\qquad
P_u-\frac{p_2}{3\ell}f_{uu}=T_1,
\]
and preservation of the full residue numerator. Its direct proof is
[accepted on Prove2Me](https://prove2.me/theorems/b0bcfd4c-df00-43b3-9114-86ccae7d0db6).
These source identities specify the two required traces; they construct
neither an upstairs current nor either normalized-trace equality.

The exact coefficient calculation and these formalizations were contributed
by `kmehltretter82` with OpenAI Codex assistance, extending the existing
chart, canonical-source reconstruction, and conditional trace endpoint of
`fqlx`, `benediamond`, and the collaborators credited above.

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
