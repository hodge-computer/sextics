# A moving conic companion and algebraic elliptic contraction

## The fixed target and the certificate proved

Write

$$
P(u,v,w)=u^6+v^6+w^6+
\frac57\bigl(u^5v+u^3vw^2+uvw^4+2uv^5\bigr).
$$

The protected instance is

$$
F=P(X_0,X_1,Y_0)+P(Y_1,Y_2,X_2),\qquad
A=X_0^4X_1Y_1,\qquad q=1.
$$

The second displayed summand is exactly the instance's second ternary polynomial, with its variables ordered to match the first. No coefficient, variable, or numerator is changed. The theorem [Submission.certificate](Solution.lean) proves the verifier-generated statement

```lean
HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A
```

The proof is an existence construction using finite algebraic extensions, rational functions, and classical choice. It does not export an expanded polynomial witness or a claimed small denominator degree. For the nonzero sextic \(F\) and homogeneous degree-six target \(A\), it supplies a nonzero homogeneous denominator \(D\), six homogeneous numerators \(N_i\) of degree \(\deg(D)+1\), relative primality of \(F,D\), and a polynomial \(Q\) satisfying

$$
AD^2-D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^2Q.
$$

A nonzero quotient is allowed and used. Before homogeneous extraction, the construction gives the stronger normalization

$$
\sum_iN_i\partial_iF=AD,\qquad
D\sum_i\partial_iN_i-\sum_iN_i\partial_iD=FQ.
$$

All existence assertions used to reach these identities are proved in Lean. In particular, the geometric existence theorem cited in the instance's motivation is not installed as an axiom.

## Overview of the construction

The two ternary blocks contribute different differential characters. On the affine charts of their triple planes, adjoin

$$
u^3=p=P(x,a,1),\qquad v^3=q=P(r,z,1).
$$

The central algebraic result is an ordinary divergence equation for the product

$$
\alpha=\frac{x^4a}{u^4},\qquad \beta=\frac{r}{v^2}.
$$

It is obtained by constructing primitives on an elliptic companion for each block and contracting their elliptic factors through rational residues. Multiplication by \(u^4v^2\) and normalized trace then give a weighted divergence equation over the original rational function field \(\mathbb C(x,a,r,z)\). An explicit change of coordinates turns that equation into a rational vector field for the physical sextic. A separate hypersurface evaluation proves that clearing its denominators preserves legality.

The Lean sources are grouped into thirteen flat helpers to keep the submission below the repository's file limit. Each helper identifies its original source components in comments; the mathematical namespaces and declarations remain descriptive.

## A polynomial family on the companion cone

### The equation and the finite seed

Use the companion cone

$$
P(x,a,y)+S^3+T^3=0.
$$

For integral computations multiply its equation by seven:

$$
H=7(x^6+a^6+y^6+S^3+T^3)
 +5(x^5a+x^3ay^2+xay^4+2xa^5).
$$

The family fixes \(x=4t\), takes \(a,y\) of degree at most two and \(S,T\) of degree at most four, and uses the constant coefficients of \(y,S,T\) as three independent parameters \(k_0,k_1,k_2\). There are thirteen remaining coefficients \(c_0,\ldots,c_{12}\), in the order

$$
\begin{aligned}
a&=c_0+c_1t+c_2t^2,\\
y&=k_0+c_3t+c_4t^2,\\
S&=k_1+c_5t+c_6t^2+c_7t^3+c_8t^4,\\
T&=k_2+c_9t+c_{10}t^2+c_{11}t^3+c_{12}t^4.
\end{aligned}
$$

The thirteen incidence equations are the coefficients of \(H\) in degrees zero through twelve. An exact seed over \(\mathbb F_5\) is

$$
(k_0,k_1,k_2)=(4,2,3),\qquad
(c_0,\ldots,c_{12})=(2,0,4,0,2,0,1,0,3,0,1,0,2).
$$

Thus \(x=4t\), \(a=2-t^2\), \(y=4+2t^2\), \(S=2+t^2+3t^4\), and \(T=3+t^2+2t^4\) modulo five. The incidence Jacobian is invertible, as is the twelve-column matrix needed to construct a polynomial normal vector while fixing \(x\). The submitted Lean proof checks explicit right inverses over the finite field; it does not rely on floating-point ranks or external CAS output.

[ConicSeed.lean](ConicSeed.lean) contains the seed and matrix checks. [MovingConic.lean](MovingConic.lean) forms the localized incidence algebra, proves its required opens remain nonzero, and obtains a finite characteristic-zero coefficient field over \(\mathbb C(k_0,k_1,k_2)\). It also proves the polynomial-family equation and the normal-vector identities.

### Evaluation, integration, and trace

The three endpoint parameters and the curve parameter supply four independent coordinates. The evaluation map is proved injective, the induced companion function-field extension is proved finite, and the normal-plus-tangent evaluation matrix is proved nonsingular. These conditions allow the maintained polynomial-family residue bridge to integrate a polynomial density along the curve parameter. Normalized trace descends the result to the companion function field.

The resulting theorem supplies a companion residue primitive for every polynomial source, not just the two sources eventually selected. This is the role of `CrossedFixedConic.companion_residue_solution` in [MovingConic.lean](MovingConic.lean).

Radial descent through \(y\) gives the affine companion

$$
P(x,a,1)+S^3+T^3=0.
$$

For the two sources \(7x^4a\) and \(7xST\), [CompanionPrimitives.lean](CompanionPrimitives.lean) obtains actual polynomial numerator/denominator data: the reduced denominator is nonzero, the normal-source identity holds exactly, and the reduced divergence numerator vanishes. The factor seven agrees with the cleared companion equation and cancels in the scalar conversion below.

## Passing from companion data to elliptic primitives

Use the Fermat elliptic curve

$$
a_e^3+b_e^3+1=0
$$

with invariant derivation \(\delta a_e=b_e^2\), \(\delta b_e=-a_e^2\). It is presented in Lean by

$$
y_e^2=x_e^3-432,\qquad
a_e=-\frac{y_e+36}{6x_e},\qquad
b_e=\frac{y_e-36}{6x_e}.
$$

On the first triple plane put \(S=ua_e\), \(T=ub_e\). The companion evaluation is injective after switching to its monic cubic presentation in \(T\). The coefficient injection uses the transcendence of \(a_e\) over the base field. Consequently every denominator already known nonzero on the companion remains nonzero after this substitution. This check is necessary: substitution into a field is not a license to invert an arbitrary old denominator.

For a companion vector value \((V_x,V_a,V_S,V_T)\) define

$$
f=\frac{3(b_eV_S-a_eV_T)}{u^2},\qquad
C_x=-\frac{3V_x}{u},\qquad C_a=-\frac{3V_a}{u}.
$$

The normal identity, its \(S,T\) derivatives, and the zero divergence identity imply the scalar equation

$$
\delta f+\partial_xC_x+\partial_aC_a
 =\frac{B}{u^4}-\frac{a_eB_S+b_eB_T}{u^3}.
$$

[ScalarCalculus.lean](ScalarCalculus.lean) proves this first-jet identity and binds it to the evaluated polynomial data. It works with the actual evaluated first jets, so it does not assume a globally defined substitution homomorphism on an ambient rational function field.

The first source yields

$$
\delta f+\operatorname{div}_{x,a}C=\alpha.
$$

The second source initially yields \(-\beta a_eb_e\). The identity

$$
\delta\left(\frac{b_e^2}{a_e}\right)
 =\frac{b_e}{a_e^2}-a_eb_e
$$

changes its sign and adds a coboundary, giving

$$
\delta g+\operatorname{div}_{r,z}G=\beta\theta,
\qquad \theta=\frac{b_e}{a_e^2}.
$$

These are the checked `first_scalar_primitive` and `second_scalar_primitive` theorems in [EllipticKernels.lean](EllipticKernels.lean). The same construction proves that \(g\) is killed by the first block's coefficient derivatives and \(f\) by the second block's derivatives. Those independence properties are retained throughout base change and translation.

## Algebraic residue contraction, including boundaries

### Separating finite poles

Translate the first primitive and its accompanying functions by an independent generic elliptic point. The translation is an actual field homomorphism, preserves the invariant derivation, and commutes with the coefficient derivatives because the generic point is constant for those derivatives.

[EllipticTranslation.lean](EllipticTranslation.lean) proves more than a finite numerical avoidance test: at each affine point over the old coefficient field, the translated functions specialize to translation of the old functions by that point. The resulting field images are nonzero whenever the original functions are nonzero. Simultaneous specialization on both branches proves regularity on the whole old finite fibre, including fibres with a zero \(y_e\) coordinate.

Finite splitting fields then supply the old poles, the needed elliptic points above them, and the finite residue supports after translation. The chosen residue functional \(R\) sums finite residues over fibres containing nonzero residues of \(f\theta\) and excludes the three theta fibres. It satisfies

$$
R(\delta h)=0,\qquad R(\partial_i h)=\partial_iR(h),\qquad R(g)=0.
$$

The last equality follows from the proved pole separation, not from a formal assertion that arbitrary primitives have disjoint poles.

### The theta pairing and infinity

For the canonical expression \(h=h_0(x_e)+h_1(x_e)y_e\), the trace of \(h\theta\) times the invariant differential has rational kernels

$$
K_0=-\frac{36x_e(x_e^3+3456)}{(x_e^3-1728)^2},\qquad
K_1=\frac{3888x_e^4}{(x_e^3-1728)^2}.
$$

At a theta fibre \(r^3=1728\), regularity gives the local formula

$$
\operatorname{Res}_r(h_0K_0+h_1K_1)
 =-12h_0'(r)+432h_1'(r)+\frac{r^2}{2}h_1(r)
 =-\delta h(r,-36).
$$

The proof also accounts for infinity. It constructs, for the chosen \(f\), a base-linear functional \(B\) satisfying

$$
B(1)=0,\qquad B(\partial_i h)=\partial_iB(h),\qquad
\operatorname{InfCoeff}\operatorname{Tr}(f\theta\omega)=B(\delta f).
$$

Here `InfCoeff` is the coefficient of \(x_e^{-1}\) at infinity, the negative of the residue there. The construction uses a finite rational approximation at \(t=1/x_e=0\). Its triangular recurrence has nonzero denominators \(5+2n\), and the approximation is taken over \(\mathbb Q\) so its coefficients are killed by every coefficient derivation. Its order is chosen beyond the particular function's pole order. Thus no regularity at infinity is silently assumed and no infinite formal summation is needed.

The rational global residue theorem, the three finite theta contributions, and this infinity correction yield

$$
R(f\theta)=3\alpha-\operatorname{div}_{x,a}\xi,
\qquad
\xi_i=\sum_{r^3=1728}C_i(r,-36)+B(C_i).
$$

[InfinityPairing.lean](InfinityPairing.lean) contains the local and infinity calculations. [EllipticContraction.lean](EllipticContraction.lean) constructs the pole sets and completes the global pairing and contraction.

### The product divergence and descent

Applying \(R\) to the derivative of \(fg\), using the two scalar equations and the independence properties, gives a divergence whose source is \(\beta R(f\theta)\). Explicitly, take

$$
U_i=\frac{R(C_i g)+\beta\xi_i}{3},\qquad
V_j=\frac{R(fG_j)}{3}.
$$

Then

$$
\operatorname{div}_{x,a}U+\operatorname{div}_{r,z}V=\alpha\beta.
$$

The auxiliary finite extensions descend by normalized trace. The independent generic elliptic point descends by normalized trace to its rational \(x_e\)-line followed by the constant Laurent coefficient there. This is a linear retraction to the base field commuting with all coefficient derivatives. It avoids an unproved specialization of the final primitive.

For the actual two blocks, [ProductDivergence.lean](ProductDivergence.lean) proves this product divergence, multiplies its vector by \(u^4v^2\), and descends through the cubic-root extension. It obtains \(W\) over \(\mathbb C(x,a,r,z)\) with

$$
\sum_i\left(\partial_iW_i
 -\frac{4\partial_ip}{3p}W_i
 -\frac{2\partial_iq}{3q}W_i\right)=s,
\qquad s=x^4ar.
$$

The rational functions \(p,q\) are nonzero; for example their constant terms are one. All cube roots and all denominator inversions used above have corresponding nonvanishing proofs.

## Returning to the physical sextic

Use independent chart coordinates

$$
X_0=tx,\quad X_1=ta,\quad X_2=t\lambda,\quad
Y_0=t,\quad Y_1=t\lambda r,\quad Y_2=t\lambda z.
$$

Then \(F=t^6(p+\lambda^6q)\) and \(A=t^6\lambda s\). Put

$$
P_d=\sum_iW_i\partial_ip,\qquad Q_d=\sum_iW_i\partial_iq,
$$

and define the chart vector

$$
w_i=-\frac{\lambda}{3p}W_i,\qquad
w_\lambda=\frac{3ps+P_d+\lambda^6Q_d}{18p\lambda^4q}.
$$

Its physical six components are

$$
\mathcal V=\bigl(tw_x,tw_a,tw_\lambda,0,
 t(\lambda w_r+rw_\lambda),t(\lambda w_z+zw_\lambda)\bigr).
$$

The chart Jacobian contributes \(2w_\lambda/\lambda\) to divergence. Direct differentiation proves

$$
\mathcal V(F)=A,\qquad
\operatorname{div}\mathcal V
 =F\left(-\frac{3ps+P_d}{9p^2q\lambda^5t^6}\right).
$$

[PhysicalTransport.lean](PhysicalTransport.lean) proves that the chart substitution is injective, constructs the six physical partial derivations, binds the fixed polynomial and numerator, and proves these identities. It also proves irreducibility of the exact physical sextic: viewing it as monic in \(Y_0\), the specialization \(X_0=X_1=Y_1=0\), \(X_2=T-1\), \(Y_2=\mathrm i\) gives

$$
Y_0^6+(T-1)^6-1,
$$

which has the checked Eisenstein irreducibility argument at \(T=0\).

## Legal denominators and homogeneous extraction

Clearing an arbitrary rational representation could introduce a factor of \(F\). The proof instead tracks each fraction simultaneously in the ambient chart field and on the hypersurface.

For the second evaluation, adjoin a nonzero \(\lambda_0\) satisfying \(\lambda_0^6=-p/q\) and retain an independent nonzero radial variable \(t\). The same six coordinate formulas define an evaluation \(\rho\) with \(\rho(F)=0\). Every nonzero element of the base rational function field remains nonzero under this field embedding. In particular \(p,q,\lambda_0,t\), and the nonzero integer constants used as divisors remain nonzero.

A compatible fraction has a common physical polynomial representative \(N/D\) in both evaluations, with \(\rho(D)\ne0\). The proof establishes closure under the required operations, including inversion when the hypersurface value is nonzero. The six chart variables are physical coordinate ratios, and induction extends compatibility to every base rational function. Therefore all components of \(\mathcal V\) and its divergence quotient have compatible representatives.

A common denominator for the six components is legal because \(\rho(F)=0\) and \(\rho(D)\ne0\) imply \(F\nmid D\). Irreducibility upgrades this to relative primality. Injectivity of the ambient chart gives the exact polynomial normal identity. Clearing the divergence quotient's own legal denominator, and using primality of \(F\), proves that the polynomial divergence numerator is divisible by \(F\).

These are the checked `normalized_data` and `physical_certificate` theorems in [CertificateClosure.lean](CertificateClosure.lean). The maintained `homogeneous_data_of_normalized` theorem then replaces the denominator by one with a legal initial homogeneous component and performs finite homogeneous extraction. This supplies the required degrees and retains the full non-strict quotient. The normal chart is legal because its derivative is nonzero of degree at most five whereas \(F\) is nonzero homogeneous of degree six.

Finally, [Solution.lean](Solution.lean) identifies the polynomial definitions with the protected generated target by exact ring identities and applies the certificate theorem. No target replacement or extra hypothesis is present.

## Prior work and assistance

The companion and translated elliptic contraction strategy comes from the sextics project's [Chapter 3A, §§3A.2–3A.3](https://github.com/hodge-computer/sextics/blob/main/docs/03a-split-and-k3.md), including its discussion of involution-stable ternary decompositions. That geometric argument explains why the crossed target should be accessible. The present proof establishes the needed algebraic identities and existence constructions directly.

Ben Burns, GitHub `fqlx`, developed the accepted moving-conic/Fermat-cover proof in [PR #128](https://github.com/hodge-computer/sextics/pull/128). Benjamin Diamond, GitHub `benediamond`, extracted its reusable machinery in [PR #134](https://github.com/hodge-computer/sextics/pull/134). This submission imports that maintained library for generic incidence and field-factor arguments, polynomial normal vectors, finite derivation extension and trace, polynomial-family residue transport, and homogeneous certificate normalization. Its underlying notices also credit the earlier accepted `quadric-contact-broken` contribution for the quotient-rule construction. The target-specific family, scalar conversion, elliptic residue contraction with its infinity correction, and physical transport are supplied here; no complete accepted proof package is copied into this folder.

The rational residue theorem, Weierstrass addition formulas, and trace identities are classical algebraic tools; the particular formulas and boundary calculations used here are proved in the submitted Lean sources. The Lean and mathlib contributors supply the proof assistant and the imported algebraic foundations.

The research and formalization were prepared with OpenAI Codex assistance for GitHub contributor `1337isnot1337`. Earlier bounded searches and intermediate results were recorded in [the existing instance discussion](https://github.com/hodge-computer/sextics/discussions/114). The unsuccessful searches concerned specified denominator ansatzes, degree limits, or finite numerical trials; none was used as a proof of unrestricted nonexistence. The final argument uses neither their negative outcomes nor numerical approximations.
