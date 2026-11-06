# Polynomial companions and higher residues for split ternaries

## Exact target

The construction treats exactly the polynomial and numerator in [instance.rec](instance.rec). Put \(c=5/7\), and write
\[
\begin{aligned}
f(x,a,y)&=x^6+a^6+y^6+c(x^5a+x^2a^3y+3xy^5+2a^5y),\\
g(r,z,w)&=r^6+z^6+w^6+c(2r^5z+2r^3zw^2+rw^5+3z^5w).
\end{aligned}
\]
Thus \(F=f(X_0,X_1,X_2)+g(Y_0,Y_1,Y_2)\), \(q=2\), and \(A=X_0^4X_1^3Y_0^3Y_1^2\). On the chart used below, set \(p=f(x,a,1)\), \(q_0=g(r,z,1)\), and \(s=x^4a^3r^3z^2\). The two block degrees are seven and five; the construction retains this distinction throughout.

## Polynomial companion curves

The geometric input consists of the two actual weighted companion cones
\[
7\bigl(f(x,a,y)+S^3+T^3\bigr)=0,
\qquad
7\bigl(g(r,z,w)+S^3+T^3\bigr)=0.
\]
The ordinary variables have weight one and \(S,T\) have weight two. Both companions reuse a moving-conic seed modulo five, where their asymmetric perturbations vanish. The selected thirteen coefficient equations have Jacobian determinant \(1\) in \(\mathbf F_5\); the twelve-dimensional free/normal block has determinant \(4\). These are exact finite matrix calculations. Generic incidence and specialization then give finite extensions of the rational parameter field, polynomial curves on each exact characteristic-zero companion, polynomial normal vectors, and a nonzero evaluation determinant. The finite-field seed supplies these hypotheses through the maintained algebraic machinery; it is not itself the characteristic-zero certificate. See [CompanionSeeds.lean](CompanionSeeds.lean), [CompanionGeometry.lean](CompanionGeometry.lean), and [CompanionResidue.lean](CompanionResidue.lean).

## Second normal residue

The new higher-pole step is a polynomial-family residue construction for a third-order pole. For a hypersurface equation \(H\), a normal coordinate, and \(g_0=\partial_0H\), its second normal source is
\[
R_2(B)=\frac12\left(
\frac{B_{00}}{g_0^2}
-\frac{3B_0H_{00}+BH_{000}}{g_0^3}
+\frac{3BH_{00}^2}{g_0^4}\right).
\]
Choose a polynomial normal vector \(\psi\) satisfying \(dH(\psi)=1\), and thicken the curve linearly by \(c(t)+\varepsilon\psi(t)\). Write the equation as \(\varepsilon+a\varepsilon^2+b\varepsilon^3+\cdots\), and write the numerator times its Jacobian as \(K_0+K_1\varepsilon+K_2\varepsilon^2+\cdots\). The relevant polynomial integrand is
\[
P=K_2-3aK_1+(6a^2-3b)K_0.
\]
Actual polynomial gradient, Hessian, third derivative, and determinant identities prove
\[
P=J\bigl(R_2(B)+\operatorname{ResDiv}_{g_0}Z\bigr),
\]
with an explicit tangent correction \(Z\). Consequently polynomial integration in the curve parameter, followed by Piola transport, supplies a residue primitive. Derivative-compatible normalized trace descends it from the finite curve field to the companion field. This includes all second-order correction terms. The helper chain is [HigherResidue.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/HigherResidue.lean), [NormalTaylor.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/NormalTaylor.lean), [NormalJetBinding.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/NormalJetBinding.lean), [SourceDensityAlgebra.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/SourceDensityAlgebra.lean), [JacobianJets.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/JacobianJets.lean), [NormalRowJets.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/NormalRowJets.lean), and [HigherCurve.lean](../../formal/lean/HodgeComputer/Constructions/HigherResidues/HigherCurve.lean).

For the first block, use \(T\) as the normal coordinate, with \(h=x^4a^3\). On the cleared companion \(H=7(f+S^3+T^3)\), take \(B=49hST\). Since \(g_0=21T^2\), the rational first-order source
\[
B'=\frac12\partial_T(B/g_0)=-\frac{7hS}{6T^2}
\]
has exactly \(R_1(B')=R_2(B)\), where \(R_1(C)=\partial_0(C/g_0)\). The resulting tangent equation has right side \(-2hS/(9T^5)\). The function \(T\) is proved nonzero in the companion field, so these divisions are legal. [CompanionPoleTwo.lean](CompanionPoleTwo.lean), [CompanionPoleTwoFamily.lean](CompanionPoleTwoFamily.lean), and [RationalAmbient.lean](RationalAmbient.lean) bind this conversion to the actual cone.

## Radial descent and elliptic contraction

Radial descent uses the map \((T,x,a,y,S)=(\rho^2T_0,\rho x_0,\rho a_0,\rho,\rho^2S_0)\). The independent cone weights are \((1,1,1,2)\); the normal \(21T^2\) has weight four. The source above has weight minus one, and becomes an affine coefficient divided by \(\rho\). Taking the radial residue therefore gives the required affine primitive. The second companion uses its degree-five polynomial source and the ordinary companion construction. These particular weights, rather than an unrestricted assertion about affine polynomial sources, justify both descents. See [CompanionTheta.lean](CompanionTheta.lean), [CompanionThetaBridge.lean](CompanionThetaBridge.lean), and [CompanionPrimitives.lean](CompanionPrimitives.lean).

Adjoin \(u^3=p\), \(v^3=q_0\), and use the Fermat elliptic curve \(a_e^3+b_e^3+1=0\), with \(\delta a_e=b_e^2\), \(\delta b_e=-a_e^2\). Scalar conversion of the first companion gives \(-h a_e/(3u^5b_e^2)\). The exact identity
\[
\delta(a_e^2/b_e+b_e^2/a_e)=b_e/a_e^2-a_e/b_e^2
\]
converts it, including its base-divergence terms, into the theta source \((h/u^5)(b_e/a_e^2)\). The second companion gives the ordinary source \(r^3z^2/v^4\). Translated elliptic contraction, with its infinity correction, combines these into a divergence primitive for their product. The checked scalar and product bindings are [EllipticSource.lean](EllipticSource.lean), [CompanionScalar.lean](CompanionScalar.lean), [CompanionThetaScalar.lean](CompanionThetaScalar.lean), [CompanionElliptic.lean](CompanionElliptic.lean), [CompanionAssembly.lean](CompanionAssembly.lean), and [ProductDivergence.lean](ProductDivergence.lean).

Multiplication by \(u^5v^4\), then normalized trace, produces a rational four-vector \(W\) satisfying
\[
\operatorname{div}W-\frac{5W(p)}{3p}-\frac{4W(q_0)}{3q_0}=s.
\]
The physical substitution \(X=t(x,a,1)\), \(Y=t\lambda(r,z,1)\) gives \(F=t^6(p+\lambda^6q_0)\). [HigherPoleTransport.lean](HigherPoleTransport.lean) and [PhysicalTransport.lean](PhysicalTransport.lean) construct the strict pole-two field, retaining the vertical component and the physical Jacobian correction \(2V_\lambda/\lambda\).

## Legal homogeneous certificate

Finally, [CertificateClearing.lean](CertificateClearing.lean) tracks common homogeneous fractions simultaneously in the ambient field and on \(F=0\). Their denominators remain nonzero in the hypersurface function field; exact irreducibility of \(F\) makes the resulting denominator relatively prime to \(F\). Clearing gives a homogeneous denominator \(D\), six numerators of degree \(\deg(D)+7\), and the full strict identity
\[
AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=0.
\]
The quotient polynomial is \(Q=0\). [Solution.lean](Solution.lean) identifies the protected polynomials exactly. This is an existential certificate construction; it does not export an expanded denominator or six expanded witnesses.

## Attribution

The reusable elliptic construction comes from `1337isnot1337`'s accepted [PR #149](https://github.com/hodge-computer/sextics/pull/149), building on `fqlx`'s moving-conic work, `HeadOfNaps`'s certificate and quotient constructions, and the repository contributors' maintained machinery. The shared library is extracted separately in [PR #158](https://github.com/hodge-computer/sextics/pull/158). Lean and mathlib provide the formal foundations. This adaptation was prepared for `fqlx` with OpenAI Codex assistance. OpenJev was used for heuristic route comparisons and independent plausibility checks; it supplies no formal verification or demonstrated speedup.
