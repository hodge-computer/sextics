# A replacement conic for the ternary deformation

## The fixed statement and construction

This proves `Submission.certificate` for the exact `holdout-ternary-deformation` instance. Write \(x_i=X_i\). The protected data are

\[
\begin{aligned}
F={}&x_0^6+x_1^6+x_2^6+Y_0^6+Y_1^6+Y_2^6
 +x_0^3x_1Y_0Y_1+x_1^3x_2Y_1Y_2\\
 &+\frac{x_0^5x_1+2x_1^5x_2+x_2^5x_0}{14},
\qquad A=x_0^3Y_0^3,\qquad q=1.
\end{aligned}
\]

The argument constructs an algebraic family of polynomial curves on the weighted quotient, integrates there, and returns through the Fermat cover by normalized trace. The new ingredient is an exact nonsingular conic incidence modulo five for this deformed equation. Étale flatness transports that incidence first to characteristic zero and then to the generic Fermat base. The coefficient \(1/14\) remains fixed throughout.

The conclusion is existential. It supplies a nonzero homogeneous polynomial denominator \(D\), six homogeneous polynomial numerators \(N_i\), and a polynomial quotient \(Q\) satisfying the full certificate identity. It does not provide an expanded JSON witness, a numerical denominator degree, or a minimal-degree assertion.

## The quotient and its new seed

Adjoin \(T\) with \(T^6=Y_0^6+Y_2^6\), and put

\[
\alpha=Y_0/T,\quad\beta=Y_2/T,\quad y=Y_1,
\quad S=y^2+T^2,\quad P=yT.
\]

Then \(\alpha^6+\beta^6=1\), and the physical equation becomes the weighted equation

\[
G=x_0^6+x_1^6+x_2^6
 +P(\alpha x_0^3x_1+\beta x_1^3x_2)+S^3-3SP^2
 +\frac{x_0^5x_1+2x_1^5x_2+x_2^5x_0}{14}.
\]

In the incidence calculation we use the integral polynomial \(H=14G\). This scaling matters: the conic normal pairing initially equals one for \(H\), and the subsequent residue calculation rescales the normal vector by fourteen for \(G\).

At \((\alpha,\beta)=(1,0)\) over \(\mathbb F_5\), the replacement polynomial curve is

\[
\begin{aligned}
x_0(t)&=1+2t^2,&x_1(t)&=t,&x_2(t)&=4+2t+2t^2,\\
S(t)&=4+t+t^2+3t^3+3t^4,&
P(t)&=4+t+4t^2+4t^3+3t^4.
\end{aligned}
\]

All thirteen coefficients of \(H\) on this curve vanish. The thirteen variables are the three coefficients of \(x_0\), the coefficients of \(t,t^2\) in \(x_2\), and the four positive-degree coefficients of each of \(S,P\). The constants \((x_2(0),S(0),P(0))\) are initially \((4,4,4)\); \(x_1=t\) is fixed. Each substituted equation has degree at most twelve.

[ConicSeed.lean](ConicSeed.lean) proves the exact finite-field incidence. [DeformedConic.lean](DeformedConic.lean) gives the full thirteen-by-thirteen coefficient Jacobian, an explicit inverse, and the checked matrix product identity. Thus the Jacobian determinant is a unit. The proof uses ordinary kernel-checked finite arithmetic, not floating-point computation or an unchecked native decision procedure. It does not reuse the undeformed seed's parity blocks.

## From the seed to a generic algebraic family

For a square polynomial system, localize its incidence algebra at the coefficient Jacobian determinant. The shared Jacobian criterion proves this algebra étale over its parameter ring. The finite-field point proves nontriviality. Flatness over the integral base then gives a nonzero generic fiber and a finite field factor.

[ConicLifting.lean](ConicLifting.lean) applies this argument over the integers; algebraic closedness embeds the resulting finite extension of \(\mathbb C\) into \(\mathbb C\). [ComplexConic.lean](ComplexConic.lean) therefore obtains a nonsingular complex incidence with the same fixed equation and endpoint constants. No assertion is made that the displayed residues themselves are a complex solution or that an arbitrary finite-field solution lifts.

Now let \(B\) be the function field of \(\alpha^6+\beta^6=1\), introduce three independent endpoint parameters \(k_1,k_2,k_3\), and allow all thirteen curve coefficients to vary. The complex point proves the new Jacobian-localized incidence algebra nontrivial over the integral parameter ring. [GenericConic.lean](GenericConic.lean) applies flatness again and selects a finite field extension

\[
E/B(k_1,k_2,k_3)
\]

containing a solution with invertible coefficient Jacobian. Thus a polynomial curve \(c(t)\) on \(G=0\) exists over \(E\), with \(x_1=t\) and endpoint coordinates \((k_1,k_2,k_3)\). Classical choice is used only after the relevant existence theorems have been proved.

## Dominance, polynomial integration and trace

The Jacobian inverse supplies polynomials \(n_i(t)\) with

\[
\sum_i H_i(c(t))n_i(t)=1.
\]

Only \(n_0\) may have nonzero constant coefficient, and its constant coefficient is nonzero. The matrix with columns given by this normal vector, the time derivative, and the three endpoint derivatives consequently has nonzero determinant: at \(t=0\), its determinant is the constant coefficient of \(n_0\). [ConicNormal.lean](ConicNormal.lean) and [ConicFlow.lean](ConicFlow.lean) prove these statements and the commutation of the derivations. The coefficient-field derivatives extend uniquely across finite separable extensions in characteristic zero.

The quotient's coordinate ring is a domain. One proves irreducibility by treating \(G\) as monic in \(x_0\) and specializing the other coefficients to the shared Eisenstein example. The ternary correction vanishes under the specialization used for this purpose. Evaluation at the curve first embeds the coefficient polynomial ring, using \(x_1=t\) and the independent endpoint values at \(t=0\), and then embeds the monic hypersurface ring and its fraction field \(K_q\) into \(E(t)\). Both fields have transcendence degree four over \(B\); essential finite type then proves that \(E(t)/K_q\) is finite. These are [ConicEmbedding.lean](ConicEmbedding.lean), [ConicTarget.lean](ConicTarget.lean), and [ConicDimension.lean](ConicDimension.lean).

Let \(\rho_q\) denote passage to \(K_q\), let \(g=\rho_q(G_0)\), and let \(\delta_i\) be the genuine tangent derivations on this normal chart. Define

\[
\mathcal D_g(w)=\sum_i\delta_i(w_i)-\frac{\sum_iw_i\delta_i(g)}{g}.
\]

The nonzero normal follows, for example, by specializing all coordinates except \(x_0\) to zero: \(G\) becomes \(x_0^6\), whereas \(G_0\) becomes \(6x_0^5\). Polynomial integration in \(t\), using the polynomial normal and tangent matrix, gives a residue primitive over \(E(t)\). Normalized finite trace commutes with the compatible derivations and descends it to \(K_q\). [ConicResidue.lean](ConicResidue.lean) proves, for every polynomial source \(U\), the existence of \(w\) with

\[
\mathcal D_g(w)=-\left(\frac{\rho_q(U_0)}g-
 \frac{\rho_q(U)\rho_q(G_{00})}{g^2}\right).
\]

This is an algebraic polynomial-integration argument. No analytic approximation or geometric vanishing theorem is assumed.

## Returning to the exact physical source

[DeformedCoverFields.lean](DeformedCoverFields.lean) constructs a common function field \(L\) with injective maps from both the physical residue field \(K_p\) and \(K_q\). Monic equations and injective coefficient maps establish the embeddings before any algebra structure is assigned. Transcendence-degree calculations prove both extensions finite. The physical and cover equations retain all three new ternary monomials.

On the physical normal chart, take tangent coordinates \((x_1,x_2,Y_0,Y_1,Y_2)\). On the cover use \((x_1,x_2,S,P,\beta)\). The Jacobian of the latter coordinates with respect to the former has determinant

\[
J=\frac{2\alpha^5(T^2-y^2)}T.
\]

[DeformedCoverCoordinates.lean](DeformedCoverCoordinates.lean) proves \(\alpha\ne0\), \(T\ne0\), and \(T^2-y^2\ne0\) in the actual cover field. These follow from the proved coefficient embeddings, not from a selected numerical point. [DeformedCoverDifferentials.lean](DeformedCoverDifferentials.lean) computes the Jacobian from the extended physical derivations. [DeformedCoverCompatibility.lean](DeformedCoverCompatibility.lean) proves that its first four inverse coordinate derivations restrict to the quotient tangent derivations and kill the entire Fermat coefficient field, including rational functions of its generators.

Apply the quotient primitive theorem to the positive source

\[
U=\frac{x_0^3S}{2\alpha^2}.
\]

Under the cover maps, the first and second distinguished normals of \(G\) agree with those of \(F\). The extra contributions are respectively

\[
\frac{5x_0^4x_1+x_2^5}{14},\qquad
\frac{20x_0^3x_1}{14}.
\]

[DeformedSourceBinding.lean](DeformedSourceBinding.lean) checks these identities and the source identity

\[
JU=A\left(1-\frac{y^4}{T^4}\right).
\]

The same factor multiplies the normal-divergence source \((A_0F_0-AF_{00})/F_0^2\). The shared residue Piola identity transports a quotient vector \(w\), with a zero fifth component, to the physical vector \(J M^{-1}w\), where \(M\) is the actual coordinate Jacobian.

For a sixth root of unity \(\zeta\) with \(\zeta^4\ne1\), the action

\[
T\longmapsto\zeta T,\qquad
(\alpha,\beta)\longmapsto(\zeta^{-1}\alpha,\zeta^{-1}\beta)
\]

fixes the physical coordinates and preserves the deformed cover equation: the new ternary terms involve only fixed coordinates. [DeformedDeck.lean](DeformedDeck.lean) constructs this action as an actual automorphism over \(K_p\). Its nontrivial character proves

\[
\operatorname{Tr}^{\mathrm{norm}}_{L/K_p}(T^{-4})=0.
\]

The correction term therefore disappears under normalized trace. Compatibility of trace with derivations gives the required residue equation for the original \(A\) over \(K_p\).

## Legal clearing and homogeneous certificate

The physical sextic is irreducible by the same monic specialization method. Its normal derivative is nonzero in the residue field, as proved in [PhysicalModel.lean](PhysicalModel.lean). Common representatives of the residue vector have denominators nonzero modulo \(F\). Irreducibility converts this condition into relative primality with \(F\); arbitrary denominator clearing without this condition would not suffice.

The shared finite-residue clearing theorem gives polynomial data \(D_0,N'_i,Q'\), with \(D_0\) relatively prime to \(F\), satisfying

\[
\sum_iN'_iF_i=AD_0,\qquad
D_0\sum_i\partial_iN'_i-\sum_iN'_i\partial_iD_0=FQ'.
\]

[DeformedCertificateClosure.lean](DeformedCertificateClosure.lean) applies this theorem, proves that the protected \(F,A\) are homogeneous of degree six, and invokes finite homogeneous extraction. The resulting \(D\) is homogeneous, nonzero and relatively prime to \(F\), and all six \(N_i\) are homogeneous of degree \(\deg(D)+1\). The full cleared identity is

\[
AD^2-D\sum_iN_iF_i+
 F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^2Q.
\]

A nonzero \(Q\) is allowed. These are exactly the protected pole-order-one certificate obligations. [Solution.lean](Solution.lean) combines the constructions and proves `Submission.certificate` without additional hypotheses or replacement target definitions.

## Prior work, assistance and limits

The construction builds directly on the accepted [central holdout proof](../holdout/solution.md) by GitHub contributor `fqlx`, including its moving-conic method, Fermat cover, Piola transport, trace descent, legal denominator clearing and homogeneous extraction. Benjamin E. Diamond, GitHub `benediamond`, and the repository contributors supplied the benchmark and certificate formalism and extracted the maintained [shared construction library](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/README.md). This submission imports its generic machinery and adapts its target-specific coordinate arguments to the deformed equation. The essential new incidence is the full nonsingular modulo-five seed and its two generic-fiber steps; the old central conic is not a solution of this target.

The modular conic and étale-incidence approach in the accepted [crossed-ternary-asymmetric contribution](../crossed-ternary-asymmetric/solution.md) by `1337isnot1337`, with its disclosed AI assistance, informed the finite-field search and the choice of a generic-incidence route.

The shared fraction-derivation machinery also credits `HeadOfNaps` and the accepted `quadric-contact-broken` contribution. The Lean and mathlib contributors supply the polynomial, étale-algebra, flatness, localization, field, derivation and trace foundations. Griffiths's residue theory and Diamond's certificate correspondence explain the geometric context, but no unformalized geometric theorem is added as an axiom here.

OpenAI Codex assisted the research, exact computations, formalization, checking and exposition for GitHub contributor `hodgepodgeconjecture`. Earlier partial results were recorded in [the instance discussion](https://github.com/hodge-computer/sextics/discussions/147#discussioncomment-19061777). That packet included experimental lifting and numerical observations. The final argument uses only the exact finite-field seed and the proved algebraic constructions; neither a numerical root nor a failed bounded search is a premise. No claim of unrestricted nonexistence follows from those earlier experiments.

The proof is an existence proof for this one fixed instance. It does not establish smoothness of a rendered mesh, solve every deformation coefficient, produce an optimized denominator, or assert that this is the first proof in the mathematical literature. Formal verification and the project's separate mathematical review determine acceptance.
