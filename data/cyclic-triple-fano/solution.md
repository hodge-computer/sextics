# A free weighted line and cubic pullback

## The quotient and the source

Set \(Z=X_2^3\). The fixed sextic is the pullback of the weighted sextic

\[
\begin{aligned}
H={}&Y_0^6+Y_1^6+X_0^6+X_1^6+Y_2^6+Z^2\\
 &+\frac57\bigl(X_0^3X_1Y_0Y_1+X_0^3Z+X_0^2Y_0Y_1Y_2^2
 +X_0X_1Y_1^3Y_2+X_0ZY_1Y_2+X_1ZY_0Y_1\bigr).
\end{aligned}
\]

The five ordinary coordinates have weight one and \(Z\) has weight three. The construction works on its affine cone. Its coordinate order in the proof is \((Y_0,Y_1,X_0,X_1,Y_2,Z)\); the final theorem explicitly returns to the repository's order.

The protected source is \(A=X_0X_2^2Y_0^3\), at pole order one. The quotient source is \(B=X_0Y_0^3\). The factor \(X_2^2\) is the density of the cubic substitution, with its scalar factor three absorbed into the transformed vector field. This source compatibility is essential: the argument does not assert that every target on this sextic follows from this quotient.

## The free line and its deformation

In the [instance discussion](https://github.com/hodge-computer/sextics/discussions/112#discussioncomment-19002605), `rbajaj5` identified the weighted line

\[
[X_0:X_1:Z:Y_0:Y_1:Y_2]=[0:s:0:is:t:it]
\]

and computed a full-rank twisted normal map. Work in the chart \(s=1\). The affine curve is

\[
(Y_0,Y_1,X_0,X_1,Y_2,Z)=(i,t,0,1,it,0).
\]

To deform it through a generic endpoint on \(Y_1=0\), write the endpoint as \((\xi,0,k_0,k_1,k_2,k_3)\), with

\[
\xi^6+k_0^6+k_1^6+k_2^6+k_3^2+\frac57 k_0^3k_3=0.
\]

Allow the following six coefficients to vary:

\[
\begin{aligned}
Y_0&=\xi+a t,& Y_1&=t,& X_0&=k_0+b t,\\
X_1&=k_1,&Y_2&=k_2+c t,&Z&=k_3+d t+e t^2+f t^3.
\end{aligned}
\]

Substitution into \(H\) has degree at most six. The constant coefficient vanishes by the endpoint relation, leaving exactly six positive-coefficient equations. At the displayed line, the endpoint is \((i,0,0,1,0,0)\) and \((a,b,c,d,e,f)=(0,0,i,0,0,0)\). With rows indexed by \(t,t^2,\ldots,t^6\), their Jacobian is

\[
\begin{pmatrix}
6i&0&0&0&0&0\\
0&0&0&5i/7&0&0\\
0&0&0&0&5i/7&0\\
0&0&0&0&0&5i/7\\
0&5i/7&0&0&0&0\\
0&0&6i&0&0&0
\end{pmatrix}.
\]

Its determinant is \(-22500/2401\). [LineSeed.lean](LineSeed.lean) proves the exact curve equation and an explicit inverse-matrix identity over \(\mathbb C\). No numerical approximation or unformalized freeness theorem is assumed.

## A generic family and polynomial normal

The endpoint ring is integral. Regard its equation as monic in \(\xi\), and specialize \((k_0,k_1,k_2,k_3)=(0,T+1,0,i)\). The resulting polynomial is \(\xi^6+(T+1)^6-1\), which is Eisenstein at \(T\). The same specialization proves the relevant quotient and physical hypersurface irreducibility. These statements are checked in [LineEndpoint.lean](LineEndpoint.lean) and [CyclicDomain.lean](CyclicDomain.lean).

Localize the square incidence algebra at its coefficient Jacobian. The exact seed proves that this étale algebra is nonzero. Flatness over the integral endpoint ring keeps its generic fiber nonzero. A finite field factor therefore supplies all six curve coefficients over a finite extension \(E\) of the endpoint function field. [LineLifting.lean](LineLifting.lean) applies the shared lifting theorem to this precise system. The coefficient \(5/7\) stays fixed throughout.

The inverse coefficient Jacobian also supplies a polynomial normal vector \(\psi(t)\) satisfying

\[
\sum_j H_j(c(t))\psi_j(t)=1.
\]

Here the positive-degree variations all have zero constant term, so the normal can be chosen with constant value \((H_{Y_0}(c(0))^{-1},0,\ldots,0)\). This is an exact polynomial identity, proved by the finite coefficient system in [LineNormal.lean](LineNormal.lean).

The four independent endpoint coordinates and the time coordinate \(Y_1=t\) make evaluation dominant. More precisely, the constant coefficients give an injective map on the four-parameter polynomial ring, and adjoining the nonzero anchored time coordinate preserves injectivity. The monic hypersurface relation then embeds the quotient function field \(K\) into \(E(t)\). Both have transcendence degree five over \(\mathbb C\), and essential finite type proves that \(E(t)/K\) is finite. [LineEmbedding.lean](LineEmbedding.lean) checks these steps.

The four endpoint derivations extend across the finite separable coefficient extension. Together with differentiation in \(t\), they give five commuting derivations. The normal-plus-tangent matrix has nonzero determinant: its constant coefficient is \(H_{Y_0}(c(0))^{-1}\). These facts, including preservation of the polynomial subring, are proved in [LineSource.lean](LineSource.lean).

## Integration, trace and cubic transport

The polynomial-family integration theorem produces a residue primitive over \(E(t)\) for any polynomial quotient source, hence for \(B=X_0Y_0^3\). Normalized finite trace descends the primitive to \(K\). Legal denominator clearing then produces polynomial data \(d,N_j,Q\) with

\[
\gcd(H,d)=1,\qquad
\sum_jN_jH_j=Bd,\qquad
 d\sum_j\partial_jN_j-\sum_jN_j\partial_jd=HQ.
\]

[LineClosure.lean](LineClosure.lean) supplies the complete hypotheses of the shared integration and clearing theorem. In particular, trace is taken over a proved finite extension and denominators are nonzero in the actual hypersurface function field.

Let \(\varphi\) substitute \(Z=X_2^3\). Before reordering the coordinates, put

\[
D=\varphi(d),\qquad
\widetilde N_j=X_2^2\varphi(N_j)\quad(j\ne Z),\qquad
\widetilde N_{X_2}=\frac13\varphi(N_Z).
\]

The chain rule gives

\[
\sum_j\widetilde N_jF_j=AD,\qquad
 D\sum_j\partial_j\widetilde N_j-\sum_j\widetilde N_j\partial_jD
 =F\,X_2^2\varphi(Q).
\]

The denominator remains legal. The cubic substitution is injective on the coefficient ring, and the equation is monic in the unaffected coordinate \(Y_0\); divisibility by its pullback would imply divisibility before substitution. Physical irreducibility converts this nondivisibility into relative primality. [CubicLift.lean](CubicLift.lean) proves both transport and legality.

Finally, homogeneous extraction gives a nonzero homogeneous denominator \(D\), six numerators of degree \(\deg(D)+1\), and the full cleared identity required by `HodgeComputer.Verify`. A nonzero quotient is allowed. [Certificate.lean](Certificate.lean) assembles the proof, and [Solution.lean](Solution.lean) binds it to the protected target, including the coordinate permutation.

## Scope and attribution

This proves existence of a finite polynomial certificate for the specified target. It does not expand the coefficients of the denominator or provide a denominator-degree bound; no `witness.json` is supplied. The finite generic field factor, trace, and homogeneous extraction are used through proved existence theorems.

- `rbajaj5` supplied the explicit free weighted line and its normal-map calculation in the linked discussion. The six-variable anchored deformation above is a direct refinement of that input.
- `fqlx` supplied the moving-family, polynomial-normal, integration, finite-trace, legal-clearing, and homogeneous-extraction machinery in [the central holdout construction](../holdout/solution.md), and the generic anchored-family and lifting argument in [PR #150](https://github.com/hodge-computer/sextics/pull/150). This proof uses the maintained [HoldoutCover library](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/README.md) and its [polynomial-curve extensions](../../formal/lean/HodgeComputer/Constructions/PolynomialCurves/README.md), retaining their prior-work and assistance credits.
- `HeadOfNaps` contributed the fraction-derivation machinery used by that shared library. Benjamin E. Diamond supplied the problem, certificate formalism, and geometric framework. The Lean and mathlib contributors supplied the formal algebraic foundations.
- OpenAI Codex assisted the adaptation, exact calculations, Lean formalization, and exposition for `benediamond`. The proof builds on the mathematical record above; neither the computer algebra check nor the rendered surface substitutes for the Lean theorem.
