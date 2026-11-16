This is a cyclic-cover version of the Fano construction, with a different symmetry from the reflection examples. Writing \(Z=X_2^3\), the sextic becomes \(G=Z^2+t\cdot Z\cdot C+H\), where \(C\) and \(H\) are the displayed cubic and sextic in the other five variables. The order-three automorphism \(X_2\mapsto\zeta_3\cdot X_2\) survives the couplings.

**Nonconstructive existence is known**, by the weighted-Fano density theorem in [Chapter 3, §3.4](../../docs/03-geometric-support.md). The finite map

\[
\Phi=(X_0,X_1,X_2^3,Y_0,Y_1,Y_2),\qquad \det(d\Phi)=3\cdot X_2^2
\]

has weights \((1,1,3,1,1,1)\), whose sum is eight. Its degree-six quotient is Fano of index two. Our target has exactly the required density form:

\[
A=\det(d\Phi)\cdot \Phi^*\!\left(\frac{1}{3}\cdot X_0\cdot Y_0^3\right).
\]

The polynomial in parentheses has weighted degree four, as required for \(q=1\). Equivalently, the character \(\zeta_3^2\) of the numerator cancels the character \(\zeta_3\) of the residue volume.

The quotient theorem supplies support through rational curves. A concrete approach is to find a free weighted curve with a nonsingular deformation system, then use its family to construct a primitive for the displayed quotient source. Dominance, a polynomial normal, finite descent, and legal transport through the cubic map are substantive obligations. The shared polynomial-family machinery handles some of these steps once their hypotheses are supplied; geometric uniruledness alone is not an evaluated rational field.

This makes the instance a test of making a known existence theorem effective. A small explicit curve could provide the needed algebraic input, while a formalized geometric argument would also meet the challenge. Neither route is required to produce a compact expanded denominator.

This is not merely the old reflection formula with a different label. None of the six coordinate reflections preserves the equation, and the Hessian symmetrizer calculation rules out a nontrivial linear block decomposition. The finite-map theorem is relevant because of the specific density factor in \(A\); it does not say that every target on the same sextic has been handled.
