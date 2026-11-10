Use the cyclic three-link sextic from [the degree-six cyclic instance](#case/cycle-three), with
\[
q=2,\qquad
A=X_0^2\cdot X_1^2\cdot X_2^3\cdot Y_0^2\cdot Y_1^2\cdot Y_2.
\]
Every coordinate occurs, and the unequal exponents in the final pair distinguish one position in the cycle. Cyclic permutation produces two companion targets on the same hypersurface.

The pole order requires field components of degree seven and divisibility of \(A-2dF(v)+F\operatorname{div}(v)\) by \(F^3\). Multiplying a degree-six certificate by a polynomial contributes derivatives of that multiplier and does not generally give this identity. The [cyclic Jacobian construction](#case/cycle-three) establishes a different, second-order-pole identity.

The sextic is invariant under the sixth-root diagonal action with weights \((2,1,0,3,2,1)\). The present numerator has weight seventeen, while the projective volume contributes nine, so the residue has character \(\zeta_6^{17+9}=\zeta_6^2\). Averaging to the invariant quotient therefore erases it. The [paired-sign sector theorem](#technical-information/known-locus/paired-signs-and-a-surface-quotient) supports the invariant sector; its conclusion does not cover this nontrivial character.

The equation has a second order-three symmetry. Put \(\omega=\zeta_6^2\). The sextic is invariant under the paired sign \(s_2:(X_2,Y_2)\mapsto(-X_2,-Y_2)\) and under
\[
\gamma=\operatorname{diag}(\omega^2,\omega^2,1,\omega,1,1).
\]
The numerator is even in \((X_2,Y_2)\) and has \(\gamma\)-weight \(2\cdot2+2\cdot2+1\cdot2\equiv1\), while the projective volume contributes \(\omega^2\). The residue is therefore invariant under both.

The [theorem of Chapter 3D on a paired sign and an order-three symmetry](#technical-information/hodge-loci) supplies divisor support for the fourth cohomology invariant under \(s_2\) and \(\gamma\). Its hypotheses hold for the exact protected equation: the two invariances are visible on its nine monomials, and the fourfold is smooth by the elimination recorded with that chapter's example. The support-to-certificate theorem therefore establishes rational certificate existence for this exact target at pole order two. The two cyclic companions are served by the conjugate symmetries.

The geometric input is the invariant third cohomology of a weighted sextic threefold in \(\mathbb P(1,1,1,1,2)\) under an order-three symmetry that moves its holomorphic form. The pencil \(Y_2=\lambda X_2\), divided by the paired sign, has such fibers:
\[
X_0^6+X_1^6+Y_0^6+Y_1^6+(1+\lambda^6)w^3
+\tfrac12\bigl(X_0^3X_1Y_0Y_1+\lambda X_1^3Y_1w+\lambda X_0Y_0w^2\bigr)=0,
\qquad w=X_2^2.
\]
Chapter 3D obtains moving one-cycles on them from Hodge loci of del Pezzo fourfolds through the threefold, proves by a finite rank calculation that their Abel–Jacobi differentials span the invariant part, and specializes the resulting supported projector before transferring support to the fourfold. An explicit rational primitive is a further algebraic realization of that established support.

The [holdout \(q=2\) target](#case/holdout-q2) belongs to the [cyclic-six family](#technical-information/known-locus/a-cyclic-six-family-and-complementary-quotients), whose deck/exchange support argument applies at every pole order. That theorem uses the separate action with weights \((0,0,0,5,1,5)\). The closing coupling here has weight four under that action and also breaks the auxiliary exchange. Thus the three diagonal actions have different scopes: the sixth-root action preserving this cycle supports its invariant residue sector, the paired sign with the second order-three symmetry supports the sector of this target, and the all-target cyclic-family theorem requires a different symmetry of the equation.
