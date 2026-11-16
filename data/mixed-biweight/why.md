The holdout chain has mixed terms only of \(X/Y\)-bidegree \((4,2)\). This example uses chain coefficients \(1/2\) and adds the opposite biweight
\[
\frac13\cdot X_0\cdot X_2\cdot Y_0^3\cdot Y_2.
\]
The global involution and all three paired sign changes survive. The target is still \(X_0^3\cdot Y_0^3\), making this a comparison of coupling geometry for the same prescribed monomial.

The [holdout cover construction](../../docs/02-explicit-constructions.md) shows exactly where its reduction ceases to apply. On \(T^6=Y_0^6+Y_2^6\), set \(\alpha=Y_0/T\), \(\beta=Y_2/T\), and \(y=Y_1\). The new coupling is
\[
\frac13\cdot\alpha^3\cdot\beta\cdot X_0\cdot X_2\cdot T^4.
\]
Without a corresponding \(y^4\) term, the exchange \(y\leftrightarrow T\) no longer preserves the equation. The polynomial cannot be passed unchanged to the quotient with coordinates \(S=y^2+T^2\), \(P=yT\). The issue is therefore not merely an inconvenient exponent pattern in the final vector field: the auxiliary reflection itself has disappeared.

The complementary diagonal action with weights \((5,1,5)\) on \(Y\) does preserve the chain terms, but multiplies this new term by \(\zeta^2\). Its quotient and polynomial-density construction therefore cannot be substituted for the broken cover without another change of geometry.

A useful approach would either replace that reflection or construct primitives on a cover with the extra fourth-power term retained. The [mixed-polar target](../mixed-polar/why.md) tests a related asymmetric quartic term with a different placement and target, while [broken paired signs](../off-paired/why.md) changes the finite symmetry without adding a second biweight. These comparisons help separate the actual hypotheses of a proposed extension.

The [cyclic cubic construction](../cycle-three/why.md) suggests a more direct comparison that retains the paired signs. Write \(Y_i=r_iX_i\) and \(u_i=X_i^2\). The extra term becomes \(\frac13r_0^3r_2u_0^2u_2\), while the two chain terms give \(u_0^2u_1\) and \(u_1^2u_2\). These form a transitive pattern rather than the directed cubic cycle of that construction. Plane-cubic invariant theory can still be applied, but the Jacobian coefficients, nonsingular polynomial-curve family, and physical source transport are different. A primitive on the already solved cyclic Jacobian cannot simply be substituted here.
