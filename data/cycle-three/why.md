This sextic closes the two-link holdout into a cycle:
\[
F=F_0+\frac12\cdot\bigl(
X_0^3\cdot X_1\cdot Y_0\cdot Y_1+
X_1^3\cdot X_2\cdot Y_1\cdot Y_2+
X_2^3\cdot X_0\cdot Y_2\cdot Y_0\bigr).
\]
Simultaneously cycling the three coordinate pairs preserves the equation. The target \(A=X_0^3\cdot Y_0^3\) singles out one pair, so a certificate transports to its cyclic translates. A certificate for their invariant sum, however, does not automatically separate into certificates for each summand.

The closing edge gives a precise boundary for the [holdout cover construction](../../docs/02-explicit-constructions.md). Adjoin \(T^6=Y_0^6+Y_2^6\), and write \(\alpha=Y_0/T\), \(\beta=Y_2/T\), \(y=Y_1\). The two chain terms become \(yT\) times a quartic in \(X\), which respects the exchange \(y\leftrightarrow T\). The closing term becomes
\[
\frac12\cdot\alpha\cdot\beta\cdot X_0\cdot X_2^3\cdot T^2.
\]
There is no matching \(y^2\) term. The exchange that creates the weighted quotient and its moving conic is therefore lost. This is more specific than a general lack of symmetry: the cycle retains paired signs and a cyclic permutation while breaking the particular symmetry used by the cover.

The complementary quotient of §2.8 is lost as well. Its action has weights \((5,1,5)\) on \(Y\), whereas the closing monomial has weight four modulo six. Thus replacing the cover by that diagonal quotient does not repair this equation-level obstruction.

The surviving paired signs suggest a different reduction. On the chart \(Y_i=r_iX_i\), put \(u_i=X_i^2\). The equation becomes a plane cubic in \(u_0,u_1,u_2\), with pure cubes and the three directed terms \(u_0^2u_1,u_1^2u_2,u_2^2u_0\). This retains the entire cycle in a small auxiliary geometry. It does not, by itself, supply a rational primitive or control variation of the ratio parameters.

A useful extension must therefore replace the chain quotient while tracking the target's residue character and the density of the new map. Moving between a cubic and another model requires more than a fiberwise equivalence: parameter derivatives enter the physical divergence equation. The [degree-twelve companion](../cycle-q2/why.md) keeps the same sextic while changing the numerator and pole order, separating this first target from a claim about every residue on the cyclic variety.
