This example has the additive decomposition

\[
F=H(X_0,X_1,Y_0,Y_1)+B(X_2,Y_2),
\qquad
B(s,t)=s^6+\frac{15}{7}s^4t^2+\frac{10}{7}s^2t^4+t^6.
\]

The four-variable core is coupled, while the binary factor is separately even. The target is \(q=1\), \(A=X_0^3Y_0^3\). It is even in each binary coordinate, so its residue is anti-invariant under both coordinate reflections. The ordinary reflection quotients serve the complementary sectors.

The [two-reflection theorem of Chapter 3B](#technical-information/weighted-threefolds) supplies divisor support for the entire globally invariant fourth cohomology of this fourfold. Its hypotheses hold directly: the protected equation is globally \(Y\)-even and separately even in \(X_2\) and \(Y_2\), and reduction modulo five is the smooth Fermat sextic. The support-to-certificate theorem therefore establishes rational certificate existence for this exact target.

The geometric input is the anti-invariant third cohomology of a weighted sextic threefold in \(\mathbb P(1,1,1,1,2)\). In the split presentation, the natural example is \(u^3=H\). Weighted adjunction gives trivial canonical class, so the earlier Fano companion argument does not apply directly. Chapter 3B adapts Voisin's Fano-extension and Abel–Jacobi method to supply the required support, then transfers it to the fourfold.

This makes the instance a concrete test of converting the geometric existence theorem into a Lean proof of the protected certificate statement. The chapter does not display a rational-field certificate or supply that formal proof. The target remains formally open until a checked solve is accepted; an existential Lean proof is admissible without exporting an expanded denominator.
