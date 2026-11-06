Group the variables into the three pairs \((X_i,Y_i)\). The first and third binary blocks are diagonal, while the middle one is
\[
6\cdot X_1^6-15\cdot X_1^4\cdot Y_1^2
+9\cdot X_1^2\cdot Y_1^4+Y_1^6.
\]
The target \(A=X_0\cdot X_1\cdot X_2^3\cdot Y_1\) involves all three blocks. This makes it a useful test of how a construction can use one pair actively, take a multiplier from another, and still accommodate a third coordinate with a different exponent.

The middle coefficients have a concrete organizing relation. With \(u=X_1^2\), \(w=Y_1^2\), and \(L=u-2\cdot w\), the binary cubic equals
\[
7\cdot(u-w)^3-L^3.
\]
The change of quadratic coordinates is invertible. Thus the displayed mixed terms conceal a sum of cubes, but exposing that sum is only part of the problem: transport changes the volume density and the divergence equation, while the target is fixed in the original coordinates.

The fiber was selected from a family suggested by an earlier algebraic-coefficient example. Choosing rational parameters asks whether the same structural relation can be realized entirely over \(\mathbb Q\). It is a sharper question than demonstrating another numerical solution with unrelated coefficients.

[Chapter 3](#technical-information/geometric-support) places the surrounding family within the general reflection-support theorem. This entry isolates a small part of that framework where the arithmetic of the adapted coordinates and the distribution of target exponents can be examined explicitly. It is particularly useful for comparing an additive block decomposition with a certificate that crosses those blocks: separation of \(F\) does not mean that the prescribed class separates in the same way.
