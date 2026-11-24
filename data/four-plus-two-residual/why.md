This example has the additive decomposition

\[
F=H(X_0,X_1,Y_0,Y_1)+B(X_2,Y_2),
\qquad
B(s,t)=s^6+\frac{15}{7}s^4t^2+\frac{10}{7}s^2t^4+t^6.
\]

The four-variable core is coupled, while the binary factor is separately even. The target is \(q=1\), \(A=X_0^3Y_0^3\). It is even in each binary coordinate, so its residue is anti-invariant under both coordinate reflections. The ordinary reflection quotients serve the complementary sectors.

The [two-reflection theorem of Chapter 3B](../../docs/03b-weighted-threefolds.md) supplies divisor support for the entire globally invariant fourth cohomology of this fourfold. Its hypotheses hold directly: the protected equation is globally \(Y\)-even and separately even in \(X_2\) and \(Y_2\), and reduction modulo five is the smooth Fermat sextic. The support-to-certificate theorem therefore establishes rational certificate existence for this exact target.

The geometric input is the anti-invariant third cohomology of a weighted sextic threefold in \(\mathbb P(1,1,1,1,2)\). In the split presentation, the natural example is \(T:u^3=H\). Weighted adjunction gives trivial canonical class, so the earlier Fano companion argument does not apply directly. Chapter 3B constructs norm-contact curves, proves that their Abel–Jacobi differentials span, and specializes the resulting supported projector before transferring support to the fourfold.

Although [symmetric-sextic-residual](../symmetric-sextic-residual/solution.md) is proved mathematically by the same two-reflection theorem, its constructive [§3B.11](../../docs/03b-weighted-threefolds.md#3b11-moving-lines-on-a-cubic-threefold-and-global-residue-cancellation) solution relies on its \(S_3\times S_3\) symmetry to collapse the fourfold to a conic bundle over a cubic surface. Here the core \(H(X_0,X_1,Y_0,Y_1)\) retains only the involution \(\sigma:(Y_0,Y_1)\mapsto(-Y_0,-Y_1)\) as a projective diagonal symmetry, and its binary boundary sextics \(H(X_0,X_1,0,0)\) and \(H(0,0,Y_0,Y_1)\) are irreducible over \(\mathbb Q\) with Galois group \(S_6\). On the four-variable core, setting \(V=(v_{X_0},v_{X_1},\tfrac14 X_2\operatorname{div}v,v_{Y_0},v_{Y_1},\tfrac14 Y_2\operatorname{div}v)\) gives the exact [§2.8 suspension reduction](../../docs/02-explicit-constructions.md#28-a-cyclic-quotient-and-its-density-character) \(2A-2dH(v)+3H\operatorname{div}(v)=0\) with no \(F^2\) remainder, isolating the problem on \(H\); without extra symmetry to split the \(96\)-dimensional anti-invariant cohomology \(H^3(T,\mathbb Q)^-\) (\(h^{2,1}=48\)), however, any curve correspondence on \(T\) spanning it requires a parameter curve of genus at least \(48\).

The additive split makes the weighted core and its residue character especially visible. The theorem also allows couplings between the two reflected coordinates and the core: support depends on the two reflections and the weighted-threefold correspondence, rather than on this particular additive presentation. An explicit rational primitive is a further algebraic realization of that established support.
