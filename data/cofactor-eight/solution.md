# Work in a quadratic–cubic coordinate map
Define
\[
C=X_0^2+X_0\cdot X_1+2\cdot X_1^2+X_2^2-2\cdot Y_0^2,
\]
\[
r=Y_0\cdot \left(X_0^2+X_0\cdot X_1+X_1^2+X_2^2-\frac32\cdot Y_0^2\right),\quad
J=C_{X_0}r_{Y_0}-C_{Y_0}r_{X_0}.
\]
In adapted coordinates the sextic is
\[
F=C^3+C\cdot X_1^2\cdot X_2^2+X_1^6+X_2^6+4\cdot r^2+K,\quad
K=Y_1^6+Y_1^4\cdot Y_2^2+Y_2^6.
\]
Use \(D=r^2+K/4\) and target \(A=J\cdot C\cdot Y_1\).

## Weighted Euler motion and cofactor transport
In the adapted coordinates, \((r/2)\partial_r+(Y_1/6)\partial_{Y_1}+(Y_2/6)\partial_{Y_2}\) scales \(D\) by one and leaves the complementary terms fixed. Multiplying by the appropriate density and applying the adjugate Jacobian gives
\[
N_0=-\frac18\cdot C\cdot Y_1\cdot r C_{Y_0},\quad N_3=\frac18\cdot C\cdot Y_1\cdot r C_{X_0},\quad
N_4=\frac1{24}\cdot A\cdot Y_1,\quad N_5=\frac1{24}\cdot A\cdot Y_2.
\]
The remaining components vanish. In particular \(N(C)=0\), and the two active cofactor terms give \(N(r)=A\cdot r/8\). It follows that \(N(D)=A\cdot D/4\), \(N(F)=A\cdot D\), and Piola's divergence identity gives \(\operatorname{div}N=A/4\). Thus the strict equations hold with the displayed normalization.

## A packet, not just one target
The same mechanism serves the eight directions
\[
J\,\langle C,X_1^2,X_1\cdot X_2,X_2^2\rangle\,\langle Y_1,Y_2\rangle.
\]
The card chooses one member of that packet. The Jacobian factor is not incidental: it is the density created by transport. Dropping it would change the target and invalidate the derivation.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{0}^{2}\cdot Y_{1}\cdot \left(X_{0}^{2} + X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + X_{2}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + 2\cdot X_{2}^{2} - 3\cdot Y_{0}^{2}\right)}{4}\\
N_{3}&=\frac{Y_{0}\cdot Y_{1}\cdot \left(2\cdot X_{0} + X_{1}\right)\cdot \left(X_{0}^{2} + X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + X_{2}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + 2\cdot X_{2}^{2} - 3\cdot Y_{0}^{2}\right)}{16}\\
N_{4}&=\frac{Y_{1}^{2}\cdot \left(2\cdot X_{0} + X_{1}\right)\cdot \left(X_{0}^{2} + X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + X_{2}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + 2\cdot X_{2}^{2} - Y_{0}^{2}\right)}{48}\\
N_{5}&=\frac{Y_{1}\cdot Y_{2}\cdot \left(2\cdot X_{0} + X_{1}\right)\cdot \left(X_{0}^{2} + X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + X_{2}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} + 2\cdot X_{2}^{2} - Y_{0}^{2}\right)}{48}
\end{aligned}
\]


## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof checks the certificate identity, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\).

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
