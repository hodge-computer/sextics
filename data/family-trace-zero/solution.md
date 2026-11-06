# A trace-zero rotation inside a cubic complement
Let
\[
U=X_0^2+Y_0^2,\quad V=X_0^2-Y_0^2,\quad Q=\frac{101}{103}\cdot (X_1^2+Y_1^2).
\]
Then
\[
F=U(U^2+V^2+Q^2)+D,\qquad D=2\cdot X_1^6+3\cdot X_2^6+5\cdot Y_1^6+7\cdot Y_2^6.
\]
The cubic complement is a line times a conic. The trace-zero derivation \(Q\partial_V-V\partial_Q\) preserves \(V^2+Q^2\), giving the basic invariant behind the construction.

## A flux in adapted coordinates
Use \(\Phi=(U,V,X_1,X_2,Y_1,Y_2)\), whose Jacobian determinant is \(\Delta=-8\cdot X_0\cdot Y_0\), and put \(B=X_1^2\). The target-space flux is
\[
P=\left(0,\frac{Q^2\cdot B}{3},-\frac{V\cdot B\cdot X_1}{6},-\frac{V\cdot B\cdot X_2}{6},-\frac{V\cdot B\cdot Y_1}{6},-\frac{V\cdot B\cdot Y_2}{6}\right).
\]
It annihilates the cubic complement, scales \(D\) by the density \(-V\cdot B\), and has divergence \(-V\cdot B\). The derivatives of \(Q\), including its dependence on passive coordinates, are included in this calculation.

Piola transport \(N=\operatorname{adj}(d\Phi)P(\Phi)\) gives
\[
A=\Delta(-V\cdot B)=8\cdot X_0\cdot Y_0\cdot (X_0^2-Y_0^2)X_1^2.
\]
The chain rule and Piola identity then give \(N(F)=N(D)=A\cdot D\) and \(\operatorname{div}N=A\).

## What is new in the mechanism
The complement need not be a triangle of linear forms in quadratic coordinates. A trace-zero action preserving a conic is enough. But the precise invariant/eigenfunction decomposition and the Jacobian density remain essential. The explicit tuple provides a strict certificate for this specialization, without claiming that every line–conic decomposition serves every target.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=- \frac{20402\cdot X_{1}^{2}\cdot Y_{0}\cdot \left(X_{1}^{2} + Y_{1}^{2}\right)^{2}}{31827}\\
N_{1}&=\frac{4\cdot X_{0}\cdot X_{1}^{3}\cdot Y_{0}\cdot \left(X_{0} - Y_{0}\right)\cdot \left(X_{0} + Y_{0}\right)}{3}\\
N_{2}&=\frac{4\cdot X_{0}\cdot X_{1}^{2}\cdot X_{2}\cdot Y_{0}\cdot \left(X_{0} - Y_{0}\right)\cdot \left(X_{0} + Y_{0}\right)}{3}\\
N_{3}&=\frac{20402\cdot X_{0}\cdot X_{1}^{2}\cdot \left(X_{1}^{2} + Y_{1}^{2}\right)^{2}}{31827}\\
N_{4}&=\frac{4\cdot X_{0}\cdot X_{1}^{2}\cdot Y_{0}\cdot Y_{1}\cdot \left(X_{0} - Y_{0}\right)\cdot \left(X_{0} + Y_{0}\right)}{3}\\
N_{5}&=\frac{4\cdot X_{0}\cdot X_{1}^{2}\cdot Y_{0}\cdot Y_{2}\cdot \left(X_{0} - Y_{0}\right)\cdot \left(X_{0} + Y_{0}\right)}{3}
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
