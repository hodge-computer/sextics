# Expose a product with opposite weights
Take the weighted coordinate map
\[
\Phi=(X_0,T,X_1^2,Y_0,Y_1,Y_2),\qquad
T=X_0^5+2\cdot X_0^3\cdot Y_0^2+3\cdot X_0\cdot Y_0^4+X_2^5.
\]
In target coordinates the sextic is a product of the first two coordinates plus a complementary weighted sextic. Give those first two coordinates opposite infinitesimal weights so that the product is invariant.

With \(R=Y_1\), the target-space flux is
\[
P=\left(\frac{R\cdot X_0}{6},-\frac{R\cdot T}{6},\frac{R\cdot X_1^2}{3},\frac{R\cdot Y_0}{6},\frac{R\cdot Y_1}{6},\frac{R\cdot Y_2}{6}\right).
\]
Here the entries are interpreted as functions of independent target coordinates before substitution. In particular, \(T\) is independent of \(X_0\) when computing the target-space divergence.

## Transport restores the original coordinates
The complementary denominator is an eigenfunction with \(P(D)=R\cdot D\), while \(P(X_0\cdot T)=0\) and \(\operatorname{div}P=R\). Put
\[
\Delta=\det(d\Phi),\qquad N=\operatorname{adj}(d\Phi)P(\Phi),\qquad A=\Delta R.
\]
Piola's identity gives \(\operatorname{div}N=A\), and the chain rule gives \(N(F)=N(D)=A\cdot D\). This yields a strict certificate with the recorded sextic denominator.

## Why the first jet matters
The triangular map makes the polynomial dependence on \(T\) linear in the complement's missing direction. The large shear polynomial therefore does not require solving a general six-variable equation: its Jacobian cofactors perform the transport exactly. Other passive densities may give compatible target directions by the same transport identity. Each choice must satisfy the displayed invariance conditions; arbitrary changes to the product structure or target do not follow automatically.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=- \frac{5\cdot X_{0}\cdot X_{1}\cdot X_{2}^{4}\cdot Y_{1}}{3}\\
N_{1}&=- \frac{5\cdot X_{1}^{2}\cdot X_{2}^{4}\cdot Y_{1}}{3}\\
N_{2}&=\frac{X_{1}\cdot Y_{1}\cdot \left(6\cdot X_{0}^{5} + 12\cdot X_{0}^{3}\cdot Y_{0}^{2} + 18\cdot X_{0}\cdot Y_{0}^{4} + X_{2}^{5}\right)}{3}\\
N_{3}&=- \frac{5\cdot X_{1}\cdot X_{2}^{4}\cdot Y_{0}\cdot Y_{1}}{3}\\
N_{4}&=- \frac{5\cdot X_{1}\cdot X_{2}^{4}\cdot Y_{1}^{2}}{3}\\
N_{5}&=- \frac{5\cdot X_{1}\cdot X_{2}^{4}\cdot Y_{1}\cdot Y_{2}}{3}
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
