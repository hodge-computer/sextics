# A second rational companion
The active cubic in squared coordinates is \(u^3+2\cdot u^2\cdot w+3\cdot u\cdot w^2+w^3\), and the target is
\[
A=X_0^3\cdot Y_0^2\cdot Y_1+\frac97\cdot X_0\cdot Y_0^4\cdot Y_1.
\]
Writing \(L=X_0^2+Y_0^2\), the denominator is the cyclotomic cofactor
\[
D=L^2-L\cdot Y_1^2+Y_1^4,\qquad
(L+Y_1^2)D=L^3+Y_1^6.
\]
This identity organizes the cancellations in the numerator. Only the \(X_0,Y_0,Y_1\) components are nonzero:
\[
\begin{aligned}
N_0&=\frac{Y_1}{14}\cdot (X_0^2\cdot Y_0^2+Y_0^4-Y_0^2\cdot Y_1^2+Y_1^4),\\
N_3&=\frac17\cdot X_0\cdot Y_0\cdot Y_1\cdot (L-Y_1^2),\\
N_4&=-\frac1{14}\cdot X_0\cdot (X_0^2-2\cdot Y_0^2)L.
\end{aligned}
\]
All other sixth powers are spectators. Substituting this tuple into the two strict equations verifies \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\). The term \(9/7\) in the target is precisely the coefficient compatible with these cancellations at this fiber.

## From a search to an intelligible witness
The displayed field satisfies both the derivative identity and the strict divergence identity. The final witness makes the mechanism transparent: a cubic identity in quadratic quantities, followed by a low-degree field tangent to its polar divisor. This is a separate specialization of the companion mechanism, not a statement that any choice of binary-cubic coefficients works unchanged.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{1}\cdot \left(X_{0}^{2}\cdot Y_{0}^{2} + Y_{0}^{4} - Y_{0}^{2}\cdot Y_{1}^{2} + Y_{1}^{4}\right)}{14}\\
N_{3}&=\frac{X_{0}\cdot Y_{0}\cdot Y_{1}\cdot \left(X_{0}^{2} + Y_{0}^{2} - Y_{1}^{2}\right)}{7}\\
N_{4}&=- \frac{X_{0}\cdot \left(X_{0}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(X_{0}^{2} + Y_{0}^{2}\right)}{14}
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
