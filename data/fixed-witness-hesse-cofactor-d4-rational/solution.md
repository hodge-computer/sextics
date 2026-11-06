# Reveal a hidden cubic identity
Introduce three quadratic forms
\[
u=X_0^2,\qquad v=X_2^2-2\cdot X_0^2,\qquad w=X_1^2+X_0^2.
\]
Set \(Q=u^2+v^2+w^2-u\cdot v-u\cdot w-v\cdot w\). In this specialization the displayed quartic satisfies \(Q=9\cdot D\), and
\[
u^3+v^3+w^3-3\cdot u\cdot v\cdot w=(u+v+w)Q.
\]
Thus a Hesse factorization becomes available after a nontrivial quadratic substitution. In the original coordinates it is easy to miss this structure among the expanded mixed terms.

## Transport the field, including its density
Use Piola transport through the quadratic coordinate map. This is the adjugate-Jacobian version of pulling back a vector field: the Jacobian determinant supplies the density needed to transport divergence correctly. A naive substitution of vector components would not preserve the second certificate equation.

The resulting numerator has nonzero components only in the three \(X\) slots. It realizes the fixed target \(X_0\cdot X_1\cdot X_2^3\cdot Y_1\), and satisfies \(N(F)=A\cdot D\), \(D\cdot\operatorname{div}N=N(D)\). The exact tuple is retained below, so the transport argument can be replaced by direct polynomial differentiation at this fiber.

## Two useful denominators, one displayed witness
Subtracting \((u+v+w)9\cdot D\) from \(F\) exposes a complementary sextic denominator used in an alternative construction. That alternative helps explain the family but is not the displayed quartic witness. The record deliberately retains the quartic construction for this fixed target. The quartic witness establishes existence for this target; it does not give a universal denominator bound for the quadratic-map family.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}\cdot Y_{1}\cdot \left(3\cdot X_{0}^{2} - X_{1}^{2} - X_{2}^{2}\right)}{54}\\
N_{1}&=- \frac{X_{0}\cdot X_{2}\cdot Y_{1}\cdot \left(3\cdot X_{0}^{2} - X_{1}^{2} - X_{2}^{2}\right)}{54}\\
N_{2}&=\frac{X_{0}\cdot X_{1}\cdot Y_{1}\cdot \left(3\cdot X_{0}^{2} - 4\cdot X_{1}^{2} - X_{2}^{2}\right)}{54}
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
