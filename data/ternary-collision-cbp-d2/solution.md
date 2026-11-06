# The second character of a contact collision
The denominator is the pullback of a line in the square-coordinate plane:
\[
D=X_1^2-X_0^2-Y_0^2.
\]
For this character, the \(X_0\) component vanishes. The two active components are
\[
N_1=\frac{Y_0}{34}\cdot (21\cdot X_0^2-40\cdot X_1^2+40\cdot Y_0^2),\qquad
N_3=-\frac{X_1}{34}\cdot (4\cdot X_0^2+15\cdot X_1^2-15\cdot Y_0^2).
\]
A useful way to see their tangency is to replace \(X_1^2-Y_0^2\) by \(D+X_0^2\). Then
\[
N_1=\frac{Y_0}{34}\cdot (-19\cdot X_0^2-40\cdot D),\qquad
N_3=-\frac{X_1}{34}\cdot (19\cdot X_0^2+15\cdot D).
\]
Consequently
\[
N(D)=-\frac{25}{17}\cdot X_1\cdot Y_0\cdot D,
\qquad \operatorname{div}N=-\frac{25}{17}\cdot X_1\cdot Y_0.
\]
The logarithmic condition is therefore visible without expanding the sextic. The other strict equation, \(N(F)=A\cdot D\), follows by differentiating the exact ternary block in the record.

## What the collision accomplishes
This quadric arises from a degenerating contact configuration of the underlying ternary cubic. The collision makes a low-degree polar divisor available, while the choice of character decides which numerator slots and target sector it reaches. This is why it is recorded separately from the first-character collision.

The exact degree-three tuple and quadratic denominator give a strict rational certificate. The result concerns the displayed collision fiber and target, not all ternary cubics or all characters of this one.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{1}&=\frac{Y_{0}\cdot \left(21\cdot X_{0}^{2} - 40\cdot X_{1}^{2} + 40\cdot Y_{0}^{2}\right)}{34}\\
N_{3}&=- \frac{X_{1}\cdot \left(4\cdot X_{0}^{2} + 15\cdot X_{1}^{2} - 15\cdot Y_{0}^{2}\right)}{34}
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
