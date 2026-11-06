# Localize the contact construction to the second block
The active variables are \((X_2,Y_1,Y_2)\). Their sextic block has the same form as a Hesse cubic in their squares. The chosen target and denominator are
\[
A=X_2^3\cdot Y_1^3-\frac53\cdot X_2\cdot Y_1\cdot Y_2^4,\qquad D=X_2^4-Y_1^2\cdot Y_2^2.
\]
The contact-conic identity underlying this divisor is the same square restriction \((s^3+r^3)^2\) that occurs for a single three-coordinate tie. Here it is applied in the second block, while the first block remains unchanged.

The numerator has exactly three active components:
\[
N_2=\frac16\cdot (X_2^2\cdot Y_1^3-Y_1\cdot Y_2^4),\quad
N_4=-\frac13\cdot X_2^3\cdot Y_2^2,\quad
N_5=\frac13\cdot X_2\cdot Y_1^3\cdot Y_2.
\]
Since it differentiates none of the variables in the first block, that block contributes nothing to \(N(F)\). The identities reduce to the three-variable calculation: \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\).

## Why this is a separate instance
The construction survives an additional deformation because the second tie is disjoint from the active coordinates. This is a precise stability mechanism, not a general claim that extra mixed terms are harmless. A term crossing the two active blocks could contribute to \(N(F)\) and destroy the equality.

The resulting quartic supplies a strict certificate for this target. The explicit tuple records both the active-block mechanism and its exact boundary of applicability.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{2}&=\frac{Y_{1}\cdot \left(X_{2}\cdot Y_{1} - Y_{2}^{2}\right)\cdot \left(X_{2}\cdot Y_{1} + Y_{2}^{2}\right)}{6}\\
N_{4}&=- \frac{X_{2}^{3}\cdot Y_{2}^{2}}{3}\\
N_{5}&=\frac{X_{2}\cdot Y_{1}^{3}\cdot Y_{2}}{3}
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
