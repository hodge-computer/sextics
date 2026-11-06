# The first collision character
Here the contact divisor pulls back to
\[
D=X_0^2-Y_0^2-X_1^2.
\]
Only two numerator components are needed:
\[
N_0=\frac{Y_0}{10}\cdot (5\cdot X_0^2-X_1^2-5\cdot Y_0^2),\qquad
N_3=\frac{X_0}{5}\cdot (5\cdot X_0^2-3\cdot X_1^2-5\cdot Y_0^2).
\]
Equivalently, \(N_0=Y_0\cdot (5\cdot D+4\cdot X_1^2)/10\) and \(N_3=X_0\cdot (5\cdot D+2\cdot X_1^2)/5\). The shared terms immediately give
\[
N(D)=-X_0\cdot Y_0\cdot D,\qquad \operatorname{div}N=-X_0\cdot Y_0.
\]
Thus \(N/D\) is divergence-free. Applying it to the sextic gives the displayed target because the numerator identity is \(N(F)=A\cdot D\).

## The geometric input and the algebraic conclusion
The original sextic is organized as a ternary cubic in \(X_0^2,Y_0^2,X_1^2\), with passive sixth powers. A special collision of the contact configuration identifies the line whose pullback is \(D\). After that discovery, no geometric existence theorem is needed for this witness: the two polynomial identities are a complete direct verification of the field equation.

The other collision character uses different active slots and a different target, which is why it has its own atlas entry. This field establishes a strict degree-two certificate on the displayed fiber. The contact configuration is specific to this cubic and does not classify rational fields on a general ternary sextic.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{0}\cdot \left(5\cdot X_{0}^{2} - X_{1}^{2} - 5\cdot Y_{0}^{2}\right)}{10}\\
N_{3}&=\frac{X_{0}\cdot \left(5\cdot X_{0}^{2} - 3\cdot X_{1}^{2} - 5\cdot Y_{0}^{2}\right)}{5}
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
