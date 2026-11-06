# A rotation field with a radial denominator
The denominator and numerator are unusually small:
\[
D=4\cdot (X_0^2+Y_0^2),\qquad
N=(-Y_0\cdot X_1^2,0,0,X_0\cdot X_1^2,0,0).
\]
This is an infinitesimal rotation in the \((X_0,Y_0)\) plane, multiplied by the passive square \(X_1^2\). Rotation preserves \(X_0^2+Y_0^2\), hence \(N(D)=0\). It also has zero divergence.

## The target comes from a difference of partial derivatives
Let \(u=X_0^2\), \(w=Y_0^2\), keeping the other variables fixed. The sextic's active dependence obeys
\[
F_u-F_w=-2\cdot (u-w)\cdot (u+w).
\]
Applying the rotation field therefore gives
\[
N(F)=2\cdot X_0\cdot Y_0\cdot X_1^2\cdot (F_w-F_u)
=4\cdot X_0\cdot Y_0\cdot X_1^2\cdot (u-w)\cdot (u+w)=A\cdot D.
\]
Since both divergence and the normal derivative of \(D\) vanish, the field \(N/D\) gives a strict certificate immediately.

## Why the example is informative
The proof depends on a rotation identity and two reflection symmetries, not on invariance under all individual coordinate sign changes. Smoothness and primitivity of the target are independent of the displayed real slice and of the short vector-field calculation.

The small quadric is a genuine legal polar divisor, not a factor extracted from the sextic. Its usefulness comes from being a first integral of the chosen field. The calculation establishes this particular target; it does not solve all targets in the two-reflection sector.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=- X_{1}^{2}\cdot Y_{0}\\
N_{3}&=X_{0}\cdot X_{1}^{2}
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
