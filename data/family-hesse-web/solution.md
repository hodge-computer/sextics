# Three contact channels over a cubic algebra
Put \(u=X_0^2\), \(w=Y_0^2\), \(x=X_1^2\), and \(a=u+w\). The active cubic is \(u^3+w^3+x^3+t\cdot u\cdot w\cdot x\), with \(t=-2\). The relevant contact parameters are roots of
\[
C^3-t\cdot C^2-4=0.
\]
The product of the three corresponding linear forms is rational:
\[
\operatorname{Norm}(a+C\cdot x)=a^3+t a^2\cdot x+4\cdot x^3=D.
\]
It has degree six after returning to the original coordinates.

## Contact conics explain the parameters
The associated conics have parameter \(\kappa=2/C\), satisfying \(\kappa^3+t\kappa=2\). Under their parametrization the cubic restricts to a square \((s^3+r^3)^2\). This contact identity gives logarithmic fields over the cubic coefficient algebra. The construction combines the three ordinary tangent channels through \((-1:1:0)\); the fourth, flex channel has zero coefficient in the selected solution.

Tracing the resulting rational fields gives a field over \(\mathbb Q\) for the target \(A=X_0^3\cdot Y_0^3\). Clearing the common norm denominator yields the literal degree-seven tuple retained in the record. It satisfies \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\).

## Why this is more than a factorization
Knowing the norm denominator alone is not enough. The weights of the contact channels must make their derivatives combine into the prescribed target and make their divergences cancel. The exact numerator is the evidence for that compatibility. The construction proves a strict certificate on this Hesse fiber; it does not imply that a rational contact conic exists individually, or that the norm degree is minimal.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{0}\cdot \left(2\cdot X_{0}^{4}\cdot X_{1}^{2} + 3\cdot X_{0}^{4}\cdot Y_{0}^{2} + 2\cdot X_{0}^{2}\cdot X_{1}^{2}\cdot Y_{0}^{2} + 6\cdot X_{0}^{2}\cdot Y_{0}^{4} - 6\cdot X_{1}^{6} + 3\cdot Y_{0}^{6}\right)}{18}\\
N_{1}&=\frac{X_{0}\cdot X_{1}\cdot Y_{0}\cdot \left(X_{0}^{2} + Y_{0}^{2}\right)\cdot \left(3\cdot X_{0}^{2} - 2\cdot X_{1}^{2} + 3\cdot Y_{0}^{2}\right)}{9}\\
N_{3}&=\frac{X_{0}\cdot \left(3\cdot X_{0}^{6} + 6\cdot X_{0}^{4}\cdot Y_{0}^{2} + 2\cdot X_{0}^{2}\cdot X_{1}^{2}\cdot Y_{0}^{2} + 3\cdot X_{0}^{2}\cdot Y_{0}^{4} - 6\cdot X_{1}^{6} + 2\cdot X_{1}^{2}\cdot Y_{0}^{4}\right)}{18}
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
