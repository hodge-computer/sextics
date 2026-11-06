# Move the passive variables inside the quadratic map
Use
\[
C=X_0^2+X_0\cdot X_1+2\cdot X_1^2-2\cdot Y_0^2+Y_1^2+Y_2^2,
\]
\[
r=Y_0\cdot \left(X_0^2+X_0\cdot X_1+X_1^2-\frac32\cdot Y_0^2+Y_1^2+Y_2^2\right),\qquad
J=C_{X_0}r_{Y_0}-C_{Y_0}r_{X_0}.
\]
The adapted sextic has form \(F=H(C,X_1,Y_1,Y_2)+4\cdot r^2+X_2^6\). The selected denominator is \(D=4\cdot r^2+X_2^6\), with target \(A=JX_2^2\cdot Y_1\).

## Pull back a weighted radial field
Only \(r\) and \(X_2\) move in the adapted coordinates. Their weights are \(1/2\) and \(1/6\), making both \(4\cdot r^2\) and \(X_2^6\) scale equally. Cofactor transport gives
\[
N_0=-\frac12\cdot X_2^2\cdot Y_1\cdot r C_{Y_0},\quad
N_3=\frac12\cdot X_2^2\cdot Y_1\cdot r C_{X_0},\quad
N_2=\frac16\cdot A\cdot X_2.
\]
The cofactor pair preserves \(C\), and \(N(r)=A\cdot r/2\). Consequently \(N(H)=0\), \(N(D)=A\cdot D\), and \(N(F)=A\cdot D\). The density and radial weights also give \(\operatorname{div}N=A\), so the rational field is divergence-free.

## Why this survives mixed blocks
The method uses an adapted-coordinate first integral \(C\), not an assumption that \(C\) contains only \(X\)-variables. Its dependence on \(Y_1,Y_2\) is harmless because those coordinates remain fixed by the field. The passive factors \(Y_1\) and \(Y_2\) give two target directions; this instance uses the first. Arbitrary new active dependence in \(H\) would require checking the invariant condition again.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=X_{2}^{2}\cdot Y_{0}^{2}\cdot Y_{1}\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} - 3\cdot Y_{0}^{2} + 2\cdot Y_{1}^{2} + 2\cdot Y_{2}^{2}\right)\\
N_{2}&=\frac{X_{2}^{3}\cdot Y_{1}\cdot \left(2\cdot X_{0} + X_{1}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} - Y_{0}^{2} + 2\cdot Y_{1}^{2} + 2\cdot Y_{2}^{2}\right)}{12}\\
N_{3}&=\frac{X_{2}^{2}\cdot Y_{0}\cdot Y_{1}\cdot \left(2\cdot X_{0} + X_{1}\right)\cdot \left(2\cdot X_{0}^{2} + 2\cdot X_{0}\cdot X_{1} + 2\cdot X_{1}^{2} - 3\cdot Y_{0}^{2} + 2\cdot Y_{1}^{2} + 2\cdot Y_{2}^{2}\right)}{4}
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
