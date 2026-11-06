# Combine an active correction with passive radial motion
For \(A=X_0^3\cdot Y_0\cdot Y_1\cdot Y_2\), take
\[
D=\frac78\cdot X_1^6+\frac{27}{32}\cdot (X_2^6+Y_0^6+Y_2^6).
\]
The numerator consists of two active corrections and four radial terms:
\[
N_0=-\frac3{64}\cdot X_1^2\cdot Y_0\cdot Y_1^3\cdot Y_2,\qquad
N_4=\frac1{64}\cdot X_0\cdot X_1^4\cdot Y_0\cdot Y_2,
\]
\[
(N_1,N_2,N_3,N_5)=\frac9{64}\cdot A(X_1,X_2,Y_0,Y_2).
\]
The active corrections compensate for differentiating the mixed tie. The radial part is chosen to scale the pure sixth powers in the denominator with a common weight.

## Divergence explains the coefficients
Each denominator coordinate has radial coefficient \(9\cdot A/64\), so
\[
N(D)=\frac{27}{32}\cdot A\cdot D.
\]
The divergence of the radial part is also \(27\cdot A/32\): the two coordinates absent from \(A\) contribute once each, while \(Y_0,Y_2\), already present in \(A\), contribute twice each. The other two components have zero derivative in their own slots. Thus \(D\cdot\operatorname{div}N=N(D)\).

The remaining equality \(N(F)=A\cdot D\) follows from cancellation between the two active corrections and the derivatives of the tie and pure sixth powers. This gives a strict degree-six denominator and degree-seven numerator tuple.

## The useful principle
Multiplying a field by a target monomial changes its divergence. Here that change is deliberately balanced by choosing the radial coordinates and their weights. The construction serves the displayed three-odd-coordinate target, rather than establishing a blanket statement about every odd monomial on the tied sextic.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=- \frac{3\cdot X_{1}^{2}\cdot Y_{0}\cdot Y_{1}^{3}\cdot Y_{2}}{64}\\
N_{1}&=\frac{9\cdot X_{0}^{3}\cdot X_{1}\cdot Y_{0}\cdot Y_{1}\cdot Y_{2}}{64}\\
N_{2}&=\frac{9\cdot X_{0}^{3}\cdot X_{2}\cdot Y_{0}\cdot Y_{1}\cdot Y_{2}}{64}\\
N_{3}&=\frac{9\cdot X_{0}^{3}\cdot Y_{0}^{2}\cdot Y_{1}\cdot Y_{2}}{64}\\
N_{4}&=\frac{X_{0}\cdot X_{1}^{4}\cdot Y_{0}\cdot Y_{2}}{64}\\
N_{5}&=\frac{9\cdot X_{0}^{3}\cdot Y_{0}\cdot Y_{1}\cdot Y_{2}^{2}}{64}
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
