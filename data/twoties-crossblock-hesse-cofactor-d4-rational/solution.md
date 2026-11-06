# Use the second tie and keep the multiplier passive
Choose active coordinates \(x=X_2\), \(y=Y_2\), passive quadratic \(R=Y_1^2\), and multiplier \(B=Y_0\cdot Y_1\). The denominator is the Hesse cofactor in
\[
(u,v,w)=(X_2^2,Y_2^2,-Y_1^2/3).
\]
Only two components are nonzero:
\[
N_2=\frac16\cdot Y_0\cdot Y_1\cdot Y_2\cdot (X_2^2-Y_2^2),\qquad
N_5=\frac16\cdot X_2\cdot Y_0\cdot Y_1\cdot \left(X_2^2+\frac13\cdot Y_1^2\right).
\]
They realize \(A=X_2^3\cdot Y_0\cdot Y_1\cdot Y_2\). Although \(Y_1\) appears in the tie and in the multiplier, neither active component differentiates it. Thus it is genuinely passive for this field.

## The two strict equations
The cubic Hesse factorization supplies the quartic cofactor, and differentiation gives \(N(F)=A\cdot D\). The numerator is logarithmic along that divisor, with \(N(D)=D\cdot\operatorname{div}N\). Both identities can be checked directly from the two displayed components. The first tied block contributes nothing because the field has no derivative in its coordinates.

For this fixed denominator, the numerator can also be found by equating polynomial coefficients in both strict identities. The exact witness below gives a solution; the second equation is essential to this calculation.

## Boundary of the conclusion
The mechanism works because the apparent cross-block complexity sits in a passive multiplier. An additional coupling involving the active pair would change the derivative calculation and cannot be declared solved from this witness alone.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{2}&=\frac{Y_{0}\cdot Y_{1}\cdot Y_{2}\cdot \left(X_{2} - Y_{2}\right)\cdot \left(X_{2} + Y_{2}\right)}{6}\\
N_{5}&=\frac{X_{2}\cdot Y_{0}\cdot Y_{1}\cdot \left(3\cdot X_{2}^{2} + Y_{1}^{2}\right)}{18}
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
