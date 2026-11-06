# A Hesse cofactor with a passive multiplier
Use the quadratic quantities
\[
u=X_0^2,\qquad v=Y_1^2,\qquad w=-\frac13\cdot X_1^2.
\]
The Hesse identity
\[
u^3+v^3+w^3-3\cdot u\cdot v\cdot w=(u+v+w)\cdot (u^2+v^2+w^2-u\cdot v-u\cdot w-v\cdot w)
\]
produces the rational quartic
\[
D=18\cdot (u^2+v^2+w^2-u\cdot v-u\cdot w-v\cdot w).
\]
After substitution this is exactly the six-term denominator shown on the instance page. The scale factor 18 clears convenient coefficients without affecting the rational field once the numerator is scaled with it.

## Two active components suffice
For \(A=X_0^3\cdot Y_0^2\cdot Y_1\), take
\[
N_0=3\cdot Y_0^2\cdot Y_1\cdot (X_0^2-Y_1^2),\qquad
N_4=X_0\cdot Y_0^2\cdot (3\cdot X_0^2+X_1^2).
\]
Every other component is zero. The multiplier \(Y_0^2\) is passive: neither active derivative differentiates it. This is why it can accompany the construction without creating a new divergence term.

The Hesse cofactor identity organizes the verification of \(N(F)=A\cdot D\). A second direct calculation gives \(N(D)=D\cdot\operatorname{div}N\), establishing the strict rational certificate. Both numerator components have degree five.

## Scope
The construction shows how a passive factor can extend an active target direction. It does not say that an arbitrary multiplier is passive, or that multiplying by a coordinate differentiated by the field would preserve the same equations.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=3\cdot Y_{0}^{2}\cdot Y_{1}\cdot \left(X_{0} - Y_{1}\right)\cdot \left(X_{0} + Y_{1}\right)\\
N_{4}&=X_{0}\cdot Y_{0}^{2}\cdot \left(3\cdot X_{0}^{2} + X_{1}^{2}\right)
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
