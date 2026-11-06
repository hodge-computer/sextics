# A quadratic norm in squared coordinates
For the binary block \(X_0^6-2\cdot X_0^4\cdot Y_0^2+Y_0^6\), the compatible target is
\[
A=X_0^3\cdot Y_0^2\cdot Y_1-\frac67\cdot X_0\cdot Y_0^4\cdot Y_1.
\]
Let \(L=(X_0^2-2\cdot Y_0^2)/2\). The quartic denominator has the compact form
\[
D=L^2-\frac12\cdot L\cdot Y_1^2+\frac14\cdot Y_1^4.
\]
It is a rational quadratic norm in the two degree-two quantities \(L\) and \(Y_1^2\). Its two conjugate quadratic factors are easier to interpret geometrically than the expanded quartic; their product is defined over \(\mathbb Q\).

## Finding a numerator and checking both equations
To find a numerator, solve the normalized equation \(N(F)=A\cdot D\) over the degree-compatible ansatz. The second equation, \(D\cdot\operatorname{div}N-N(D)=0\), then selects the admissible strict fields. This second screen is essential: a solution of the first equation alone need not be a certificate.

The displayed rational point survives both screens and yields the three nonzero components recorded below. Their degree is five, as required by \(\deg N_i=4+6-5\). Differentiating the exact tuple establishes both identities, with no residual multiple of \(F\).

## What the degree statement means
The displayed witness has a quartic denominator and certifies the fixed target. The quartic result concerns the stated specialization and the strict normalized problem; it does not rule out other non-strict mechanisms in a broader problem.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{1}\cdot \left(5\cdot X_{0}^{2}\cdot Y_{0}^{2} - 10\cdot Y_{0}^{4} - 5\cdot Y_{0}^{2}\cdot Y_{1}^{2} + 2\cdot Y_{1}^{4}\right)}{56}\\
N_{3}&=\frac{X_{0}\cdot Y_{0}\cdot Y_{1}\cdot \left(X_{0}^{2} - 2\cdot Y_{0}^{2} - Y_{1}^{2}\right)}{14}\\
N_{4}&=- \frac{X_{0}\cdot \left(X_{0}^{2} - 2\cdot Y_{0}^{2}\right)\cdot \left(2\cdot X_{0}^{2} - Y_{0}^{2}\right)}{56}
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
