# A contact conic in the square-coordinate plane
Let \(u=X_0^2\), \(x=X_1^2\), and \(w=Y_0^2\). The active cubic is \(u^3+x^3+w^3+u\cdot x\cdot w\). On the conic \(u^2=x\cdot w\), use the parametrization
\[
(u,x,w)=(s\cdot r,s^2,r^2).
\]
Its restriction is \(s^6+2\cdot s^3\cdot r^3+r^6=(s^3+r^3)^2\). The square restriction is the contact phenomenon. Pulling the conic back gives, up to sign,
\[
D=X_0^4-X_1^2\cdot Y_0^2.
\]

## An explicit three-component field
For \(A=X_0^3\cdot Y_0^3-\frac53\cdot X_0\cdot X_1^4\cdot Y_0\), choose
\[
N_0=\frac16\cdot (X_0^2\cdot Y_0^3-X_1^4\cdot Y_0),\quad
N_1=\frac13\cdot X_0\cdot X_1\cdot Y_0^3,\quad
N_3=-\frac13\cdot X_0^3\cdot X_1^2.
\]
The coefficient \(-5/3\) is dictated by the contact construction. It is the target combination for which differentiating the sextic factors through \(D\). Direct expansion gives \(N(F)=A\cdot D\), and differentiating the denominator gives \(N(D)=D\cdot\operatorname{div}N\). These are strict equalities, not congruences modulo \(F\).

## Scope of the construction
This example belongs to the Hesse contact-conic family and supplies a degree-four denominator for the stated target. The square restriction explains the divisor; the rational numerator certifies the particular target. Neither statement says that each monomial in the bundle is separately solved by this same construction, or that every Hesse parameter has this rational contact conic.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{0}\cdot \left(X_{0}\cdot Y_{0} - X_{1}^{2}\right)\cdot \left(X_{0}\cdot Y_{0} + X_{1}^{2}\right)}{6}\\
N_{1}&=\frac{X_{0}\cdot X_{1}\cdot Y_{0}^{3}}{3}\\
N_{3}&=- \frac{X_{0}^{3}\cdot X_{1}^{2}}{3}
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
