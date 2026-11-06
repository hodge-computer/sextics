# Pull back the Hesse cofactor
Take \(x=X_0\), \(y=X_2\), \(R=Y_2^2\), and \(B=X_1\cdot Y_1\). In the Hesse identity use \((u,v,w)=(x^2,y^2,-R/3)\). The denominator is the corresponding quartic cofactor
\[
D=u^2+v^2+w^2-u\cdot v-u\cdot w-v\cdot w.
\]
The chosen field has only two nonzero components:
\[
N_0=\frac{B X_2}{18}\cdot (3\cdot X_2^2+Y_2^2),\qquad
N_2=\frac{X_0\cdot B}{6}\cdot (X_2^2-X_0^2).
\]
Here \(B\) and \(R\) are passive for the active differentiation.

## Why a complicated passive block does not obstruct the field
The sextic contains the non-diagonal passive expression
\[
5\cdot X_1^6+21\cdot X_1^4\cdot Y_1^2+30\cdot X_1^2\cdot Y_1^4+14\cdot Y_1^6+Y_0^6+Y_2^6.
\]
Its coefficients look unrelated to a Fermat formula, but the field differentiates neither \(X_1\), \(Y_1\), \(Y_0\), nor \(Y_2\). This entire part therefore disappears from \(N(F)\). What remains is the Hesse-cofactor calculation in the active pair. The resulting identities are \(N(F)=A\cdot D\) and \(N(D)=D\cdot\operatorname{div}N\).

This is the practical value of identifying a passive block: complexity there need not increase the denominator degree. It is a statement about a field's derivatives, not about the apparent number of terms in the sextic.

## Scope
The explicit tuple supplies a strict quartic certificate for this target. The result applies to the selected Hesse-compatible active part; arbitrary mixed terms involving the active coordinates would require a new verification.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}\cdot Y_{1}\cdot \left(3\cdot X_{2}^{2} + Y_{2}^{2}\right)}{18}\\
N_{2}&=- \frac{X_{0}\cdot X_{1}\cdot Y_{1}\cdot \left(X_{0} - X_{2}\right)\cdot \left(X_{0} + X_{2}\right)}{6}
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
