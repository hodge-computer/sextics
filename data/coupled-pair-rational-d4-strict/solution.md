# Deform the sextic while retaining a logarithmic field
Start with the two-coordinate Fermat cofactor construction in \(x=X_0\), \(y=Y_0\), with passive multiplier \(B=X_1\cdot X_2\). Its denominator is
\[
D=x^4-x^2\cdot y^2+y^4,
\]
and its numerator satisfies
\[
N(F_0)=A_0\cdot D,\qquad N(D)=D\cdot\operatorname{div}N,\qquad
A_0=x^3\cdot y\cdot B,\quad \operatorname{div}N=\frac{x\cdot y\cdot B}{3}.
\]
Now put \(W=Y_1^2\) and deform by a multiple of the same divisor:
\[
F=F_0+D\cdot W.
\]
The field does not differentiate \(W\). Therefore
\[
N(F)=A_0\cdot D+W N(D)=D\left(A_0+\frac13\cdot x\cdot y\cdot B\cdot W\right).
\]
This is exactly the displayed deformed target \(A\).

## Why the second equation survives
Neither \(N\) nor \(D\) has changed, so their logarithmic divergence identity survives verbatim. The deformation affects only the target in the first equation. This gives a strict certificate on a sextic that is no longer simply the original passive sum.

More generally, a term \(D\cdot W\) with \(N(W)=0\) produces a controlled target change \(W\operatorname{div}N\). The condition on \(W\) is essential; otherwise an additional \(D N(W)\) term enters the numerator equation.

## Significance and limits
The retained tuple makes this a direct transport argument. The construction supports this compatible deformation and target; it does not turn arbitrary deformations of Fermat into solved instances.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}\cdot Y_{0}\cdot \left(X_{0} - Y_{0}\right)\cdot \left(X_{0} + Y_{0}\right)}{6}\\
N_{3}&=\frac{X_{0}^{3}\cdot X_{1}\cdot X_{2}}{6}
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
