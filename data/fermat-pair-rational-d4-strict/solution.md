# A quartic cofactor of two sixth powers
Write \(x=X_0\), \(y=X_1\), and \(B=X_2\cdot Y_0\). The denominator comes from the elementary factorization
\[
x^6+y^6=(x^2+y^2)D,\qquad D=x^4-x^2\cdot y^2+y^4.
\]
Choose just two nonzero numerator components:
\[
N_x=\frac{B}{6}\cdot y(x^2-y^2),\qquad N_y=\frac{B}{6}\cdot x^3.
\]
The other four coordinates are parameters for this field. Differentiating the Fermat sextic gives
\[
N(F)=B\bigl(x^5\cdot y(x^2-y^2)+x^3\cdot y^5\bigr)=x^3\cdot y\cdot B\,D=A\cdot D.
\]
The second identity is just as important. Direct differentiation yields
\[
\operatorname{div}N=\frac{x\cdot y\cdot B}{3},\qquad N(D)=\frac{x\cdot y\cdot B}{3}\cdot D.
\]
Thus the logarithmic derivative of the denominator exactly matches the divergence of the numerator. Dividing by \(D\) produces a divergence-free rational field whose derivative of \(F\) is \(A\). No remainder is needed.

## What this contributes
The field above gives a strict certificate with a quartic denominator for this target. The Fermat case is treated in [Diamond's paper](https://arxiv.org/abs/2603.29157); the particular quartic witness here is specified and checked in the files linked below.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}\cdot Y_{0}\cdot \left(X_{0} - X_{1}\right)\cdot \left(X_{0} + X_{1}\right)}{6}\\
N_{1}&=\frac{X_{0}^{3}\cdot X_{2}\cdot Y_{0}}{6}
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
