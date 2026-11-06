# Contact geometry supplies a quadric
Put \((u,w,x)=(X_0^2,Y_0^2,X_1^2)\). The relevant line is
\[
\ell=u-2\cdot w+x=0,\qquad D=X_0^2-2\cdot Y_0^2+X_1^2.
\]
In the plane cubic, this line is tangent at \((1:1:1)\), with residual intersection \((2:1:0)\). The residual point lies on the coordinate line \(x=0\), a condition that interacts favorably with the square-coordinate pullback. Parametrize \(\ell\) by
\[
(u,w,x)=(s+2\cdot r,s+r,s).
\]
The cubic restricts to \(-\frac52\cdot s\cdot r^2\). The repeated factor exhibits tangency, and the remaining factor records the residual intersection. Thus the contact information is an exact polynomial identity.

## Turning contact into a strict field
Pulling \(\ell\) back gives a degree-two denominator. The construction supplies a degree-three numerator supported in the three active coordinate slots. The numerator is logarithmic along this quadric: its normal derivative \(N(D)\) equals \(D\cdot\operatorname{div}N\). Simultaneously its derivative of the sextic is \(A\cdot D\). The exact tuple below makes both statements directly checkable.

The first identity realizes the requested target; the second removes the extra term created when differentiating \(N/D\). Contact geometry suggests the divisor, but these algebraic equalities are what establish the certificate.

## Extent of the result
The special tangent/residual configuration is a genuine hypothesis; an arbitrary tangent to an arbitrary ternary cubic need not give this same field.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{Y_{0}\cdot \left(41\cdot X_{0}^{2} + 33\cdot X_{1}^{2} - 78\cdot Y_{0}^{2}\right)}{150}\\
N_{1}&=- \frac{2\cdot X_{0}\cdot X_{1}\cdot Y_{0}}{75}\\
N_{3}&=- \frac{X_{0}\cdot \left(24\cdot X_{0}^{2} + 27\cdot X_{1}^{2} - 49\cdot Y_{0}^{2}\right)}{75}
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
