# A weighted split rather than a separated sum
In adapted binary coordinates \(R,S\), the cubic block has the root-cube form \(\alpha\cdot R^3+\kappa\cdot R\cdot S^2\). Write the full sextic as \(F=C+D\) so that the weighted derivation
\[
W=\frac16\cdot (2\cdot R\partial_R-S\partial_S+z\partial_z+w\partial_w)
\]
obeys \(W(C)=0\) and \(W(D)=D\). Crossed-block terms are allowed precisely when they have the required weight. Thus the construction does not require the original polynomial to split into independent variable sets.

## Transport to the prescribed monomial
Piola transport through the quadratic coordinate map, with the appropriate density, gives the target \(A=X_0\cdot X_1\cdot X_2^3\cdot Y_0\). At this specialization the nonzero numerator components simplify to
\[
N_0=\frac1{24}\cdot Y_0\cdot X_1\cdot X_2^3\cdot (X_0^2-3\cdot Y_0^2),\qquad
N_3=\frac1{24}\cdot X_0\cdot X_1\cdot X_2^3\cdot (-3\cdot X_0^2+Y_0^2),
\]
\[
N_2=\frac16\cdot A\cdot X_2,\qquad N_5=\frac16\cdot A\cdot Y_2.
\]
Although the expanded sextic and denominator have many rational terms, this tuple remains short. Its derivatives satisfy \(N(F)=A\cdot D\) and \(N(D)=D\cdot\operatorname{div}N\). The exact expanded denominator is retained in the solution record, so there is no ambiguity about which weighted specialization is being used.

## The constraint behind the flexibility
The numerous crossed terms are not arbitrary perturbations. Their weights make the complementary part invariant and the denominator an eigenfunction of the adapted field. This is the hypothesis that must survive when extending the family. The argument applies to sextics and targets satisfying these weight identities; it supplies no universal denominator-degree bound.

## The retained numerator

In the fixed order \(X_0,X_1,X_2,Y_0,Y_1,Y_2\), the nonzero components are shown below; omitted components are zero. These are the literal rational tuple in the solution record.

\[
\begin{aligned}
N_{0}&=\frac{X_{1}\cdot X_{2}^{3}\cdot Y_{0}\cdot \left(X_{0}^{2} - 3\cdot Y_{0}^{2}\right)}{24}\\
N_{2}&=\frac{X_{0}\cdot X_{1}\cdot X_{2}^{4}\cdot Y_{0}}{6}\\
N_{3}&=- \frac{X_{0}\cdot X_{1}\cdot X_{2}^{3}\cdot \left(3\cdot X_{0}^{2} - Y_{0}^{2}\right)}{24}\\
N_{5}&=\frac{X_{0}\cdot X_{1}\cdot X_{2}^{3}\cdot Y_{0}\cdot Y_{2}}{6}
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
