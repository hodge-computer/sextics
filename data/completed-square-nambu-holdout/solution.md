# Complete the square before constructing the field
The sextic is arranged as
\[
F=X_1^6+T^2+G(X_0,X_2,Y_0,Y_2),\qquad
T=Y_1^3+Y_2^3+\frac12\cdot X_2^2\cdot Y_2.
\]
The crucial point is that \(G\) is independent of the two active variables \(X_1,Y_1\). Use
\[
D=X_1^6+T^2,\qquad A=X_1^2\cdot X_2\cdot Y_1^2\cdot Y_2,
\]
and the two nonzero components
\[
N_1=\frac16\cdot X_1^3\cdot X_2\cdot Y_1^2\cdot Y_2,\qquad
N_4=\frac16\cdot X_1^2\cdot X_2\cdot Y_2\cdot T.
\]
This is a weighted radial construction in the two quantities \(X_1^3,T\). The derivative \(\partial T/\partial Y_1=3\cdot Y_1^2\) accounts for the factor \(Y_1^2\) in the target.

## The entire verification in three equalities
Because \(N\) does not differentiate the passive variables, \(N(G)=0\). Direct calculation gives
\[
N(F)=N(D)=A\cdot D,\qquad \operatorname{div}N=A.
\]
For example, the two terms in \(N(D)\) are \(A\cdot X_1^6\) and \(A\cdot T^2\). Each active component contributes \(A/2\) to the divergence. Hence both strict certificate equations hold, without expanding \(G\).

## The Nambu interpretation
Over \(\mathbb Q(i)\), the denominator splits as \((X_1^3+i\cdot T)\cdot(X_1^3-i\cdot T)\). The rational field above can be interpreted as the trace of conjugate Nambu channels with passive first integrals. The compact formula shows why the complex auxiliary factors cause no irrational coefficients in the final witness. It also makes the scope clear: changing the passive term \(G\) preserves the identities, whereas changing the active completed square requires checking them again.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
