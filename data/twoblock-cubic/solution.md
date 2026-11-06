# A fixed denominator serving a companion bundle
The first binary block has coefficients \((-11/8,0,1)\) after its leading cube; the second has coefficients \((7/3,-2,1)\). The target and selected divisor are
\[
A=X_0^3\cdot Y_0^2\cdot Y_1-3\cdot X_0\cdot Y_0^4\cdot Y_1,
\]
\[
D=Y_0^2\cdot (X_0^2-3\cdot Y_0^2)^2+\frac1{17}\cdot Y_1^6+8\cdot X_1^6.
\]
The factor \(Y_0^2\cdot (X_0^2-3\cdot Y_0^2)^2\) records the binary-block structure; the two spectator sixth powers complete a legal denominator.

## Completing the numerator
With \(D\) fixed, impose the two equations
\[
N(F)=A\cdot D,\qquad D\cdot\operatorname{div}N-N(D)=F\cdot C
\]
on the degree-seven character supports. Reducing the second equation modulo \(F\) gives a linear system for the numerator coefficients. The witness linked below supplies a solution. In this completion \(N_2=N_5=0\), and, for example,
\[
N_1=-\frac1{34}\cdot X_0\cdot X_1\cdot Y_1\cdot (X_0^2-8\cdot Y_0^2)\cdot (4\cdot X_0^2-17\cdot Y_0^2),
\]
\[
N_3=-\frac3{34}\cdot X_0\cdot Y_0\cdot Y_1\cdot (X_0^2-3\cdot Y_0^2)\cdot (4\cdot X_0^2-17\cdot Y_0^2),\qquad
N_4=-\frac1{34}\cdot X_0\cdot Y_1^2\cdot (2\cdot X_0^2-Y_0^2)^2.
\]
Direct substitution proves that this particular completion has \(C=0\). It is therefore strict. The construction method allowed a nonzero remainder; its use did not by itself imply that the resulting remainder was nonzero.

## Why non-strict certificates also work
For any completion satisfying the two displayed equations,
\[
A-\mathrm dF(v)+F\cdot\operatorname{div}v=\frac{F^2\cdot C}{D^2},\qquad v=N/D.
\]
Since \(D\) is coprime to \(F\), the quotient \(C/D^2\) belongs to the relevant localization. Thus a nonzero \(C\) is fully allowed by the challenge. Strictness is only the special case \(C=0\), not an additional acceptance requirement.

## What transport preserves
The exact witness accommodates the second binary block in the displayed companion target. That is a statement about the chosen companion target and denominator shape. Replacing its multiplier by a different coordinate can fail the same fixed-denominator system, but such a failure says nothing about all possible denominators for the altered target.

The record contains all six exact rational numerator polynomials and the quotient \(C=0\), together with the reproducible linear-completion procedure.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here the normalized first equation vanishes and the second numerator is \(F\cdot C\), so the right-hand side is divisible by \(F^2\) in the localization away from \(F\). The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
