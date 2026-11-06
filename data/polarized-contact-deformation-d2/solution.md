# Deform by a multiple of the preserved divisor
Start with the coupled polarized-contact field \(N\), denominator \(D=X_2^2-Y_2^2\), and target \(A_0\). Its special properties are
\[
N(F_0)=A_0\cdot D,\qquad N(D)=0,\qquad \operatorname{div}N=0.
\]
Choose \(H=Y_1^4\) and \(s=101000303=101\cdot1000003\). Define
\[
F=F_0+s\cdot D\cdot H,\qquad A=A_0+s\cdot N(H).
\]
The numerator and denominator are unchanged.

## The transport calculation
The product rule gives
\[
N(F)=A_0\cdot D+s\bigl(N(D)H+D\cdot N(H)\bigr)=D\cdot(A_0+s\cdot N(H))=A\cdot D.
\]
Since both \(N(D)\) and \(\operatorname{div}N\) remain zero, the second strict equation survives automatically. The changed target has degree six: the numerator has degree three and differentiates a quartic. Thus the deformation preserves the required grading as well as the certificate identity.

## Why this coefficient was selected
The deformation vanishes modulo both \(1000003\) and \(101\), so at either prime it reduces to the undeformed polynomial. This preserves the reductions used to compare smoothness and the target class. The coefficient choice is an exact arithmetic design choice, not a numerical continuity argument.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof checks the certificate identity, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\).

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
