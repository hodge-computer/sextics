# Split the sextic into a Hesse triangle and a radial part
Put \(U=Y_0^2\), \(V=Y_1^2\), \(W=Y_2^2\). Then
\[
F=C+D,\qquad C=U^3+V^3+W^3-3\cdot U\cdot V\cdot W,\qquad
D=X_0^6+X_1^6+X_2^6+2\cdot Y_2^6.
\]
Over a field containing a primitive cube root \(\omega\), the complement factors into three quadrics:
\[
C=(U+V+W)\cdot (U+\omega\cdot V+\omega^2\cdot W)\cdot (U+\omega^2\cdot V+\omega\cdot W).
\]
The field is designed to annihilate this complement while scaling \(D\).

## The concrete numerator
For \(A=X_0\cdot Y_0\cdot Y_1^3\cdot Y_2\), the three-quadric Piola formula specializes to
\[
N_{X_i}=\frac16\cdot A\cdot X_i\quad(i=0,1,2),
\]
\[
N_{Y_0}=\frac16\cdot X_0\cdot Y_1\cdot Y_2^5,\quad
N_{Y_1}=\frac16\cdot X_0\cdot Y_0^3\cdot Y_2^3,\quad
N_{Y_2}=\frac16\cdot X_0\cdot Y_0\cdot Y_1^3\cdot Y_2^2.
\]
Direct differentiation gives \(N(C)=0\), \(N(D)=A\cdot D\), and \(\operatorname{div}N=A\). Consequently \(N(F)=A\cdot D\) and the rational field has zero divergence.

## Why Piola transport generalizes the formula
For arbitrary quadratic forms \(U,V,W\), the coordinate map \(\Phi=(X_0,X_1,X_2,U,V,W)\) has a Jacobian determinant \(\Delta\). Transporting a weighted target-space flux by \(\operatorname{adj}(d\Phi)\) multiplies both its divergence and target derivative by \(\Delta\). Here \(\Delta=8\cdot Y_0\cdot Y_1\cdot Y_2\), and division by eight gives the displayed normalization. This explains the monomial target and how the construction extends beyond coordinate squares.

The selected denominator is the sextic \(D\), not the quartic alternative also discussed in the linked research record. The two witnesses must not be interchanged without changing their numerators. The broader three-quadric family remains a proper locus of even sextics.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
