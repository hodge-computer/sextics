# Diagonalize the binary cubic over its Hessian field
The first block is \(p(u,v)=u^3+2\cdot u^2\cdot v+3\cdot u\cdot v^2+5\cdot v^3\), where \((u,v)=(X_0^2,Y_0^2)\). For a general binary cubic \(a\cdot u^3+b\cdot u^2\cdot v+c\cdot u\cdot v^2+d\cdot v^3\), use the Hessian quadratic
\[
H_p=(3\cdot a\cdot c-b^2)u^2+(9\cdot a\cdot d-b\cdot c)u\cdot v+(3\cdot b\cdot d-c^2)v^2.
\]
Its discriminant is \(\Delta_H=-3\operatorname{disc}(p)\). Over the corresponding quadratic extension, its factors provide linear coordinates \(R,S\) in which \(p=\alpha\cdot R^3+\beta\cdot S^3\).

## Construct a field upstairs, then trace the field
In the adapted coordinates, one groups \(\alpha\cdot R^3\) with one passive binary sextic \(H\), and \(\beta\cdot S^3\) with the other. A weighted partial Euler field scales the first group and annihilates the second. Multiplication by the prescribed density and Piola transport realize the target \(X_0\cdot X_1^2\cdot X_2^2\cdot Y_0\).

The conjugate construction serves the same rational target. Averaging the rational vector fields therefore preserves the certificate equation. Clearing their conjugate denominators produces their norm. With this normalization, the rational degree-twelve denominator is
\[
D=H^2+p\cdot H+\frac{H_p^3}{9\cdot\Delta_H},
\]
where \(H=2\cdot X_1^6+3\cdot X_1^4\cdot Y_1^2+5\cdot X_1^2\cdot Y_1^4+7\cdot Y_1^6\), and all binary forms are evaluated at \((u,v)\).

## Why the order of operations matters
One traces the fields, not the numerator tuples independently of their denominators. After a common denominator is chosen, the conjugate contributions combine into rational coefficients and satisfy both strict identities. This distinction is essential to a correct descent.

The family supplies a finite construction and several target directions, with additional legality conditions. The card is the stated specialization, not a claim that every cubic is diagonalizable over \(\mathbb Q\), nor that a degree-twelve norm is minimal.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
