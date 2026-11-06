# Use the cyclic monomial map
Define
\[
U=X_0^3\cdot X_1^2,\qquad V=X_1^3\cdot X_2^2,\qquad W=X_2^3\cdot X_0^2,
\]
\[
P=U^2\cdot W+U\cdot V^2+V\cdot W^2,\qquad
Q=U^2+V^2+W^2-U\cdot V-U\cdot W-V\cdot W.
\]
The target is the individual monomial \(A=U\cdot Y_0\). The rational denominator is
\[
D=Q^3+9\cdot (U+V+W)^3\cdot P,
\]
which has degree thirty in the original variables.

## Fourier channels and rational descent
The construction diagonalizes the cyclic structure using a primitive cube root of unity. It constructs logarithmic fields in the resulting Fourier coordinates, then transports them through the monomial map by the rational Piola formula. The two conjugate fields are combined by a normalized trace, giving coefficients in \(\mathbb Q\).

After simplification, only the three active \(X\)-components remain. The exact rational expressions are supplied in the witness linked below. Their total degree is 31. The multiplier \(Y_0\) is passive, so it does not introduce an extra derivative in the active field.

The descended tuple satisfies \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\). These identities establish the strict certificate; the denominator norm by itself would not.

## What the larger denominator buys
The lower-degree Klein–Hesse branch serves zero-sum combinations of \(U,V,W\). This construction reaches individual monomials. Cyclic permutation and the three passive linear multipliers give nine target directions, with a mirrored block yielding a corresponding packet. The scope is this explicit family and target space, not all odd sextic targets. Degree thirty is a usable rational denominator, without a minimality claim.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
