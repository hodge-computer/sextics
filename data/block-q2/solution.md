# A binary block and its compatible degree-twelve bundle
Use \(u=X_0^2\), \(w=Y_0^2\), and
\[
D=P(u,w)=u^3+2\cdot u^2\cdot w-u\cdot w^2+w^3.
\]
The full sextic adds the four spectator sixth powers. The target is
\[
A=X_0\cdot Y_0^{11}-\frac{610}{87}\cdot X_0\cdot Y_0^5\cdot Y_2^6.
\]
The coefficient is determined by the binary cubic, not chosen for numerical convenience. For the parameters \((\mu,\nu,\gamma)=(2,-1,1)\), the cubic discriminant is \(-87\), and the compatibility expression is
\[
\frac{10\cdot (2\cdot\mu^3-9\cdot\mu\cdot\nu+27\cdot\gamma)}{\operatorname{disc}(P)}=-\frac{610}{87}.
\]

## A complete fixed-denominator solve
At \(q=2\) and \(\deg D=6\), the numerator degree is thirteen. The numerator is obtained by solving
\[
2\cdot N(F)=A\cdot D,\qquad D\cdot\operatorname{div}N-N(D)=0.
\]
This provides a strict certificate, so the residual is zero and in particular divisible by \(F^3\).

## Interpret the coefficient correctly
At this fiber the compatibility calculation forces the displayed target ratio. That conclusion belongs to the fixed denominator and the retained target bundle. Rank jumps at other parameter values can change the compatibility conditions, and failure for a different ratio here does not exclude every possible denominator.

The exact witness linked below supplies a concrete rational tuple. The selected denominator is also checked to be nonzero and coprime to the full sextic, rather than inferred to be legal merely because it is one visible block.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
