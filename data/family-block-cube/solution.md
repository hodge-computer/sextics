# An osculating cube for a binary cubic
The active cubic is \(p(s)=s^3+s^2+2\cdot s+3\), corresponding to the displayed homogeneous block in \(X_0^2,Y_0^2\). At the family parameter \(\theta=0\), the osculating cube is
\[
C=\frac{(2\cdot X_0^2+9\cdot Y_0^2)^3}{243}.
\]
The construction completes it to
\[
D=C+Y_1^6+\frac{1681}{1701}\cdot Y_2^6,
\qquad A=X_0^3\cdot Y_0^3.
\]
The unusual last coefficient is forced by the pencil compatibility. It should not be replaced by one merely because the denominator would look simpler.

## How contact controls the completion
The osculating cube is chosen to match the binary cubic and its first derivative at the selected parameter. The pencil joining the cube and the original cubic therefore contains a prescribed double-contact member. The spectator channels must occur at the compatible degeneration parameters of that pencil. This converts the geometric choice into exact rational coefficient relations.

Once \(D\) is fixed, solve for homogeneous degree-seven numerators on the degree-compatible character supports. The exact witness below gives one such solution. Both \(N(F)=A\cdot D\) and \(D\cdot\operatorname{div}N=N(D)\) are imposed; the latter is not inferred from the contact picture alone. The non-diagonal block in \(X_1,X_2\) is passive for the adapted construction.

## What the parameter conditions mean
This card is one legal specialization of a parameterized block-cube family. In particular, failure of a simplified fixed denominator only excludes that shape. The exact witness supplies the actual rational certificate for the displayed target, with no claim that all binary cubics use the same osculating parameter or spectator weights.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
