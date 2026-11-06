# Move from Klein monomials to Hesse coordinates
Define
\[
r=X_0\cdot X_1\cdot X_2,\quad U=X_0^3\cdot X_1^2,\quad V=X_1^3\cdot X_2^2,\quad W=X_2^3\cdot X_0^2,\quad p=U+V+W.
\]
The active sextic is the cyclic Klein form with deformation \(\kappa\cdot r^2\). The monomial map exposes a Hesse relation among \(U,V,W\). Its logarithmic and complementary Euler fields can be transported back by a rational monomial Piola formula.

For this branch the polar divisor is
\[
D_\kappa=(\kappa^2-3\kappa+9)r^3\cdot f_\kappa-p^3.
\]
At \(\kappa=2\), the coefficient is \(7\), and \(D\) has degree fifteen. The numerator degree is therefore sixteen. This is the \(\kappa=2\) specialization of the displayed formula; formulas valid only at \(\kappa=0\) must not be substituted here.

## Why the target is a difference
The construction uses the nontrivial Fourier directions of the cyclic monomial triple. These span zero-sum combinations such as \(U-V\), multiplied by permitted passive linear factors. The sum direction behaves differently. The displayed target lies in the served packet, and the transported field satisfies the two strict identities after the complementary Euler correction.

The Piola step accounts for the Jacobian density of the monomial map. It is essential for divergence; merely replacing variables in a field would lose that density. Rational simplification then cancels the auxiliary monomial denominators, leaving the stated polynomial numerator over \(D_\kappa\).

## Scope
This branch serves a six-dimensional packet of zero-sum targets at the stated parameter, not every individual cyclic monomial. The separate rational Klein entry treats an individual monomial by a different, higher-degree trace construction. The degree-fifteen record contains the expanded rational tuple: eleven terms in each active component and three zero components.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
