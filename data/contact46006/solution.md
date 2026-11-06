# Start with a plane contact presentation
In three variables \(z\), the retained sextic has form
\[
f=h^2+C\cdot k,\qquad h=z_0^3+2\cdot z_2^3,
\]
where
\[
C=z_1^3+5\cdot z_1^2\cdot z_2-22\cdot z_1\cdot z_2^2-56\cdot z_2^3.
\]
Take the polynomial field \(W=\nabla C\times\nabla h\). A cross product of gradients has zero divergence and annihilates both \(C\) and \(h\). Therefore
\[
W(f)=C\cdot W(k)=C A_C,\qquad W(C)=0,\qquad \operatorname{div}W=0.
\]
The contact presentation is doing all the work: it turns the derivative of the sextic into a multiple of the contact divisor.

## Polarize two copies
Let \(U=X+Y\), \(V=X-Y\). The six-variable instance is
\[
F=f(U)+f(V),\quad A=A_C(U)-A_C(V),\quad D=C(U)C(V).
\]
The involution \(Y\mapsto-Y\) exchanges \(U,V\), making \(F,D\) even and \(A\) odd. In the original coordinate slots the numerator is
\[
N_X=\frac{W(U)C(V)-W(V)C(U)}2,\qquad
N_Y=\frac{W(U)C(V)+W(V)C(U)}2.
\]
These are vector identities with three components each.

## Verification and scope
In \((U,V)\) coordinates, the two field components are \(W(U)C(V)\) and \(-W(V)C(U)\). Their derivative of \(F\) is \(A\cdot D\); their divergence is zero; and they annihilate \(D\). Linear coordinate transport preserves those statements. Thus the certificate is strict.

The construction requires the special contact presentation \(f=h^2+C\cdot k\). It does not establish such a presentation for an arbitrary plane sextic, nor solve every target on the polarized fourfold. The record serves the specific Hamiltonian target difference and preserves its exact plane data.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof checks the certificate identity, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\).

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
