# A line with triple contact
In square coordinates \((u,w,x)=(X_0^2,Y_0^2,X_1^2)\), the active cubic is
\[
p=(u-2\cdot w)^3+(u-2\cdot w+x)\cdot (2\cdot u^2+3\cdot u\cdot w+5\cdot w^2+7\cdot u\cdot x+12\cdot w\cdot x+13\cdot x^2).
\]
Its restriction to \(u-2\cdot w+x=0\) is the cube \((u-2\cdot w)^3\). Thus the contact line meets the cubic with multiplicity three at \((2:1:0)\). Pull it back to
\[
D=X_0^2-2\cdot Y_0^2+X_1^2.
\]

## A compact numerator despite a long target
Take
\[
N_0=-2\cdot Y_0\cdot (X_0^2-2\cdot Y_0^2),\qquad N_3=X_0\cdot X_1^2,
\]
with all other components zero. The logarithmic equation is immediate:
\[
\operatorname{div}N=-4\cdot X_0\cdot Y_0,\qquad N(D)=-4\cdot X_0\cdot Y_0\cdot D.
\]
Differentiating the displayed cubic produces
\[
\frac{N(F)}D=X_0\cdot Y_0\cdot \bigl(-36\cdot X_0^4-50\cdot X_0^2\cdot X_1^2+56\cdot X_0^2\cdot Y_0^2-28\cdot X_1^4+28\cdot X_1^2\cdot Y_0^2-44\cdot Y_0^4\bigr),
\]
which is exactly the recorded target. The passive sixth powers do not contribute.

## What the example demonstrates
The target looks complicated when expanded, but the field and the contact presentation are simple. This is a construction-first mechanism: a geometric divisor supplies a logarithmic field, and its derivative identifies the served target. The exact record fixes that target afterward, so verification is still a concrete polynomial calculation. The conclusion is a strict degree-two certificate on this inflection fiber, not a proof that the same quadric works away from the collision.

## The finite certificate check
For \(v=N/D\), clearing denominators gives
\[
A-q\cdot\mathrm dF(v)+F\cdot\operatorname{div}v
=\frac{D\cdot(A\cdot D-q\cdot N(F))+F\cdot\bigl(D\cdot\operatorname{div}N-N(D)\bigr)}{D^2}.
\]
Here both bracketed expressions vanish, so the residual is identically zero. The degree condition, nonzero denominator, and coprimality with \(F\) are separate side conditions retained with the exact record. The accepted Lean proof establishes the exact identities, homogeneous degrees, nonzero denominator, and coprimality over \(\mathbb C\) for this tuple.

The [exact witness](witness.json) gives the denominator, all six numerators, and the quotient. The [Lean proof](Solution.lean) checks the certificate and its side conditions.

The Lean proof uses the shared [explicit-witness assembly](../../formal/lean/HodgeComputer/Constructions/Explicit.lean); its instance-specific identities and displayed witness remain in this folder.
