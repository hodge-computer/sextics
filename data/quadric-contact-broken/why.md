This is a deliberately obstructed deformation of [Two reflections · quadric polar](../two-reflection-cubic-surface-d2/why.md). Let \(F_*\) denote that entry's sextic, and retain its target

\[
A=X_1^2\cdot X_0\cdot Y_0\cdot(X_0^2-Y_0^2).
\]

Add the globally even perturbation \(t\cdot X_0\cdot X_1\cdot Y_0\cdot Y_1\cdot(X_2^2+2\cdot Y_2^2)\), with \(t=5/7\). It destroys both individual reflections used by the original construction.

For \(F_*\), the accepted field is

\[
v=\frac{X_1^2}{4\cdot(X_0^2+Y_0^2)}\cdot(-Y_0,0,0,X_0,0,0).
\]

It is divergence-free and satisfies \(dF_*(v)=A\). On the deformed sextic, the error is explicitly

\[
dF(v)-A=\frac{t\cdot X_1^3\cdot Y_1\cdot(X_2^2+2\cdot Y_2^2)\cdot(X_0^2-Y_0^2)}{4\cdot(X_0^2+Y_0^2)}.
\]

There is a stronger obstruction than failure of this particular field: **no replacement numerator tuple can work with denominator \(D=X_0^2+Y_0^2\)**, or a nonzero constant multiple of it. Any legal certificate with that denominator would imply \(A\cdot D\in(\partial_0F,\ldots,\partial_5F)\). Indeed, the cleared key equation and coprimality of \(D\) with \(F\) imply \(A\cdot D-\sum_iN_i\partial_iF\) is a multiple of \(F\); Euler's identity places \(F\) in its Jacobian ideal.

This necessary condition is an exact linear system: six arbitrary cubics supply 336 coefficients. Modulo \(101\), its coefficient matrix has rank 336 and the augmented matrix rank 337. The full column rank makes this a characteristic-zero inconsistency certificate as well: a rational nonzero augmented minor remains nonzero, while the coefficient matrix has only 336 columns. The same linear-system obstruction holds over \(\mathbb C\).

Thus a solution needs a genuinely different denominator, possibly a higher power of the old quadric or an entirely different support. The obstruction does not rule out those possibilities. This makes the instance a focused test of how a successful contact construction can be repaired after its symmetry is broken.

Reduction modulo \(5\) proves smoothness. The Hessian symmetrizer space is scalar, excluding a hidden linear block split. The record includes the reproducible full-numerator rank calculation; it imposes no denominator bound on the actual challenge.
