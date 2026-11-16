This equation is a controlled departure from the all-target split theorem:

\[
F=f(X)+g(Y)+t\cdot L(X)^2\cdot M(Y),\qquad t=\frac57.
\]

The entire mixed component has block bidegree \((4,2)\) and tensor rank one. There is no \((2,4)\) component. At \(t=0\), the elliptic-companion theorem of [Chapter 3A](../../docs/03a-split-and-k3.md) supplies every allowed certificate. The nonzero coupling preserves global parity while removing the product decomposition on which that theorem relies.

The quotient geometry gives a precise way to study what changed. Over \(\mathbb P^2_X\times\mathbb P^2_Y\), use the squared relative block scale to write the fiber equation as the binary cubic

\[
a\cdot s^3+b\cdot s^2\cdot u+d\cdot u^3=0,
\]

where \(a=f(X)\), \(b=t\cdot L(X)^2\cdot M(Y)\), and \(d=g(Y)\). Its discriminant is

\[
-d\cdot\bigl(4\cdot b^3+27\cdot a^2\cdot d\bigr).
\]

The square factor in \(L\) and the absence of a second mixed coefficient make this a much more structured perturbation than a general sextic. But the branch locus now varies with both blocks: one cannot simply reuse the fixed elliptic contraction from the split case. Producing an actual support correspondence across this deformation is the unresolved step, not checking that the equation retains a particular bidegree.

A first avenue is to analyze the divisors \(L=0\), \(M=0\), and the discriminant factor, where the cover degenerates in controlled ways. A contact or trace construction would have to verify its Gysin image or the full rational-field identity; degeneracy alone is not a certificate. The target \(A=X_0^3\cdot Y_0^3\) keeps the same balanced block degrees that make the undeformed split geometry accessible.

Reduction modulo \(5\) proves smoothness. There are no coordinate reflections and the Hessian symmetrizer space is scalar. In particular, the deformation cannot be undone by a linear coordinate change restoring a \(3+3\) split. No certificate for the nonzero value \(t=5/7\), or general existence theorem covering it, is supplied here.
