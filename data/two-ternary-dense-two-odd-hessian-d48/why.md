The equation splits into two ternary blocks,
\[
F=P(X_0,X_1,Y_0)+Q(X_2,Y_1,Y_2),
\]
each a dense cubic in the squares of its three coordinates. The target is the very short monomial \(A=X_0^5\cdot Y_1\). The mismatch between a simple target and two complicated blocks makes this a useful test of whether a general existence argument can be turned into explicit algebra without selecting an easier target afterward.

Nonconstructive existence is known: the target is odd in the reflected coordinates \(X_0,Y_1\), placing it in a supported sector of the reflection and cubic-surface constructions. See the reflection theorem in [Chapter 3, §3.3](#technical-information/geometric-support). The constructive problem is to produce concrete rational data for this exact class.

Each ternary block can be viewed as a cubic in one selected square, with coefficients depending on the other two squares. Binary-cubic Hessians and discriminants therefore remain available, but they now vary over those passive parameters. Diagonalizing such cubics, tracing between algebraic branches, and returning to homogeneous six-variable coordinates can introduce much larger denominators than the small constant-coefficient examples.

This entry asks whether those operations can be organized through compact identities rather than an opaque expansion. It also exposes the practical distinction between the size of a polynomial witness and the size of an explanation or proof of that witness. A structured formula can be intelligible even when its expansion has thousands of terms.

The stable identifier refers to one presentation of the same target; it imposes no denominator degree in the challenge. Comparing this example with [the asymmetric ternary split at \(q=2\)](#case/split-ternary-q2) highlights the next step: retaining constructive control when the individual square symmetries are removed.
