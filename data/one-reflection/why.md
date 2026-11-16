The sextic is a sparse deformation of Fermat with two couplings,
\[
X_0^3\cdot X_1\cdot Y_0\cdot Y_1
+X_1^3\cdot X_2\cdot Y_0\cdot Y_1.
\]
Both involve the same pair of odd coordinates. The target is the degree-six monomial \(X_0^3\cdot Y_0^3\), keeping the requested class simple while changing the coupling geometry from the central holdout. The visible reflection in \(Y_2\) alone does not serve this target, since its numerator is even in \(Y_2\).

Two additional reflections become visible after the block-linear change
\[
P=Y_0+Y_1,\qquad M=Y_0-Y_1.
\]
Indeed, \(Y_0\cdot Y_1=(P^2-M^2)/4\), while \(Y_0^6+Y_1^6\) is separately even in \(P\) and \(M\). Consequently \(F\) is separately even in \(P,M,Y_2\). This coordinate change commutes with the global sign involution, and the target decomposes as
\[
A=\frac18\cdot X_0^3\cdot P\cdot(P^2+3\cdot M^2)
+\frac18\cdot X_0^3\cdot M\cdot(M^2+3\cdot P^2).
\]
The two summands are odd under the \(P\) and \(M\) reflections, respectively.

Thus **existence is already known geometrically** from the reflection theorem in [Chapter 3](../../docs/03-geometric-support.md): each summand descends to the appropriate weighted Fano quotient, whose rational-curve construction provides divisor support. Adding the supported classes and applying the certificate theorem gives existence for this target. This geometric argument supplies a finite construction in principle; turning it into a usable rational field requires additional algebraic work.

The constructive challenge is to turn these hidden reflections into usable equations for a supporting divisor and a rational vector field. The shared factor \(X_1\cdot Y_0\cdot Y_1\) in the perturbation offers an additional algebraic handle. A successful construction would show how changing coordinates can expose useful quotient geometry even when the displayed target lies outside the sector served by the most obvious reflection. Compare [the coupled Fano target](../reflection-coupled-fano/why.md), where the favorable reflection character is visible from the outset.
