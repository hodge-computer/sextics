This example begins with a plane sextic having a prescribed contact presentation,
\[
f=h^2+C\cdot k,
\]
where \(h,C,k\) are cubics. Along \(C=0\), the sextic restricts to a square. That is substantially more information than knowing that some curve meets the sextic: it specifies an algebraic relation that can potentially control both a rational pole and its derivative.

The six-variable equation is obtained by polarization:
\[
F=f(U)+f(V),\qquad U=X+Y,\quad V=X-Y.
\]
The involution \(Y\mapsto-Y\) exchanges the two blocks. This matters because a block swap acts differently on the split cohomology from the usual sign change of an entire ternary block. The all-target block-sign argument cannot simply be imported with the variables renamed; [Chapter 3A](../../docs/03a-split-and-k3.md) explains the remaining K3 component.

The target is likewise an antisymmetric difference, \(g(U)-g(V)\), with \(g\) determined by the plane contact data. It is therefore a selected class naturally attached to the presentation, not a claim that every target on this polarized sextic is equally accessible. The relevant question is how the contact geometry selects this target and how a construction can respect the swap involution after returning to \(X,Y\) coordinates.

The cubic-contact presentation suggests several controlled variations: change the degree of the contact form, replace a square by another perfect power, or couple the two polarized copies through quantities that the contact field preserves. [The factored binary example](../cone-ladder-linear/why.md) and [the coupled polarized example](../polarized-contact-coupled-d2/why.md) pursue those directions. The significance here comes from the special algebraic presentation; the topology of a rendered real slice is a separate visualization, not evidence for the certificate.
