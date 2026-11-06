All three binary blocks are non-diagonal and have different coefficients. For example, the first is
\[
p(u,w)=u^3+2\cdot u^2\cdot w+3\cdot u\cdot w^2+5\cdot w^3,
\qquad (u,w)=(X_0^2,Y_0^2).
\]
Its discriminant is \(-367\). The Hessian quadratic splits over \(\mathbb Q(\sqrt{1101})\), providing a natural extension field in which the binary cubic can be expressed as a sum of two cubes.

The target \(X_0\cdot X_1^2\cdot X_2^2\cdot Y_0\) crosses the three blocks. Its \(X_0\cdot Y_0\) factor is suited to the Jacobian density of a quadratic-coordinate change, while the two remaining squares have a balanced role in the other pairs. This makes the example a test of adapting the geometry to a prescribed rational class, rather than selecting any class that happens to appear after diagonalization.

The arithmetic issue is central. A convenient construction over a quadratic extension does not yet give a rational tuple of polynomials. Conjugate fields may have different denominators, and descent must preserve the entire rational-field equation. Multiplying conjugate denominator factors without transporting and combining the corresponding fields would leave that issue unresolved.

This fiber was chosen to demonstrate a family construction across several target directions, with the atlas retaining one representative. Its role is to separate geometric simplification over an extension from the eventual rational presentation. Comparing it with [the root-cube example](#case/family-root-cube) also distinguishes two ways of adapting a binary cubic: split its Hessian, or choose a root of the cubic itself. [Chapter 2](#technical-information/explicit-constructions) develops the general contact-and-descent setting. The denominator degree in a particular descended answer is secondary to understanding why the target survives the descent.
