This target combines two residue characters on the central chain sextic:

\[
A=X_0^3\cdot Y_0^3+X_0^3\cdot Y_0\cdot Y_1^2.
\]

The first summand is served by the [central holdout's Fermat cover](../holdout/why.md) and its moving-conic construction. For the second, the corresponding deck exponent is zero: the antisymmetrized source used by that cover vanishes. The bundle therefore probes the image of the construction, rather than merely another coefficient choice in the same source formula.

The second summand is invariant as a residue under a complementary diagonal action, with weights \((5,1,5)\) on the odd coordinates. The original equation is invariant under that action as well. **Geometric existence is known** from the quotient-support argument in [Chapter 4](../../docs/04-known-locus-and-frontier.md), together with the cover argument for the first summand. The challenge is to turn that complementary support into a rational-field certificate, or to formalize the existence argument itself.

An explicit construction must supply a primitive on the serving geometry and transport its density, normal derivative, and denominator back to the original sextic. The polynomial-family integration machinery gives a route once a suitable curve family and source have been established; knowing that a residue descends does not supply those inputs.

Combining the two resulting certificates is a separate algebraic step. A common denominator must retain both quotient remainders; there is no reason to demand strict certificates or the same denominator for the two summands. Thus the bundle tests whether two supporting mechanisms can be assembled without narrowing the unrestricted existence problem. It does not ask for a single source formula covering every character of the sextic.
