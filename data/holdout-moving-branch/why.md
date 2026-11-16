A cover can create a reflection that the original equation does not possess. For the [central holdout](../holdout/why.md), adjoining \(T^6=Y_0^6+Y_2^6\) and writing \(Y_0=\alpha\cdot T\), \(Y_2=\beta\cdot T\), \(y=Y_1\) makes the equation symmetric under \(y\leftrightarrow T\). The fixed coefficient curve \(\alpha^6+\beta^6=1\) and a moving conic on the quotient then support the cover-and-trace construction.

This instance adds just

\[
\frac17\cdot X_0^2\cdot Y_0^2\cdot Y_2^2
\]

to that sextic, keeping the same target \(A=X_0^3\cdot Y_0^3\). All three paired sign changes survive. The perturbation is separately even in every coordinate: its purpose is to change the branch geometry without introducing another odd chain coupling.

On the original cover the extra term is \(\frac17\cdot X_0^2\cdot\alpha^2\cdot\beta^2\cdot T^4\). Interchanging \(y,T\) changes the equation by

\[
\frac17\cdot X_0^2\cdot\alpha^2\cdot\beta^2\cdot(y^4-T^4).
\]

Thus the old quotient coordinates \(S=y^2+T^2\), \(P=y\cdot T\) no longer describe the complete equation. Absorbing the perturbation into the definition of \(T\) instead gives

\[
\alpha^6+\beta^6+\frac17\cdot(X_0/T)^2\cdot\alpha^2\cdot\beta^2=1.
\]

The coefficient curve now varies with an active coordinate. The derivative compatibility and normal-source identities proved over the fixed Fermat curve cannot simply be reused.

The complementary diagonal quotient does not avoid this change. Its weights \((5,1,5)\) on \(Y\) give the perturbation weight two modulo six, so it no longer preserves the equation. The two chain constructions fail at their geometric input, before a choice of polynomial source or curve seed.

A solution would therefore test whether a cover-and-trace argument can accommodate moving branch data. Possible approaches include a different auxiliary cover, a transport calculation that incorporates the varying coefficient relation, or a new family of rational curves. The [deformed-ternary companion](../holdout-ternary-deformation/why.md) demonstrates the different situation in which a replacement conic and its nonsingular incidence suffice because the original cover symmetry and coefficient curve remain available. The shared lifting theorem does not restore a symmetry absent from the changed equation.

Exact checks establish smoothness and rule out linear direct-sum decompositions, coordinate-reflection formulas, and the target-fixing junior diagonal quotients screened in [Chapter 4](../../docs/04-known-locus-and-frontier.md). These are boundaries of specified constructions, not a claim that every possible method has been excluded. No certificate or general existence conclusion for this perturbed target is supplied here.

Paired signs provide a more direct alternative. Put \(r=X_2^2\), \(v=Y_0/X_0\), \(c_i=(Y_i/X_i)/v\), and normalize the three squares by \(r\). The cubic is the same six-coefficient transitive family used by [Mixed biweight](../mixed-biweight/why.md), with
\[
(a,b,c)=(1+v^6,1+c_1^6\cdot v^6,1+c_2^6\cdot v^6),\qquad
(d,e,f)=(c_1\cdot v^2,c_1\cdot c_2\cdot v^2,\tfrac17\cdot c_2^2\cdot v^4).
\]
Its universal covariant and differential identities are therefore available. The substitution \(T=r\cdot v^6\) again gives polynomial Jacobian coefficients of degrees four and six, and the same diagonal symmetry preserves the target residue. The remaining application obligations are a nonsingular polynomial-curve incidence for these coefficient functions and the exact physical source transport. This is a test of the reach of the transitive Jacobian method, not evidence that moving branch data intrinsically prevents a certificate.
