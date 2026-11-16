The target is the balanced monomial
\[
A=X_0\cdot X_1\cdot X_2\cdot Y_0\cdot Y_1\cdot Y_2,
\]
on a deformation of the holdout with chain coefficients \(1/2\) and an additional term \(\tfrac13\cdot X_0\cdot X_1\cdot Y_0\cdot Y_1^3\). That term has bidegree \((2,4)\), whereas the chain terms have bidegree \((4,2)\). The paired sign changes preserve both equation and target.

Compare the identical target on [the all-six holdout instance](../holdout-all-six/why.md). Its cover construction uses \(T^6=Y_0^6+Y_2^6\), \(y=Y_1\), and the exchange \(y\leftrightarrow T\). In the present equation the extra coupling becomes
\[
\frac13\cdot\alpha\cdot X_0\cdot X_1\cdot y^3\cdot T,
\qquad \alpha=Y_0/T.
\]
It lacks the exchanged term proportional to \(y\cdot T^3\). Consequently the equation does not descend to the same weighted quotient, even though the balanced target has exactly the trace character used successfully on the holdout. A favorable target projection cannot compensate for the loss of the quotient geometry on which its primitive is constructed.

The complementary quotient of [Chapter 2, §2.8](../../docs/02-explicit-constructions.md) has a different failure here. Its diagonal action with weights \((5,1,5)\) on \(Y\) gives the extra coupling weight two. Consequently the polynomial-density integration theorem on that quotient cannot be imported without first constructing a replacement quotient.

The common factor \(X_0\cdot X_1\cdot Y_0\cdot Y_1\) in the first coupling and the added term still leaves useful structure. It suggests investigating adapted quadratic coordinates or a replacement cover, with the asymmetric combination of \(X_0^2\) and \(Y_1^2\) kept explicit. A successful construction must control both the equation and the density; matching the target's pairwise balance alone is insufficient.

The paired-sign substitution \(Y_i=r_iX_i\), \(u_i=X_i^2\) makes another boundary explicit. The added coupling becomes \(\frac13r_0r_1^3u_0u_1^2\), reversing the first cubic edge. The [cyclic cubic](../cycle-three/why.md) and [transitive mixed-biweight](../mixed-biweight/why.md) constructions show that a Jacobian and a moving-map correction can replace the lost chain quotient. Both retain the diagonal action with weights \(2,1,0,3,2,1\) modulo six, which also preserves this equation and the balanced residue. Thus that character screen supplies no obstruction here. The added reverse edge nevertheless lies in a different cubic coefficient pattern from either accepted covariant family. Here both the altered Jacobian family and the balanced physical source need a derivative-compatible transport. The shared moving-map identity addresses a correction term once such data are supplied; it does not furnish the missing primitive.
