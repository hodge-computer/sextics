The cross term \(X_0\cdot X_2^5\) makes this sextic look different from the cubic-in-squares examples. It can instead be written
\[
F=X_0\cdot T+X_1^6+Y_0^6+Y_1^6+Y_2^6,
\]
where \(T=X_0^5+2\cdot X_0^3\cdot Y_0^2+3\cdot X_0\cdot Y_0^4+X_2^5\). The useful structure is a product of degrees one and five, together with a complementary weighted polynomial.

The target is \(-10\cdot X_1\cdot X_2^4\cdot Y_1\). Its coefficient and exponents match the Jacobian density of the map using \(X_0,T,X_1^2\) as three adapted coordinates. Thus the target is tied to a nonlinear change of variables, rather than an arbitrary odd sextic chosen independently of the presentation.

The product \(X_0\cdot T\) admits opposite infinitesimal weights on its two factors. This suggests a logarithmic or shear-type approach, in contrast with the contact conics used in the Hesse examples. The complication is that \(T\) depends on the original variables: it is independent only in the adapted coordinate system. A correct construction must account for that dependence when it returns to the original vector-field equation.

This instance is a simple representative of a much larger family built around that degree-one-times-degree-five structure. Its purpose is to test how a nonlinear coordinate map can convert a short weighted identity into a useful rational primitive, and to make the resulting target restriction explicit. The broader family does not cover arbitrary even sextics merely because its expanded equations can have many terms. [Chapter 2, §2.1](../../docs/02-explicit-constructions.md) explains cofactor transport, while [the mixed cofactor example](../cofactor-mixed/why.md) provides a comparison with a quadratic–cubic map instead of a triangular one.
