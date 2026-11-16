This target moves the central holdout to the next pole order:
\[
q=2,\qquad
A=X_0^3\cdot X_1^2\cdot X_2^2\cdot Y_0^3\cdot Y_1^2.
\]
The polynomial has degree twelve, as required. It multiplies the central cubic by three square factors, but a certificate for the cubic would not simply multiply to a certificate here: differentiation of those factors introduces extra terms, and the pole-order operator itself changes.

At \(q=1\), the condition is \(F^2\mid A-dF(v)+F\cdot\operatorname{div}(v)\). Here it becomes
\[
F^3\mid A-2\cdot dF(v)+F\cdot\operatorname{div}(v).
\]
Both the coefficient of the derivative term and the required divisibility increase. This makes the example a test of a mechanism across pole orders, rather than merely a larger polynomial input to the same linear system.

The exact same degree-twelve target on Fermat is [an accepted control](../fermat-q2/why.md). The comparison therefore isolates the effect of the holdout's two mixed couplings. A successful extension must explain how to correct the diagonal construction when its active and passive coordinates cease to be separate.

The degree-six character counts do not by themselves determine this degree-twelve class. In particular, the direct quotients' 182-dimensional supported space and its ten-dimensional paired-sign complement refer to \(q=1\); they should not be transferred to this target without a separate argument in the appropriate Jacobian degree.

This is a useful place to investigate recursive pole reduction, deformation of known rational fields, or support constructions that serve several Hodge levels at once. Any such approach must preserve the specific numerator class, not merely its total degree or parity. [The binary-block \(q=2\) instance](../block-q2/why.md) provides a second comparison where parameter dependence is controlled but the equation remains much more separated.
