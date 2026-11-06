# Cubic-surface contact and pole reduction

These coefficient-parameterized constructions are extracted from `HeadOfNaps`’s [holdout-q2 proof](../../../../../data/holdout-q2/solution.md) ([#124](https://github.com/hodge-computer/sextics/pull/124)), with its original mathematical credit and AI-assistance disclosure. The public namespace is `HodgeComputer.CubicSurfaces`.

| Module | Interface | Scope |
| --- | --- | --- |
| `LineContact` | `LineContact.certificate_equations` | A contact field for the four-variable cubic specified by `LineContact.cubic`, given its four line-relation equations. `sourceCoefficients` and `gradientCoefficients` expose the quadratic source span. |
| `QuinticReduction` | `QuinticReduction.source`, `primitive_source` | An explicit Jacobian representation of a quintic source for the stated coefficient family. The normalized primitive requires an inverse of the displayed coefficient denominator. |
| `Q2Reduction` | `Q2Reduction.q2_equations` | Converts a Jacobian representation `N(G) = B` and a strict pole-one certificate for `div N` into pole-two equations on a homogeneous cubic in four variables. |

The pole-two construction is the cleared Euler correction

\[
W_2=(N+G W_1)/2-(\operatorname{div}N)E/6.
\]

Its polynomial form uses denominator `6D` and proves both contraction and divergence identities. The grading, cubic degree and source-representation hypotheses are explicit; it is not a theorem that every quintic lies in the required Jacobian image.

The application constructs the contact line over a finite algebra, proves the source-span and denominator conditions, supplies the special-fiber nonvanishing check, and transports the result to the six-variable sextic. The common norm and matrix machinery is in [FiniteAlgebra](../FiniteAlgebra/README.md).
