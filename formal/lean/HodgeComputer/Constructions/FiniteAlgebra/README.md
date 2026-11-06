# Finite-algebra contact certificates

These tools come from `HeadOfNaps`’s accepted [quadric-contact-broken](../../../../../data/quadric-contact-broken/solution.md) ([#122](https://github.com/hodge-computer/sextics/pull/122)) and [holdout-q2](../../../../../data/holdout-q2/solution.md) ([#124](https://github.com/hodge-computer/sextics/pull/124)) constructions. Both applications now import one implementation. Their explanations retain the original mathematical credit and disclosed AI assistance; this extraction was prepared for `benediamond` with Codex assistance.

Import individual modules, or `HodgeComputer.Constructions.FiniteAlgebra` for the whole package. The original declaration namespaces (`QuadricContact`, `QuadricContactMatrixBezout`, `FiniteAlgebraInverse`, and `CheckedPolynomialLists`) are retained.

| Module | Reusable result | What the application supplies |
| --- | --- | --- |
| `MatrixContact` | `QuadricContact.pderiv_contact` and `pderiv_contact_column` turn commuting matrix contact data into polynomial contraction/divergence identities. | The matrix, its adjugate, compatible tangent matrices, the actual formal derivatives, and contact equations. |
| `MatrixBezout` | `QuadricContactMatrixBezout.relPrime_det_of_matrix_bezout` proves coprimality with a determinant; `relPrime_cubic_det` specializes the matrix identity to a cubic. | An actual matrix Bézout identity, not just a nonzero determinant at one point. |
| `PolynomialMatrixMap` | Substitution into the matrix construction preserves its derivatives, source identities and grading under the stated hypotheses. | The coefficient map and derivative/degree compatibility. |
| `MatrixHomogeneous` | Homogeneity of determinants, adjugates, traces and contact numerators. | Uniform degrees for the matrix entries. |
| `FiniteAlgebraInverse` | `isUnit_of_leftMulMatrix` supplies an inverse inside a finite free algebra. | A basis and a unit determinant for multiplication by the element. |
| `RegularSpecialization`, `AdjoinRootSpecialization`, `AdjoinRootUnits` | Transfer polynomial and finite-algebra identities through a regular coefficient specialization. | The exact denominator, monic-polynomial and invertibility hypotheses in the chosen interface. |
| `FractionDerivation` | `QuadricContactFraction.extend` extends a rational-base derivation to a fraction field. | A domain, its fraction field, and the compatible algebra structures. |
| `CheckedPolynomialLists`, `CheckedPolynomialListDegree` | Kernel-checked rational coefficient arithmetic and degree bounds. | Concrete lists and equalities; these are exact calculations. |

The finite line algebra, eliminants, specialization values, source-span matrix, physical substitution, and final `HasCertificate` theorem remain in the applications. In particular, this package does not assert that an arbitrary cubic has suitable contact data, or that a determinant is legal merely because it is nonzero.
