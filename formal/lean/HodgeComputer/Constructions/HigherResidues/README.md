# Higher residues on polynomial-curve families

This library constructs a residue primitive for a third-order hypersurface pole from a supplied polynomial-curve family. It is the formal counterpart of the higher-pole residue calculus in [Chapter 3A](../../../../../docs/03a-split-and-k3.md). The proofs are extracted from `fqlx`'s [split-ternary construction](https://github.com/hodge-computer/sextics/pull/159); its accepted files, attribution, and verification record remain unchanged.

## Entry point and scope

Import `HodgeComputer.Constructions.HigherResidues.HigherCurve` and use `SplitHigherResidue.residue_solution_from_polynomial_curve_two`. The theorem treats a polynomial hypersurface in five affine coordinates and an arbitrary polynomial numerator. It takes the actual evaluated derivatives, a polynomial normal, inverse coordinate matrices, compatible commuting derivations, and polynomiality hypotheses as inputs. It supplies a tangent primitive for the second normal residue. The density and determinant identities below have more general field and dimension parameters where their statements allow them.

An application still constructs its curve family, proves dominance and the matrix identities, descends through any finite extension, and checks its coordinate transport, denominator legality, homogeneity, and exact certificate statement. The library does not assert that every hypersurface has such a family, or that a pole-one certificate can simply be multiplied into a higher-pole certificate.

| Module | Mathematical role |
| --- | --- |
| `HigherResidue` | Second-density transgression, determinant coefficients, and integration of a polynomial density with its tangent correction. |
| `NormalTaylor` | First and second Taylor identities separating normal and tangent derivatives. |
| `NormalJetBinding` | Binding those identities to actual polynomial gradients, Hessians, third derivatives, and rational source derivatives. |
| `JacobianJets` | First and second determinant jets for the moving coordinate matrix. |
| `NormalRowJets` | The corresponding identities for the row obtained from the hypersurface gradient. |
| `SourceDensityAlgebra` | Algebraic assembly of the numerator and Jacobian jets. |
| `HigherCurve` | The polynomial-curve residue primitive assembled from these ingredients. |

The original declaration namespaces are retained to preserve their mathematical interfaces. Import the shared modules for new applications; do not also import copies of these declarations from the accepted instance. Target-specific conic seeds, scalar weights, elliptic conversion, and physical certificate closure stay in the instance folder.

Build with `lake build HodgeComputer.Constructions.HigherResidues.HigherCurve`. As with the other shared constructions, additions require kernel replay and an application against the protected certificate statement. The original construction credits `1337isnot1337`'s elliptic companion method, `fqlx`'s moving-conic work, `HeadOfNaps`, the project contributors, Lean and mathlib; its adaptation and formalization were prepared for `fqlx` with OpenAI Codex assistance.
