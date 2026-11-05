# Elliptic companion algebra

Target-independent residue and elliptic contraction machinery extracted from the accepted crossed-ternary construction of `1337isnot1337`. The original declaration namespaces are retained; the shared modules and instance sources are maintained against the current verifier, with original attribution preserved. See [the construction explanation](../../../../../data/crossed-ternary-asymmetric/solution.md) for mathematical attribution, collaborators, and disclosed AI assistance.

The entry point `Contraction` proves `CrossedElliptic.product_divergence` for arbitrary characteristic-zero fields, two groups of derivations, and supplied scalar primitives with the required independence. It does not construct those primitives or identify any application target.

`CompanionAlgebra` contains generic incidence opens, normals, monic hypersurface derivations, and affine residue-data clearing. `Residues`, `Coordinates`, `Calculus`, `Kernels`, `Translation`, and `Infinity` implement the field, rational residues, coefficient derivations, translated pole separation, and infinity correction used by `Contraction`. Target-specific companion equations, seeds, domain proofs, scalar sources, and physical certificate closure are not extracted.

`ScalarEmbedding` parameterizes the monic companion cubic and its injective elliptic substitution by an arbitrary two-variable polynomial. `AffineCompanion` supplies the required irreducibility when that polynomial has constant term one. These modules justify denominator preservation under the substitution; they do not construct a scalar primitive or extend a source's pole order.

The library's elliptic curve is the Fermat cubic, equivalently the Weierstrass model `y² = x³ − 432`; the contraction is not stated for an arbitrary elliptic curve. Its mathematical account is [Chapter 3A](../../../../../docs/03a-split-and-k3.md).

| Module | Mathematical role |
| --- | --- |
| `CompanionAlgebra` | Weighted coordinate embeddings, incidence opens, normals, and affine residue clearing. |
| `Residues` | Rational residues, coefficient differentiation, and derivative-compatible descent. |
| `Coordinates` | The elliptic function field, Fermat coordinates, translation, and their field maps. |
| `Calculus` | Elliptic and coefficient derivations and their compatibility with translation. |
| `Kernels` | Theta kernels, local residue pairings, and base change. |
| `Translation` | Regularity after translation and separation of finite pole sets. |
| `Infinity` | The infinity correction needed for the full residue identity. |
| `Contraction` | Pole splitting, trace descent, and the product-divergence theorem. |
| `ScalarEmbedding` | Injective substitution of a parameterized companion cubic into the Fermat elliptic field. |
| `AffineCompanion` | Irreducibility of that companion when its affine polynomial has constant term one. |

Build both entry points with `lake build HodgeComputer.Constructions.EllipticCompanions.Contraction HodgeComputer.Constructions.EllipticCompanions.AffineCompanion`. New applications must independently establish their companion primitives, exact target transport, nonzero/legal denominators, homogeneity, and the protected certificate theorem.
