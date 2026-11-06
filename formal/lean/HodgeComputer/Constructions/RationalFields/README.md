# Rational vector fields and residue corrections

These modules are extracted from `benediamond`’s [dense two-ternary Hessian construction](../../../../../data/two-ternary-dense-two-odd-hessian-d48/solution.md) ([#41](https://github.com/hodge-computer/sextics/pull/41)). The application explanation retains its mathematical attribution and assistance disclosure. Declaration names remain in `HodgeTestbed.Conic`.

| Module | Entry point | Required input |
| --- | --- | --- |
| `Calculus` | `fieldAction`, `fieldDivergence`, `fieldBracket`; action and divergence of the bracket | Bundled coordinate derivations; commutation where the theorem requires it. |
| `ResidueReduction` | `residueCorrection_game` | A normal field with `n(F) = 1`, commuting coordinates, and the displayed primitive identity. |
| `EulerCorrection` | `eulerCorrection_strict`, `residue_euler_strict` | `E(F) = 6F`, `div E = 6`, and the stated degree-zero condition on the raw divergence. |
| `Homogenization` | `HomogeneousChart`, `homogenizedField_strict` | The actual five-to-six-variable chart derivative rules, plus the residue primitive. |
| `ReflectionCover` | `coverField_game`, `coverField_game_half` | The square-cover and derivative identities displayed in the theorem. |

The calculus works for abstract algebraic derivations; the homogenization and Euler normalization retain their sextic dimensions and constants. No generic smoothness claim or target certificate is hidden in these interfaces. The dense application supplies its coordinate fields, embeddings, normal and primitive, then clears denominators and checks the protected polynomial certificate.
