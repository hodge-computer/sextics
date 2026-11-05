# Shared Lean contract

This project pins Lean 4.33.1 and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`; the Lake manifest pins transitive dependencies. Compiled artifacts and dependency caches are ignored.

[`HodgeComputer/Verify.lean`](HodgeComputer/Verify.lean) defines `HodgeComputer.Verify (n := n) F A d q D N Q` over `HodgeComputer.AmbientPoly n`, the ring `MvPolynomial (Fin (n + 1)) ℂ`. The parameters `n`, `d`, and `q` are natural numbers; `d` is the degree of `F`. The contract requires:

- `F ≠ 0` and `F.IsHomogeneous d`;
- `A` homogeneous of integer degree `d * (q + 1) - (n + 1)`;
- `D ≠ 0` and `D.IsHomogeneous D.totalDegree`;
- each `N i` homogeneous of integer degree `D.totalDegree + d * q - n`;
- `IsRelPrime F D` and the complete cleared certificate identity.

The integer-degree predicate `HodgeComputer.Homogeneous` permits only the zero polynomial in negative degrees. The denominator degree is unrestricted, and the quotient `Q` may be nonzero. `HodgeComputer.HasCertificate F q A` means that such `D`, `N`, and `Q` exist, using `F.totalDegree` for `d` and inferring `n` from the common polynomial ring. The witness interface `Verify` retains an explicit `d`; `Verify.hasCertificate` derives the existence statement from a verified witness. `localization_identity` relates their cleared identity to the rational field `N / D`. See the [formal contract](../README.md) for the equation and its meaning.

The catalogue uses `n = 5` and `d = 6`. Six-variable notation for its constructions is in [`HodgeComputer/Sextic.lean`](HodgeComputer/Sextic.lean), under `HodgeComputer.Sextic`; it is separate from the general verifier. Shared differential notation is in [`HodgeTestbed/Algebra.lean`](HodgeTestbed/Algebra.lean).

Instance-specific proofs live under `data/<id>/` and are compiled by the protected proposal verifier. It supplies target and witness modules, checks the theorem, replays candidate modules with `leanchecker`, and audits transitive axioms. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

From this directory, prepare the shared dependencies with `lake exe cache get` and `lake build HodgeComputer.Verify`. Follow the complete [local proof-checking instructions](../../CONTRIBUTING.md#local-verification) from the repository root. Local compilation is development feedback; the protected checks and owner merge precede publication of contributor credit.

For shared-library and toolchain maintenance, see [MAINTAINING.md](../../MAINTAINING.md#publication-and-maintained-proofs).
