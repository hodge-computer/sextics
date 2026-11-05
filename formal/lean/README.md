# Shared Lean contract

This project pins Lean 4.33.0 and mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`; the Lake manifest pins transitive dependencies. Compiled artifacts and dependency caches are ignored.

`HodgeComputer/Verify.lean` defines `Verify F A q d D N Q` over `MvPolynomial (Fin 6) ℂ`. It requires a nonzero homogeneous denominator, numerator degrees, `IsRelPrime F D`, and the complete cleared certificate identity. It permits arbitrary denominator degree and nonzero quotient. `HasCertificate` existentially quantifies this witness. `localization_identity` justifies clearing denominators. Shared differential notation is in `HodgeTestbed/Algebra.lean`.

Instance-specific proofs live under `data/<id>/` and are compiled by the protected proposal verifier. It supplies target and witness modules, checks the theorem, replays candidate modules with `leanchecker`, and audits transitive axioms. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Prepare the shared dependencies with `lake exe cache get` and `lake build HodgeComputer.Verify`. Follow the complete local proof-checking instructions in `CONTRIBUTING.md` from the repository root. Local compilation is development feedback; formal acceptance is recorded by the trusted merged-PR publisher.
