# The holdout Fermat cover

This library extracts the 58 helper modules from `fqlx`'s accepted [PR #128](https://github.com/hodge-computer/sextics/pull/128), retaining their construction and attribution. Their import paths begin with `HodgeComputer.Constructions.HoldoutCover` instead of the submission-local `Proposal` namespace. The instance sources under `data/holdout/` and the shared modules are maintained against the current verifier.

The fixed physical equation is

\[
F=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6
  +X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2.
\]

The library constructs the cover with \(T^6=Y_0^6+Y_2^6\), the Fermat coefficient field, its weighted quotient, a moving conic through the generic point, polynomial integration, finite trace, and legal homogeneous certificate clearing. The [original explanation](../../../../../data/holdout/solution.md) develops the argument and credits its mathematical and formal dependencies.

## Entry points

- `PolynomialNormal.lean`: generic coefficient linear algebra constructs a polynomial normal. `polynomial_linear_combination_one` cancels positive coefficients around a prescribed constant direction; `full_polynomial_combination_one` instead solves for the constant term and positive coefficients together. The latter applies to the mixed-polar Jacobian incidence.
- `ConicResidue.lean`: `HoldoutConicIncidence.conic_target_residue_solution` gives a residue primitive for every polynomial source on the fixed weighted quotient.
- `GeneralizedCover.lean`: `HoldoutGeneralization.certificate_of_source_pair` converts a homogeneous degree-six physical target into a certificate when the application supplies its quotient-source identity, its normal derivative identity, and a trace-zero correction.
- `GeneralizedCover.lean`: `trace_square` and `trace_inverse_square` complement the accepted `commonCover_trace_inverse_fourth` character calculation.
- `CoverCertificate.lean`: the original assembly for the central source remains available.

An application imports `HodgeComputer.Constructions.HoldoutCover.GeneralizedCover`, defines its target and quotient source, and proves the required exact identities. It must still close the protected `HodgeSubmission` theorem. The library makes no claim that every degree-six source has such identities, and it does not export an expanded denominator.

## Maintenance and credit

Shared changes belong in a maintenance PR; individual solve PRs only add their instance-specific files. Recheck affected accepted proofs and preserve their original attribution. The original holdout application and the later specializations import these shared modules directly. The original declaration namespaces and attribution are retained.

The Fermat-cover and moving-conic construction is due to `fqlx`, with the collaborators, prior work, and AI assistance acknowledged in the accepted explanation and source comments. The target-parameterized assembly, additional trace characters and full-coefficient normal lemma were prepared with OpenAI Codex assistance for `benediamond`. Moving the code into the library does not itself earn a solve point or change any existing credit.

From `formal/lean`, build the public entry point with:

```sh
lake build HodgeComputer.Constructions.HoldoutCover.GeneralizedCover
```

After changing this library, check an application against its protected target and replay the library with `leanchecker`. The solve workflow's dependency-cache key includes all shared Lean sources, so changed machinery cannot reuse an unchanged cache key.
