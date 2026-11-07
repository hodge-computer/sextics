# Symmetric sextic: partial primitive transport

This draft contains the latest primitive/current endpoints and their local Lean
dependencies from the supplied research packet.
Prepared for `fqlx` with OpenAI Codex assistance; original source attributions
are retained. The shared research record is [Discussion #117](https://github.com/hodge-computer/sextics/discussions/117).

**The protected `HasCertificate F 1 A` theorem remains unproved in this packet.**
The repository's [mathematical context](../../data/symmetric-sextic-residual/why.md)
documents geometric existence; this is a partial formalization of that argument.

## Source and remaining proof gaps

- [SymmetricPrimitiveEndpoint.lean](source-snapshot/SymmetricPrimitiveEndpoint.lean)
  defines the three rational primitive coefficients on the actual chart function
  field. Given those coefficients and their differential equation,
  `clear_relative_primitive` produces legal affine polynomial data with a
  nonzero denominator relatively prime to the chart equation and a full cleared
  defect divisible by its square.
- [SymmetricRegularCurrent.lean](source-snapshot/SymmetricRegularCurrent.lean)
  gives the earlier conditional homogeneous certificate endpoint.
- [ContactResidueAnnihilator.lean](source-snapshot/ContactResidueAnnihilator.lean)
  and [WeightedFiberSmoothness.lean](source-snapshot/WeightedFiberSmoothness.lean)
  supply the contact identities and exact weighted-fiber smoothness step.

[modules.json](source-snapshot/modules.json) lists the 19 retained modules in
dependency order. All their local Lean imports are included; generated matrix
modules and earlier solver experiments are outside this dependency closure.
The Lean source is unchanged from the downloaded packet.

Still required: the actual contact/cohomology identification, formal finite
witnesses, support-to-function-field exactness giving
`Nonempty SymmetricPrimitiveEndpoint.RelativePrimitive`, and the final
affine-to-homogeneous assembly. Finite contact rank alone supplies no primitive.

## Verification and reproduction

[Import checks](IMPORT_CHECKS.json) and [source hashes](SOURCE_SHA256)
describe this focused selection. Four small [verification receipts](verification/)
record the original import's successful exact Python replays: contact rank 48,
the contact smoothness minor, five source/Jacobian identities, and a trace-weight
closedness countermodel. The first two require the larger witnesses linked below.
The source/Jacobian audit and countermodel scripts remain in this directory and
were rerun after trimming. The countermodel concerns a shortcut, not nonexistence
of a certificate for this instance.

**No Lean compilation, kernel replay, or fresh transitive axiom audit was run
for this import or this trim.** The full packet's earlier Lean receipts are
historical evidence. Repository content checks are separate from Lean acceptance.

For Lean reproduction, prepare a separate Sextics checkout at
`ca173aad142bd5f6bf5dd156b6798223a45df54f`, with Lean 4.33.1 and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. In its `formal/lean/`, run
`lake exe cache get` and `lake build HodgeComputer`. Then, in a scratch copy of
the retained source directory:

```sh
python3 verify_partial.py --repo /path/to/pinned/sextics
python3 audit_primitive_transport.py --repo /path/to/pinned/sextics
python3 audit_contact_steps.py --repo /path/to/pinned/sextics
python3 weighted_primitive_transport_source_audit.py
python3 trace_closedness_counterexample.py
```

The last two use Python 3.11 and `sympy==1.14.0`; the countermodel uses only the
standard library. The verifier enforces the pinned checkout and compiles the
reduced module list. Its receipt description was updated to match this scope.
The scripts write outputs beside their source; generated logs and objects are
excluded from Git.

## Optional historical evidence

The [complete earlier import](https://github.com/fqlx/sextics/tree/dde07deff352489809e66f2306955a7316b799e1/research/symmetric-sextic-residual)
preserves the contact witnesses, independent rational checkers, historical
receipts, reports, and solver transcripts. They remain accessible at that
immutable commit, outside this PR's final file diff. The original ZIP has SHA-256
`51ff792e036f2831fbee654a1699332448d91c9e40b493edd99fce83ada7e933`.
No large external checkpoint parts were downloaded.

This draft adds research source only; it supplies no solve manifest or accepted
solution and changes no protected target or maintained Lean module.
