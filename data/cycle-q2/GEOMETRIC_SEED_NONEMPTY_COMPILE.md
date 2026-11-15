# Seed-nonemptiness assembly: bounded compilation receipt

Date: 15 November 2026.
Assembly input: `d2e3431d12feaed2c812cea76ced186f77772cb7`.
Checked source commit: `5484700bcd82e8f64b02446e3abfe56512ad8092`.
Check branch: `fqlx/cycle-q2-bounded-compile-d2e3431-20261115` in `fqlx/sextics`.

## Outcome

**Two actual helper modules compiled successfully. The complete geometric
assembly did not compile: checking stopped at its first missing compiled
proposal import. The protected certificate is still incomplete.**

The successful source files were staged under `Proposal/` and compiled
without replacement definitions, theorem stubs, added assumptions, or new
admissions. The degree-gap file here is byte-for-byte the one that passed.
The inverse-ideal helper is unchanged. Their historical source-only header
comments predate this run; this receipt supersedes those comments for
exactly the hashes listed below, not for other modules or the full assembly.

## Exact compiler and results

Compiler: Lean 4.33.1, x86_64-unknown-linux-gnu, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

| Module | Exit | Elapsed seconds | Peak sampled process-group RSS (KiB) | Object |
| --- | ---: | ---: | ---: | --- |
| `GeometricSectionDegreeGap` | 0 | 2.333 | 3013972 | Created |
| `GeometricSectionInverseIdeal` | 0 | 2.338 | 2845448 | Created |
| `GeometricEmptySectionRows` | 1 | 0.712 | 1026904 | Not created: import missing |

`GeometricSeedSectionInverse`, `GeometricSeedConeSection`,
`GeometricSeedSectionNonempty`, and `GeometricFirstOrderNonemptyFlatCurve`
were not attempted after the failure. In particular, there is no compilation
receipt for `seed_specializedCurve_nonempty` or
`exists_nonempty_proper_flat_firstOrderCurve`.

The first blocking diagnostic was:

```text
Proposal/GeometricEmptySectionRows.lean:1:0: error: object file '/home/runner/work/sextics/sextics/formal/lean/.lake/build/lib/lean/Proposal/GeometricSectionUnitCech.olean' of module Proposal.GeometricSectionUnitCech does not exist
```

This is an unmet build prerequisite, not a successful check of the file and
not evidence that its mathematical argument is false. No automatic build
of the missing transitive geometry dependencies was launched.

## Printed axiom dependencies

```text
'CycleQ2SectionDegreeGap.lower_class_zero_of_multiple' depends on axioms: [propext, Classical.choice, Quot.sound]
'CycleQ2SectionInverseIdeal.recover' depends on axioms: [propext]
'CycleQ2SectionInverseIdeal.exists_unique_inverse_of_bezout' depends on axioms: [propext, Classical.choice, Quot.sound]
'CycleQ2SectionInverseIdeal.inverse_rescales_of_equiv' depends on axioms: [propext, Quot.sound]
```

These outputs contain no `sorryAx` or additional project axiom. They are
compiler `#print axioms` results for these four endpoints only. No independent
`leanchecker` replay or protected acceptance run was performed.

## Repair that was actually checked

The original degree-gap module imported all of `Mathlib.Tactic`. Under
`-M3072`, it terminated with a Lean memory exception before yielding an
object. The revised source imports only
`Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous` and
`Mathlib.RingTheory.Ideal.Quotient.Defs`; `omega`, tactic `ext`, and
`split_ifs` are replaced with elementary proof steps. All three theorem
statements are preserved exactly. The memory budget was not increased.

The intermediate narrow-import attempt exposed missing `Ideal.Quotient`
definitions. Adding the explicit quotient import produced the successful
result above. The unchanged inverse-ideal helper then also passed.

## Source and output identities

Source SHA-256:

```text
GeometricSectionDegreeGap.lean
  e536705d1ebd3ea41016f209624b5ac9e579b3c584c49c921151207189ab16cb
GeometricSectionInverseIdeal.lean
  6036d3ab6dfd6a3b605090d57e9f2e2422f8e4b56a5feb415fe8798a2ddbd1be
GeometricEmptySectionRows.lean
  11305a6c03fd8e7975b90720a5d52d2381e0dd36986ada7f01704e7115702d74
```

Output SHA-256:

```text
GeometricSectionDegreeGap.olean (122728 bytes)
  63454ef33cb7ee67dfd7a5c1f4f3b6645813c26f4475d126decef87f1c043165
GeometricSectionInverseIdeal.olean (163680 bytes)
  6f7bcfa4d9f2d137ce52d06cd9754c1413f2213a07f1fcf32cb82ba8caf7fbf8
```

The protected `data/cycle-q2/Solution.lean` blob remains
`3422e79fc263c2b098c61ce9a9577e303aefc009`, including its unchanged
`Submission.missing_geometric_existence` statement and original admission.
No workflow, target, manifest, shared-library, or verifier changes are
included in the proof-branch commit carrying this receipt.

## Run and artifact

[Bounded compilation run 43702141477](https://github.com/fqlx/sextics/actions/runs/43702141477)
completed with overall failure because of the missing import. Job:
`132775372874`. Artifact: `14157231460`, named
`cycle-q2-bounded-compile-43702141477`; retention seven days.

Artifact ZIP SHA-256:
`479637c83bc8ae925ff1022b7d6ad5872ff19556f51ead58e17c92172ee1052c`.
It contains the command logs, per-module JSON result records, runtime
preflight, pinned versions, protected blob check, and both compiled objects.
A downloaded copy is also attached to the conversation checkpoint.

All proof compilations ran sequentially with one Lean worker, a 3072 MiB
Lean-managed memory budget, a 4608 MiB sampled resident process-group
ceiling, a 1536 MiB available-memory reserve, and a 90-second per-module
wall deadline. No full project build was run. The prepared cache contains
pinned official dependency artifacts, not a claimed compiled version of
the source-only proposal geometry.

Earlier bounded attempts are retained as diagnostics, not successes:
run 43701246123 stopped during cache setup because file paths were relative
to the downstream project; run 43701467286 failed to read a core `.ir`
file under a virtual-address-space cap; run 43701682474 hit Lean's managed
memory limit with the broad import; run 43701940191 exposed the missing
explicit quotient import. Each follow-up changed the identified cause.

## Exact next compilation boundary

Prepare a source-hash-matched compiled dependency closure for
`Proposal.GeometricSectionUnitCech` under the pinned compiler and Mathlib.
The same staged environment must also contain the actual `HodgeTarget`
and other required `Proposal`/shared-library imports, without stubs or
admissions used as substitutes. Compile missing dependencies individually
in dependency order with bounded resources, preserving the logs.

Then, from the prepared `formal/lean` staging directory, resume with:

```sh
timeout --signal=TERM --kill-after=5s 90s \
  lake env lean -j1 -M3072 \
  -o .lake/build/lib/lean/Proposal/GeometricEmptySectionRows.olean \
  Proposal/GeometricEmptySectionRows.lean
```

Continue to the four unattempted modules only after that succeeds. The
resident-memory guard from the isolated workflow should also be retained.
Successful leaf compilation does not establish the missing Abel--Jacobi,
support, or protected affine residue-exactness comparisons.
