# Recovered cycle-q2 Lean source — incomplete development draft

These are the original source bytes recovered from `cycle_q2_normalized.zip`.
The Lean modules and configuration have not been edited or regenerated.

## Start here

- `formal/CycleQ2Draft.lean`: entry point, with the explicit `sorry` in
  `CycleQ2Draft.missing_rational_solution` and the dependent `certificate_draft`.
- `formal/CycleQ2Workspace.lean`: literal original F, A, q=2, OriginalGoal,
  and fixed-denominator algebra.
- `formal/CycleQ2Assembly.lean`: normalized witness structure and conditional
  assembly/correction lemmas.
- `formal/CycleQ2Normalization.lean`: same-denominator radial normalization
  and equivalence with the original existential target.
- `formal/HodgeComputer/Verify.lean` and `formal/HodgeTestbed/Algebra.lean`:
  the verifier/algebra sources bundled with the saved workspace.
- `formal/HodgeComputer.lean` and `formal/HodgeTestbed.lean`: import roots.

## Exact remaining admission

```lean
theorem missing_rational_solution : Nonempty NormalizedRationalSolution := by
  sorry
```

There is one explicit `sorry` line across the eight Lean modules.
This is a source-text count, not a compiler or axiom audit. The missing theorem
requires the legal homogeneous denominator, six numerators, quotient, and both
normalized equations. The large compiled physical-current transport has not
been formalized in this source package.

## Recorded verification status

The original `STATUS.json` is preserved unchanged. It records that these source
files were NOT compiled, no kernel replay was performed, and no full original
certificate was constructed. No new Lean build was attempted while retrieving
and packaging this source handoff. The source bodies may still require repair
once the pinned compiler runs.

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0`
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
- `formal/lake-manifest.json` retains the dependency lock.

Compiler binaries, Mathlib source/cache, and compiled `.olean` files are NOT
included in this source-only handoff. Use the accompanying original full
workspace for its setup and build-check scripts. In a prepared pinned environment,
the draft build command from `formal` is:

```sh
lake build CycleQ2Draft
```

A successful draft build still would not be a complete proof while the admission
remains. Do not confuse this 4.33.0 source snapshot with the separate 4.33.1 setup
reported in another Math-project chat.

## Recovery provenance

`RECOVERY_MANIFEST.json` lists each copied file and its SHA-256. All copied files
were compared byte-for-byte with their original ZIP members. ZIP CRC checking,
byte comparison, and explicit-hole counting are the only new checks performed.
