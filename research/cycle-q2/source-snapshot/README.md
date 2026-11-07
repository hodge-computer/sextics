# Cycle-q2 — Lean source plus research history

Start with **[RESEARCH_HISTORY.md](RESEARCH_HISTORY.md)** for the complete ledger of the approaches documented in the accessible record: what worked, what failed, what was withdrawn, and the exact remaining gaps. The ledger distinguishes partial source integration, auxiliary successes, scoped obstructions, modular searches, formal jets and tooling results.

The **[archived strategy atlas](research/ARCHIVED_STRATEGY_ATLAS.md)** preserves all 45 nodes from the recovered graph. **[Sources](research/SOURCES.md)** and the included report snapshots provide the documentary trail. Historical status labels are not new verification claims.

## Lean entry point

Open **[formal/CycleQ2Draft.lean](formal/CycleQ2Draft.lean)**. It retains the deliberate `sorry` in `missing_rational_solution`. The missing statement still requires the actual legal homogeneous rational solution. No complete cycle-q2 proof is included.

All eight `.lean` modules, toolchain pin and dependency configuration are byte-for-byte unchanged from `cycle_q2_lean_source.zip`. This snapshot uses Lean 4.33.0 and its pinned Mathlib revision. It is not silently merged with the separate 4.33.1 helper environment described in another project chat. No compiler, Mathlib cache or newly compiled `.olean` is included.

The original **[source-package README](README_SOURCE_SNAPSHOT.md)** and **[STATUS.json](STATUS.json)** are preserved for context. The saved draft is marked uncompiled. This update performed documentation, source/byte preservation and ZIP/link checks only; it did not run Lean or rerun historical mathematical checks.

## Where the missing mathematics is

The normalized equations are `2*N(F)=A*D` and `D*div(N)-N(grad D)=F^2*Q`, with the unchanged exact target and all legality/grading obligations. The existing original-coordinate partial current leaves a nonzero F² error. Normalization and denominator cancellation preserve that error; compilation alone does not eliminate it.

See Sections4–7 of the history for the exact tangent-correction equation, the coupled nine-class system, scope conflicts, and the do-not-repeat checklist.

## Integrity

`HANDOFF_CHECKS.json` records original-source preservation, the one explicit admission line, local documentary-link checks and packaging scope. `HANDOFF_MANIFEST.sha256` hashes the delivered files. These are not mathematical-proof receipts.
