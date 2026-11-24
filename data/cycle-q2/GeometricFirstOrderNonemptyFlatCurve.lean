import Proposal.GeometricSeedSectionNonempty
import Proposal.GeometricFirstOrderFlatCurve

/-!
# The same proper flat first-order curve has a nonempty original closed fiber

The nonemptiness theorem applies to every original section vector, hence
in particular to the vector already chosen for the first-order flatness
construction. The existing seed-fiber isomorphism transports an actual
point. No replacement vector or auxiliary parameter family is used.

This endpoint remains source-only: its complete dependency chain and this
file have not finished compilation. It does not assert an Abel--Jacobi
or protected residue comparison. Prepared for fqlx with OpenAI ChatGPT
assistance, 15 November 2026.

## Actual bounded dependency compilation receipt, 15 November 2026

Source baseline: 2ec547c6da661aeb281db6ed4775ba38336b47f3.
Latest checked CI commit: 254a27089f855b048a4cf1794fcba6f21e3c9189.
Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

54 actual modules in this endpoint's 327-module dependency closure have
compiled successfully: 34 Proposal modules and 20 shared/generated modules.
The latest receipt reuses 39 hash-matched successes and records 15 new ones.
All 54 successful source hashes and emitted object hashes were verified
against the downloaded artifact. The actual .olean files are retained,
not merely their names or historical build claims.

These successes include GeometricSurfaceAdjunction, GeometricSeed,
GeometricSurfaceBindings, all four GeometricFormalInputs01 parts,
GeometricIncidenceTraceData, HigherResidue, the generated HodgeTarget,
and the unchanged shared HodgeComputer.Verify module. Compiling the
checker and target is not verification of Submission.certificate.

Last compiled module: Proposal.GeometricIncidenceTraceData.
Next unchecked module: Proposal.GeometricFormalInputs02Part01.
The last batch stopped normally at its configured bound, before starting
the next module. A green bounded-CI run is not a completed proposal build.

The accumulated 135 printed theorem-level axiom audits contain only
propext, Classical.choice, and Quot.sound; none contains sorryAx.
They cover the endpoints actually printed, not every declaration. There
was no independent leanchecker replay or protected acceptance run.

## Reproducible runs and retained binary artifacts

Run https://github.com/fqlx/sextics/actions/runs/43747495934:
16 successful dependencies, followed by a total-batch interruption.
Artifact 14175415801; ZIP SHA-256:
6f6b130b9873ebccca963c2a0021233382b177a2e93f3b27d1c46d9b670c3732

Run https://github.com/fqlx/sextics/actions/runs/43748269711:
the 16 successes were reused, then unchanged GeometricSurfaceAdjunction
compiled successfully in 88.597 seconds, with sampled peak RSS 3157612 KiB.
Artifact 14175013789; ZIP SHA-256:
98784a7c1e2bfab4bfef79d08b04c25ec2f5fe9cbebd0b999e4dec63d45a470c

Run https://github.com/fqlx/sextics/actions/runs/43748815087:
22 more modules compiled, giving 39. HigherResidue reached a default
heartbeat limit because the direct runner omitted the existing Lake
maxHeartbeats=0 setting. That attempt is not counted as a success.
Artifact 14175715953; ZIP SHA-256:
2839315959e00e5097e5e00af3e685fd0adf85ae15a4d51f053ee9b16a764e71

Run https://github.com/fqlx/sextics/actions/runs/43749434573:
the invocation was corrected to honor the existing Lake option; the
shared proof source was not changed. HigherResidue then passed in 31.383
seconds, followed by 14 more modules. All 54 objects are in this artifact.
Artifact 14176355553, q2-dependency-rebuild-43749434573, retained 30 days.
ZIP SHA-256:
f56889b0567227f3c4281ce142aaa781ec5f4b18bcb1e7a6251b103916591804

The isolated CI branch fqlx/q2-dependency-rebuild-20261115 contains the
resumable driver. It checks source and recursive dependency signatures,
compiler identity, and every cached artifact hash before reuse. Proof
compilations ran sequentially with one worker, a 5120 MiB Lean-managed
memory budget, a 6144 MiB resident-memory ceiling, and a 1536 MiB reserve.
The largest observed sampled RSS was 4892260 KiB. No memory guard fired.
The adjunction continuation had a 360-second module deadline; the later
batches used 180-second module deadlines and a 600-second batch bound.

## Exact remaining boundary

seed_specializedCurve_nonempty and this module are NOT thereby checked.
The supported-correspondence and protected residue-exactness formalizations
are not supplied by these dependency compilation results. The original
Submission.missing_geometric_existence admission remains unchanged.
Protected Solution.lean blob: 3422e79fc263c2b098c61ce9a9577e303aefc009.

No theorem statement, definition, or proof body was changed for this
checkpoint. Workflow and runner changes remain on the isolated CI branch,
not in the solve proposal. No full-project build or kernel replay ran.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FirstOrderNonemptyFlatCurve

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidencePolynomialJacobianBinding CycleQ2SpecializedProjectiveCurve
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderFlatCurve CycleQ2SeedSectionNonempty

/-- The closed first-order construction now retains both its original
seed-fiber isomorphism and actual nonemptiness of that fiber. -/
theorem exists_nonempty_proper_flat_firstOrderCurve :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅
        FirstOrderCurveSeedFiber t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (FirstOrderCurveSeedFiber t) := by
  obtain ⟨t, ht, hflat, hproper, ⟨e⟩⟩ := exists_proper_flat_firstOrderCurve
  obtain ⟨x⟩ := seed_specializedCurve_nonempty t
  exact ⟨t, ht, hflat, hproper, ⟨e⟩, ⟨x⟩, ⟨e.hom x⟩⟩

end CycleQ2FirstOrderNonemptyFlatCurve

end

#print axioms CycleQ2FirstOrderNonemptyFlatCurve.exists_nonempty_proper_flat_firstOrderCurve
