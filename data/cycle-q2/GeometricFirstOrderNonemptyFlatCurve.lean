import Proposal.GeometricSeedSectionNonempty
import Proposal.GeometricFirstOrderFlatCurve

/-!
# The same proper flat first-order curve has a nonempty original closed fiber

The nonemptiness theorem applies to every original section vector, hence
in particular to the vector already chosen for the first-order flatness
construction. The existing seed-fiber isomorphism transports an actual
point. No replacement vector or auxiliary parameter family is used.

Source-only draft. Not elaborated, compiled, or kernel-replayed.
This does not assert an Abel--Jacobi or protected residue comparison.
Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.

## Bounded dependency compilation checkpoint, 15 November 2026

CI run 43747495934 at d02d69db5a896d6030430ce2d445006fbd18cbd0
compiled 16 actual dependency modules, through GeometricChartKaehler,
with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The 33 printed theorem-level axiom audits contain only propext,
Classical.choice, and Quot.sound. This is not independent kernel replay.
All 16 successful source hashes and all 16 emitted object hashes were
checked against the downloaded receipt. Unlike the old source-only
checkpoint, this artifact retains the actual compiled objects.

Run: https://github.com/fqlx/sextics/actions/runs/43747495934
Artifact: 14175415801, q2-dependency-rebuild-43747495934, retained 30 days.
Artifact ZIP SHA-256:
6f6b130b9873ebccca963c2a0021233382b177a2e93f3b27d1c46d9b670c3732

The total batch deadline interrupted GeometricSurfaceAdjunction before
an object or Lean error was produced. A separate bounded continuation
then reused all 16 source-and-object-hash-matched dependencies and compiled
that unchanged module successfully: exit 0, 88.597 seconds, peak sampled
resident memory 3157612 KiB, no memory-guard stop. It emitted the actual
GeometricSurfaceAdjunction.olean. All 17 successful source and object
hashes were checked against the downloaded continuation receipt.

Continuation run: https://github.com/fqlx/sextics/actions/runs/43748269711
Checked commit: b25a5fd1fdd822bc667c5032bbfb9df986475327
Artifact: 14175013789, q2-dependency-rebuild-43748269711, retained 30 days.
Artifact ZIP SHA-256:
98784a7c1e2bfab4bfef79d08b04c25ec2f5fe9cbebd0b999e4dec63d45a470c
Surface-adjunction source SHA-256:
00acf5c0ffb3107422834a0ce5ec02fa6a2c90897c86df2d4c60c0e9834ed3a3
Surface-adjunction object SHA-256:
c49570d30e9ac7fb57731bfbb8facffbd8672d4eb142e33d18c5a8c098254f42

The continuation stopped normally at its one-new-module bound; the next
unchecked module was GeometricSeedConormalBases. The selected dependency
closure contains 327 modules; 17 successes are not a complete build.
SurfaceAdjunction contains no printed theorem-level axiom audit; the 33
audits above concern the first 16 modules only. No independent kernel
replay or protected acceptance run was performed.

The remaining dependency chain, seed_specializedCurve_nonempty, and this
module are NOT thereby checked. The original protected existence
admission remains unchanged. These checkpoint notes change no definition,
theorem statement, or proof body.
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