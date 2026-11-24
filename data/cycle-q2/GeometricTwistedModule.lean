import Proposal.GeometricTwistedModuleCore
import Proposal.GeometricProjectiveCech

/-!
# The actual degree-one sheaf as a sheaf of structure-ring modules

The generic action constructed in `GeometricTwistedModuleCore` is specialized
to the actual projective curve and its two covering denominator opens from
`GeometricProjectiveCech`. Forgetting the action gives literally the same
additive kernel sheaf used by the existing Cech and cohomology constructions.

The two frames are linear over the actual structure-sheaf sections on every
subopen, and their naturality and transition remain those proved in the core.
For `r ≠ 0`, the proved two-open cover gives a rank-one linear frame near every
point. Both complex parameters are retained without specialization.

The canonical-sheaf and geometric Serre-trace comparisons are separate results.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry


/-- The actual degree-one sheaf on the actual projective curve, now with
its structure-sheaf module structure. -/
def degreeOneModuleSheaf (r θ : ℂ) :
    SheafOfModules.{0} (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf) :=
  TwistedModule.moduleSheaf (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)

theorem degreeOneModuleSheaf_toSheaf (r θ : ℂ) :
    (SheafOfModules.toSheaf (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf)).obj
        (degreeOneModuleSheaf r θ) = degreeOneSheaf r θ := rfl

/-- A specialized instance makes the scalar structure explicit at the
existing public `degreeOneSheaf` interface. It is the same transported action. -/
instance degreeOneSectionsModule (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O) ((degreeOneSheaf r θ).obj.obj (op O)) :=
  TwistedModule.sectionsModule (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O

/-- On each actual covering chart, and every subopen of it, the original
section group is a free rank-one module, exhibited by a linear frame.
The naturality theorems above retain the full local trivialization data. -/
theorem degreeOne_linear_frames (r θ : ℂ) :
    (∀ (O : (projectiveCurve r θ).Opens) (hO : O ≤ firstProjectivePatch r θ),
      Nonempty ((degreeOneSheaf r θ).obj.obj (op O) ≃ₗ[Γ(projectiveCurve r θ, O)]
        Γ(projectiveCurve r θ, O))) ∧
    (∀ (O : (projectiveCurve r θ).Opens) (hO : O ≤ secondProjectivePatch r θ),
      Nonempty ((degreeOneSheaf r θ).obj.obj (op O) ≃ₗ[Γ(projectiveCurve r θ, O)]
        Γ(projectiveCurve r θ, O))) := by
  constructor
  · intro O hO
    exact ⟨TwistedModule.firstLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO⟩
  · intro O hO
    exact ⟨TwistedModule.secondLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO⟩

/-- The proved two-open cover makes the linear frames genuinely local at
every point of the actual projective curve. This does not assume a cover or
an unidentified line bundle as extra geometric input. -/
theorem degreeOne_local_frames_cover (r θ : ℂ) (hr : r ≠ 0)
    (x : projectiveCurve r θ) :
    ∃ O : (projectiveCurve r θ).Opens, x ∈ O ∧
      ∀ (P : (projectiveCurve r θ).Opens), P ≤ O →
        Nonempty ((degreeOneSheaf r θ).obj.obj (op P) ≃ₗ[Γ(projectiveCurve r θ, P)]
          Γ(projectiveCurve r θ, P)) := by
  have hx : x ∈ firstProjectivePatch r θ ⊔ secondProjectivePatch r θ := by
    rw [projective_twoOpen_cover r θ hr]
    trivial
  rcases (show x ∈ firstProjectivePatch r θ ∨ x ∈ secondProjectivePatch r θ from hx) with
    hx | hx
  · exact ⟨firstProjectivePatch r θ, hx, (degreeOne_linear_frames r θ).1⟩
  · exact ⟨secondProjectivePatch r θ, hx, (degreeOne_linear_frames r θ).2⟩

end CycleQ2GeometricProjectiveCurve

end
