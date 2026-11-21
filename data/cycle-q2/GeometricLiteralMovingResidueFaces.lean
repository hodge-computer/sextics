import Proposal.GeometricLiteralNativeDifferentialSections
import Proposal.GeometricSeedSectionDivisorTransitions
import Proposal.GeometricExteriorSheaf

/-!
# The ordered residue boundary for the moving Cartier equations

Use the equation of the second vertex to express each simple pole.
In the third frame the boundary of these lifts has regular numerator
e_k times dlog(e_j/e_k) wedged with the first edge differential.
The calculation divides only by an actual frame-change unit.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingResidueFaces

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionDivisorFrames
  CycleQ2SeedSectionSheafGlobal CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafImage

abbrev OneForms (W : Surface.Opens) : Type := DifferentialSheaf.val.obj (op W)

abbrev equationDifferential (W : Surface.Opens) (f : Γ(Surface,W)) : OneForms W :=
  (universalDifferential Surface.sheaf globalCoefficient).d (X := op W) f

/-- The original row evaluated at the moving section vector. -/
def frameEquation {W : Surface.Opens} (t : Fin 3 → ℂ) (j : FrameData W) : Γ(Surface,W) :=
  sectionRows t j.chart W j.within j.pivot.1

/-- Positive-divisor orientation for the original ideal frame change. -/
def positiveTransition {W : Surface.Opens} (j k : FrameData W) : Γ(Surface,W)ˣ :=
  (divisorTransition j k)⁻¹

theorem frameEquation_change {W : Surface.Opens} (t : Fin 3 → ℂ) (j k : FrameData W) :
    frameEquation t j = (positiveTransition j k : Γ(Surface,W)) * frameEquation t k := by
  have h := congrArg ((globalEvaluation t).app W) (generator_transition j k)
  rw [Scheme.Modules.Hom.app_smul] at h
  unfold generator at h
  rw [sourceGenerator_evaluation, sourceGenerator_evaluation] at h
  change frameEquation t k = (divisorTransition j k : Γ(Surface,W)) * frameEquation t j at h
  rw [h, ← mul_assoc]
  simp [positiveTransition]

/-- Writing the pole in the next frame separates off the regular dlog term. -/
theorem differential_change {W : Surface.Opens} (t : Fin 3 → ℂ) (j k : FrameData W) :
    ((positiveTransition j k)⁻¹ : Γ(Surface,W)ˣ).val • equationDifferential W (frameEquation t j) =
      equationDifferential W (frameEquation t k) +
        frameEquation t k • sheafLogDifferential W (positiveTransition j k) := by
  rw [frameEquation_change t j k]
  unfold equationDifferential
  rw [(universalDifferential Surface.sheaf globalCoefficient).d_mul]
  dsimp only [sheafLogDifferential]
  rw [smul_add, smul_smul, Units.inv_mul, one_smul]
  apply congrArg (_ + ·)
  exact smul_comm
    (↑((positiveTransition j k)⁻¹) : Γ(Surface,W)) (frameEquation t k)
    (equationDifferential W (positiveTransition j k : Γ(Surface,W)))

private def wedgeFirst (W : Surface.Opens) (β : OneForms W) :=
  (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W).comp
    (show OneForms W →ₗ[Surface.sheaf.obj.obj (op W)] ⋀[Surface.sheaf.obj.obj (op W)]^2 (OneForms W) from
      { toFun := fun α => exteriorPower.ιMulti (Surface.sheaf.obj.obj (op W)) 2 ![α,β]
        map_add' := fun α γ => (exteriorPower.ιMulti (Surface.sheaf.obj.obj (op W)) 2).map_vecCons_add ![β] α γ
        map_smul' := fun a α => (exteriorPower.ιMulti (Surface.sheaf.obj.obj (op W)) 2).map_vecCons_smul ![β] a α })

private theorem wedge_add_right (W : Surface.Opens) (α β γ : OneForms W) :
    wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![α, β + γ] =
      wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![α,β] +
      wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![α,γ] := by
  let F := exteriorPower.ιMulti (Surface.sheaf.obj.obj (op W)) 2 (M := OneForms W)
  have upd (b : OneForms W) : Function.update ![α,β] 1 b = ![α,b] := by
    funext i
    fin_cases i <;> rfl
  unfold wedgeSection
  rw [← map_add]
  apply congrArg (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W)
  simpa only [F, upd] using F.map_update_add ![α,β] 1 β γ

/-- The numerator of the second-vertex pole d(e_j)/e_j ∧ β in its own frame. -/
def poleNumerator {W : Surface.Opens} (t : Fin 3 → ℂ) (j : FrameData W) (β : OneForms W) :=
  wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![equationDifferential W (frameEquation t j), β]

/-- The ordered boundary in the last frame, for every moving parameter and every
triple-overlap differential cocycle. Multiplication by the last equation is
the local form of the inclusion of regular two-forms in simple-pole forms. -/
theorem poleNumerator_boundary {W : Surface.Opens} (t : Fin 3 → ℂ) (j k : FrameData W)
    (bᵢⱼ bⱼₖ bᵢₖ : OneForms W) (hb : bᵢₖ = bᵢⱼ + bⱼₖ) :
    poleNumerator t k bⱼₖ - poleNumerator t k bᵢₖ +
        ((positiveTransition j k)⁻¹ : Γ(Surface,W)ˣ).val • poleNumerator t j bᵢⱼ =
      frameEquation t k • wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
        ![sheafLogDifferential W (positiveTransition j k), bᵢⱼ] := by
  have h := congrArg (wedgeFirst W bᵢⱼ) (differential_change t j k)
  rw [map_smul, map_add, map_smul] at h
  rw [hb]
  unfold poleNumerator
  rw [wedge_add_right]
  change _ - (_ + _) + _ = _
  change _ • (poleNumerator t j bᵢⱼ) = poleNumerator t k bᵢⱼ + _ at h
  rw [show ((positiveTransition j k)⁻¹ : Γ(Surface,W)ˣ).val •
      wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![equationDifferential W (frameEquation t j), bᵢⱼ] =
      poleNumerator t k bᵢⱼ + frameEquation t k •
        wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![sheafLogDifferential W (positiveTransition j k), bᵢⱼ]
      from h]
  unfold poleNumerator
  abel

end CycleQ2LiteralMovingResidueFaces
end

#print axioms CycleQ2LiteralMovingResidueFaces.poleNumerator_boundary
