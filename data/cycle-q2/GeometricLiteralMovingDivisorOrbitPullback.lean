import Proposal.GeometricLiteralOrbitAction
import Proposal.GeometricSeedProjectiveImageCocycle
import Proposal.GeometricChartSectionPullback

/-!
# Pullback of the original dehomogenized equations by the projective action

A homogeneous numerator of degree n transforms by polynomial substitution and
the inverse nth power of the scalar acting on its chart denominator. The
formula holds in the actual structure sheaf on arbitrary subopens.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorOrbitPullback

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
  CycleQ2SeedCyclicAction CycleQ2SurfaceCoordinateSections
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralOrbitAction

/-- Scalar of the action on the three weight-one coordinates used in the cover. -/
def coordinateScale (z : ℂ) : Fin 3 → ℂ := ![z^2, z, 1]

theorem coordinateScale_ne_zero (z : ℂ) (hz : z ^ 3 = 1) (i : Fin 3) :
    coordinateScale z i ≠ 0 := by
  have h : z ≠ 0 := by rintro rfl; norm_num at hz
  fin_cases i <;> simp [coordinateScale, h]

theorem action_coordinateDen (z : ℂ) (hz : z^3 = 1) (i : Fin 3) :
    surfaceGradedAction z hz (coordinateDen 57 1 i.succ) =
      coordinateDen 57 1 i.succ * surfaceQuotient 57 1 (C (coordinateScale z i)) := by
  change surfaceAction z hz (surfaceQuotient 57 1 (X i.succ.castSucc)) = _
  rw [surfaceAction_polynomial, polynomialAction_X, ← map_mul]
  apply congrArg (surfaceQuotient 57 1)
  fin_cases i <;> simp [actionValues, coordinateScale, mul_comm]

theorem preimage_patch_le (z : ℂ) (hz : z^3 = 1) (i : Fin 3) :
    (closedProjectiveAction z hz).hom ⁻¹ᵁ Patch i ≤ Patch i :=
  Proj.basicOpen_mono (surfaceGrade 57 1) _ _ ⟨_, action_coordinateDen z hz i⟩

theorem preimage_patch (z : ℂ) (hz : z^3 = 1) (i : Fin 3) :
    (closedProjectiveAction z hz).hom ⁻¹ᵁ Patch i = Patch i := by
  apply le_antisymm (preimage_patch_le z hz i)
  apply Proj.basicOpen_mono (surfaceGrade 57 1)
  refine ⟨surfaceQuotient 57 1 (C (coordinateScale z i)⁻¹), ?_⟩
  rw [action_coordinateDen, mul_assoc]
  have hc : C (coordinateScale z i) * C (coordinateScale z i)⁻¹ = (1 : WeightedPoly) := by
    rw [← map_mul, mul_inv_cancel₀ (coordinateScale_ne_zero z hz i), map_one]
  rw [← map_mul, hc, map_one, mul_one]

theorem polynomialSection_pullback (z : ℂ) (hz : z^3 = 1) (i : Fin 3)
    (V W : Surface.Opens) (hi : V ≤ Patch i)
    (hW : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ V)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    (closedProjectiveAction z hz).hom.appLE V W hW (polynomialSection i V hi p) =
      polynomialSection i W
        ((hW.trans ((closedProjectiveAction z hz).hom.preimage_mono hi)).trans
          (preimage_patch_le z hz i))
        (C ((coordinateScale z i)⁻¹ ^ n) * polynomialAction z p) := by
  let f := surfaceGradedAction z hz
  let j := (closedProjectiveAction z hz).hom
  let a := coordinateDen 57 1 i.succ
  let c := coordinateScale z i
  let q := C (c⁻¹ ^ n) * polynomialAction z p
  have hq : q.IsWeightedHomogeneous weight n := by
    simpa only [zero_add] using (isWeightedHomogeneous_C weight (c⁻¹ ^ n)).mul (polynomialAction_weighted z hp)
  have hc : surfaceQuotient 57 1 (C c) ∈ surfaceGrade 57 1 0 :=
    surfaceQuotient_mem_grade 57 1 (isWeightedHomogeneous_C weight c)
  have he : f a = a * surfaceQuotient 57 1 (C c) := action_coordinateDen z hz i
  let x := homogeneousFraction 57 1 i.succ n p hp
  let y := homogeneousFraction 57 1 i.succ n q hq
  have hm : Away.map f a x = awayMap (surfaceGrade 57 1) hc he y := by
    apply HomogeneousLocalization.val_injective
    simp only [x, y, homogeneousFraction, Away.map_mk, awayMap_mk, Away.val_mk]
    have hnum : f (surfaceQuotient 57 1 p) =
        surfaceQuotient 57 1 q * surfaceQuotient 57 1 (C c) ^ n := by
      change surfaceAction z hz (surfaceQuotient 57 1 p) = _
      rw [surfaceAction_polynomial, ← map_pow, ← map_mul]
      apply congrArg (surfaceQuotient 57 1)
      dsimp only [q]
      rw [← map_pow, mul_right_comm, ← map_mul, ← mul_pow,
        inv_mul_cancel₀ (coordinateScale_ne_zero z hz i), one_pow, map_one, one_mul]
    rw [hnum]
  have ht := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f
    (cyclic_irrelevant_le_map f (surfaceAction_cube z hz)) (coordinate_mem_grade 57 1 i.succ)) x
  change j.appLE (Patch i) (j ⁻¹ᵁ Patch i) le_rfl ((Proj.awayToSection _ a) x) =
    (Proj.awayToSection _ (f a)) (Away.map f a x) at ht
  rw [hm] at ht
  have hr := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (surfaceGrade 57 1) hc he) y
  let hWV : W ≤ j ⁻¹ᵁ Patch i := hW.trans (j.preimage_mono hi)
  change j.appLE V W hW (coordinatePolynomialSection 57 1 i.succ V hi p) =
    coordinatePolynomialSection 57 1 i.succ W _ q
  rw [coordinatePolynomialSection_fraction 57 1 i.succ V hi n p hp,
    coordinatePolynomialSection_fraction 57 1 i.succ W _ n q hq]
  change j.appLE V W hW (Surface.presheaf.map (homOfLE hi).op ((Proj.awayToSection _ a) x)) = _
  rw [CycleQ2ChartSectionPullback.restriction_square j hi (le_refl _) hWV hW, ht]
  change Surface.presheaf.map (homOfLE hWV).op
    ((Proj.awayToSection _ (f a)) (awayMap _ hc he y)) = _
  rw [show (Proj.awayToSection _ (f a)) (awayMap _ hc he y) =
      Surface.presheaf.map (homOfLE (preimage_patch_le z hz i)).op ((Proj.awayToSection _ a) y) from hr]
  change (Surface.presheaf.map (homOfLE (preimage_patch_le z hz i)).op ≫
    Surface.presheaf.map (homOfLE hWV).op) ((Proj.awayToSection _ a) y) = _
  rw [← Functor.map_comp]
  rfl

end CycleQ2LiteralMovingDivisorOrbitPullback

end

#print axioms CycleQ2LiteralMovingDivisorOrbitPullback.preimage_patch
#print axioms CycleQ2LiteralMovingDivisorOrbitPullback.polynomialSection_pullback
