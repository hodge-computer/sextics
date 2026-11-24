import Proposal.GeometricLiteralAbelJacobiSeedLiftRegular
import Proposal.GeometricLiteralAbelJacobiSeedLift
import Proposal.GeometricLiteralAbelJacobiCubicNonzero
import Proposal.GeometricSeedProjectiveImageChart

/-!
# The nonzero normal on the same smooth moving section

The seed cone embeds into its localization at the first of the three weight-one
Čech coordinates. For a homogeneous element, dehomogenization at this coordinate
therefore detects zero. Applying this to each graded component of an annihilator
transfers regularity of the selected affine row to the ordinary cone pivot.
The low-degree cubic nonvanishing theorem then applies to the same section.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLiftConeRegular

open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceNormalForm CycleQ2IncidenceImageLine
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection CycleQ2RelativeConstantSection
  CycleQ2RelativeCurveChart CycleQ2SeedConeSection CycleQ2SegreFactorChartExact
  CycleQ2FirstOrderCurveChartFlat CycleQ2LiteralAbelJacobiSeedLiftRegular

attribute [local instance] CycleQ2SeedConeSection.pointSurfaceCommRing
  CycleQ2SeedConeSection.seedCommRing CycleQ2SeedConeSection.chartCommRing
  CycleQ2SeedProjectiveImageChart.cone_isLocalization
  CycleQ2GeometricIncidenceProj.surfaceGradedRing

private abbrev index : Fin 4 := (0 : Fin 3).succ
private abbrev chartring := DehomogenizedRing seed index
private abbrev cone := PointSurface seed
private abbrev d : cone →+* chartring := surfaceToDehomogenized seed index

private theorem coordinate_unit :
    IsUnit (toCone {0} (surfaceQuotient seed (X index.castSucc))) := by
  let u := CycleQ2SeedProjectiveImageChart.localizingCoordinate (0 : Fin 3)
  have he : literalToSeed (surfaceQuotient seed (X index.castSucc)) = u := by
    change literalToSeed (Ideal.Quotient.mk (pointEquations seed) (X index.castSucc)) = u
    rw [literalToSeed_polynomial]
    dsimp only [u]
    rw [CycleQ2SeedProjectiveImageChart.localizingCoordinate_eq]
    exact (CycleQ2GeometricSurfaceCoordinates.seedRingEquiv_quotient _ _).symm
  change IsUnit (algebraMap A (Chart {0}) (literalToSeed _))
  rw [he]
  exact IsLocalization.Away.algebraMap_isUnit u

private theorem coordinateLocalization_injective :
    Function.Injective (algebraMap cone (CoordinateLocalization seed index)) := by
  let g := IsLocalization.Away.lift (S := CoordinateLocalization seed index)
    (g := (toCone {0}).toRingHom) (surfaceQuotient seed (X index.castSucc)) coordinate_unit
  have h (b : cone) :
      g (algebraMap cone (CoordinateLocalization seed index) b) = toCone {0} b :=
    IsLocalization.Away.lift_eq _ _ b
  intro b c he
  have hh := congrArg g he
  rw [h, h] at hh
  exact literalToSeed.injective
    (CycleQ2SeedCechGlobalGluing.localization_injective ℂ (57 : ℂ) Complex.I {0} hh)

private theorem zero_of_dehomogenized {n : ℕ} {b : cone} (hb : b ∈ surfaceGrade seed n)
    (hz : d b = 0) : b = 0 := by
  obtain ⟨p, hp, rfl⟩ := hb
  change surfaceQuotient seed p = 0
  have H : homogeneousFraction seed index n p hp = 0 := by
    apply (familyCoordinateChartEquiv seed index).injective
    rw [familyCoordinateChartEquiv_homogeneousFraction, map_zero]
    exact hz
  have hh := congrArg HomogeneousLocalization.val H
  rw [homogeneousFraction_val, HomogeneousLocalization.val_zero] at hh
  let g := surfaceQuotient seed (X index.castSucc)
  have hu : IsUnit (IsLocalization.Away.invSelf (S := CoordinateLocalization seed index) g) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap cone (CoordinateLocalization seed index) g,
      (mul_comm _ _).trans (IsLocalization.Away.mul_invSelf g)⟩
  apply coordinateLocalization_injective
  rw [map_zero]
  apply (hu.pow n).mul_right_cancel
  rw [zero_mul]
  exact hh

private theorem homogeneous_annihilator_zero (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart)
    (reg : IsSMulRegular (SeedRefinement index p) (seedRefinedEquation t index p))
    {n : ℕ} (b : cone) (hb : b ∈ surfaceGrade seed n)
    (h : constantEquation seed t p.1 * b = 0) :
    algebraMap cone (CoefficientPivot seed p) b = 0 := by
  let u := basePivot seed p
  let f := algebraMap chartring (SeedRefinement index p)
  have he : f (d (constantEquation seed t p.1)) = seedRefinedEquation t index p := by
    rw [← relativeEquation_complex]
    rfl
  have hfb : f (d b) = 0 := by
    apply reg.right_eq_zero_of_smul
    change seedRefinedEquation t index p * f (d b) = 0
    rw [← he, ← map_mul, ← map_mul, h, map_zero, map_zero]
  have hz : f (d b) = f 0 := hfb.trans f.map_zero.symm
  obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (S := SeedRefinement index p)
    (seedPivot index p) hz
  have hz' : d (u ^ N * b) = 0 := by
    rw [map_mul, map_pow]
    exact hN.trans (mul_zero _)
  have hb' := zero_of_dehomogenized
    (SetLike.mul_mem_graded (SetLike.pow_mem_graded N (basePivot_homogeneous seed p)) hb) hz'
  have hh := congrArg (algebraMap cone (CoefficientPivot seed p)) hb'
  rw [map_mul, map_pow, map_zero] at hh
  apply ((IsLocalization.Away.algebraMap_isUnit (S := CoefficientPivot seed p) u).pow N).mul_left_cancel
  simpa only [mul_zero] using hh

/-- Regularity on a single faithful weight-one chart implies regularity of the
same original row on the homogeneous cone pivot. -/
theorem coefficientPivot_regular_of_affine (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart)
    (reg : IsSMulRegular (SeedRefinement index p) (seedRefinedEquation t index p)) :
    IsSMulRegular (CoefficientPivot seed p)
      (algebraMap cone (CoefficientPivot seed p) (constantEquation seed t p.1)) := by
  classical
  let u := basePivot seed p
  let f := algebraMap cone (CoefficientPivot seed p)
  let a := constantEquation seed t p.1
  have hu : IsUnit (f u) := IsLocalization.Away.algebraMap_isUnit u
  have hbase (b : cone) (hab : a * b = 0) : f b = 0 := by
    rw [← DirectSum.sum_support_decompose (surfaceGrade seed) b, map_sum]
    apply Finset.sum_eq_zero
    intro n _
    apply homogeneous_annihilator_zero t p reg _ (DirectSum.decompose (surfaceGrade seed) b n).property
    rw [← DirectSum.coe_decompose_mul_add_of_left_mem _ (constantEquation_homogeneous seed t p.1)]
    change constantEquation seed t p.1 * b = 0 at hab
    simp [hab]
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  obtain ⟨l, b, hbl⟩ := IsLocalization.Away.surj u z
  have hfb : f (a * b) = f 0 := by
    change f a * z = 0 at hz
    rw [map_mul, ← hbl, ← mul_assoc, hz, zero_mul, map_zero]
  obtain ⟨j, hj⟩ := IsLocalization.Away.exists_of_eq (S := CoefficientPivot seed p) u hfb
  have hj' : a * (u ^ j * b) = 0 := by
    rw [mul_left_comm, hj, mul_zero]
  have hh := hbase (u ^ j * b) hj'
  rw [map_mul, map_pow] at hh
  have hzero : f b = 0 := (hu.pow j).mul_left_cancel (by simpa only [mul_zero] using hh)
  apply (hu.pow l).mul_right_cancel
  rw [zero_mul]
  exact hbl.trans hzero

open CycleQ2SpecializedProjectiveCurve

theorem coefficientPivot_regular_of_smooth_seed (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t))
    (p : CycleQ2SegreCech.Chart) :
    IsSMulRegular (CoefficientPivot seed p)
      (algebraMap cone (CoefficientPivot seed p) (constantEquation seed t p.1)) :=
  coefficientPivot_regular_of_affine t p (seedRefinedEquation_regular t hs index p)

open CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralAbelJacobiCubicNonzero
  CycleQ2LiteralAbelJacobiCubicNonzeroSeed CycleQ2FirstOrderChartReduction
  CycleQ2IncidenceEtaleParameter CycleQ2RelativeConstantCurve
  CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra

/-- The original cubic detects the embedded normal on a chart of this same
smooth member, whose moving projective family has a smooth proper neighborhood. -/
theorem smooth_neighborhood_and_nonzero_normal (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) :
    (∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
      Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V)) ∧
    ∃ hf : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
      ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
        ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_chart_nonzero t (coefficientPivot_regular_of_smooth_seed t hs)
    firstOrderWeightedCubic.val 3 firstOrderWeightedCubic.property (by decide) seed_cubic_ne_zero
  refine ⟨CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_smooth_seed t hs,
    firstOrderCurveChart_flat_of_smooth_seed t hs, j, ?_⟩
  let := firstOrderCurveChart_flat_of_smooth_seed t hs j.succ
  rw [relativeNormal_cubic]
  exact neg_ne_zero.mpr hj

#print axioms coefficientPivot_regular_of_smooth_seed
#print axioms smooth_neighborhood_and_nonzero_normal

end CycleQ2LiteralAbelJacobiSeedLiftConeRegular
end
