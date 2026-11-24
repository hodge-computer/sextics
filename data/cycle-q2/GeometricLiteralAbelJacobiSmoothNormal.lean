import Proposal.GeometricLiteralAbelJacobiSeedLift
import Proposal.GeometricLiteralAbelJacobiCubicNonzero
import Proposal.GeometricLiteralAbelJacobiIndependentRegular
import Proposal.GeometricLiteralAbelJacobiBertiniMinor

/-!
# The nonzero normal of a smooth original moving curve

The scheme-theoretic Jacobian cover and the nonvanishing cubic concern the
same section vector. Restricting the smooth infinitesimal curve to its four
affine charts supplies the chart flatness needed for the normal functional.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSmoothNormal

open CategoryTheory AlgebraicGeometry
open CycleQ2IncidenceImageLine CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2SeedConeSection CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceSeedFiberCover CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2RelativeConstantCurve
  CycleQ2LiteralAbelJacobiSeedLift CycleQ2LiteralAbelJacobiCubicNonzero
  CycleQ2LiteralAbelJacobiCubicNonzeroSeed CycleQ2LiteralAbelJacobiRelativeNormal

attribute [local instance] CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedCommRing
  CycleQ2LiteralAbelJacobiContraction.seedChartCommRing
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra

/-- Smoothness of the genuine first-order curve makes every one of the
original coordinate charts flat over the very same dual numbers. -/
theorem flat_charts_of_smooth (t : Fin 3 → ℂ) (hs : Smooth (firstOrderCurveToBase t))
    (i : Fin 4) : Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i) := by
  have hc : Flat (firstOrderChartToCurve t i ≫ firstOrderCurveToBase t) := inferInstance
  rw [firstOrderChartToCurve_overBase] at hc
  exact RingHom.flat_algebraMap_iff.mp ((HasRingHomProperty.Spec_iff (P := @Flat)).mp hc)

open CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveCoordinateChart
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiFamily

/-- The residue chart on which the moving normal is evaluated is an actual
smooth complex algebra whenever the original seed minors cover the curve. -/
theorem seedChart_smooth_of_minors (t : Fin 3 → ℂ) (h : SeedMinorCover t) (i : Fin 4) :
    Algebra.Smooth ℂ (A t i) := by
  have hf := (smooth_neighborhood_of_seed_minors t h).1
  have hs := ((firstOrderCurve_smooth_iff_flat_and_smooth_seed t).mp hf).2
  have hc : Smooth ((specializedCoordinateAffineChart seed t i).inv ≫
      (specializedCoordinatePatch seed t i).ι ≫ specializedCurveToBase seed t) := by
    infer_instance
  rw [specializedCoordinateAffineChart_overBase] at hc
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hc)

theorem smooth_normal_of_seed_minors (t : Fin 3 → ℂ) (h : SeedMinorCover t)
    (hr : ∀ m : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed m)
      (algebraMap (PointSurface seed) (CoefficientPivot seed m) (constantEquation seed t m.1))) :
    ∃ hf : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
      Smooth (firstOrderCurveToBase t) ∧ Flat (firstOrderCurveToBase t) ∧
      IsProper (firstOrderCurveToBase t) ∧
      (∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
        Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
        IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
        Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V)) ∧
      ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
        ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 := by
  obtain ⟨hs, hV⟩ := smooth_neighborhood_of_seed_minors t h
  have hf := flat_charts_of_smooth t hs
  obtain ⟨j, hj⟩ := exists_chart_nonzero t hr firstOrderWeightedCubic.val 3
    firstOrderWeightedCubic.property (by decide) seed_cubic_ne_zero
  refine ⟨hf, hs, inferInstance, firstOrderCurveToBase_proper t, hV, j, ?_⟩
  have := hf j.succ
  rw [relativeNormal_cubic]
  exact neg_ne_zero.mpr hj

open CycleQ2LiteralAbelJacobiContraction

/-- One smooth proper section family, with nonempty fibers, has a nonzero
first-order normal on the fixed sextic. On an original affine chart an
ambient derivation realizes the same normal and is nonzero on the cubic. -/
theorem exists_smooth_moving_curve_nonzero_normal :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ t ≠ 0 ∧
      ∃ hf : ∀ i : Fin 4, Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i),
        Smooth (firstOrderCurveToBase t) ∧ Flat (firstOrderCurveToBase t) ∧
        IsProper (firstOrderCurveToBase t) ∧ Nonempty (specializedCurve seed t) ∧
        (∀ i, Algebra.Smooth ℂ (A t i)) ∧
        (∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
          Smooth ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
          IsProper ((relativeCurveToBase incidencePoint t) ∣_ V) ∧
          Function.Surjective ((relativeCurveToBase incidencePoint t) ∣_ V)) ∧
        ∃ j : Fin 3, @relativeNormal t j.succ (hf j.succ)
          ((idealOnT t j.succ).toCotangent (cubicClass t j.succ)) ≠ 0 ∧
          ∃ v : Derivation ℂ (T j.succ) (A t j.succ),
            (∀ x : idealOnT t j.succ, v x.val =
              @relativeNormal t j.succ (hf j.succ) ((idealOnT t j.succ).toCotangent x)) ∧
            v (cubicOnT j.succ) ≠ 0 := by
  obtain ⟨t, ht, hne, hr⟩ := CycleQ2LiteralAbelJacobiIndependentRegular.exists_independent_regular
  have h : SeedMinorCover t := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  obtain ⟨hf, hs, hflat, hproper, hV, j, hj⟩ := smooth_normal_of_seed_minors t h hr
  have hcharts := seedChart_smooth_of_minors t h
  have := hf j.succ
  have := hcharts j.succ
  obtain ⟨v, hv, _⟩ := exists_moving_representative t j.succ
  exact ⟨t, ht, hne, hf, hs, hflat, hproper,
    CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t, hcharts, hV, j, hj, v, hv,
    fun hz => hj ((hv (cubicClass t j.succ)).symm.trans hz)⟩

end CycleQ2LiteralAbelJacobiSmoothNormal

end

#print axioms CycleQ2LiteralAbelJacobiSmoothNormal.exists_smooth_moving_curve_nonzero_normal
