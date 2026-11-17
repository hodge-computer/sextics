import Proposal.GeometricFirstOrderCurveCharts
import Proposal.GeometricFirstOrderCurvePivotCover
import Proposal.GeometricLiteralAbelJacobiFamily
import Proposal.GeometricIncidenceChartMinorCover
import Proposal.GeometricIncidenceSeedChartMinorCover
import Proposal.GeometricSpecializedCurveCoordinateChart
import Proposal.GeometricSpecializedSectionIdeal
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Regularity of a principal smooth curve in a smooth surface

Over a field every smooth affine chart is reduced. If a principal equation
annihilates a nonzero element, the principal open of that element is a
nonempty open on which the ambient scheme and its closed subscheme agree.
The two relative dimensions must then agree by the rank of differentials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLiftRegular

open scoped TensorProduct

private theorem reduced_of_etale_domain {P A : Type} [CommRing P] [IsDomain P] [CommRing A]
    [Algebra P A] [Algebra.Etale P A] : IsReduced A := by
  let K := FractionRing P
  let : IsReduced (K ⊗[P] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[P] K ⊗[P] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective P K))

private theorem reduced_of_standardSmooth {k A : Type} [Field k] [CommRing A]
    (n : ℕ) (f : k →+* A) (hf : f.IsStandardSmoothOfRelativeDimension n) : IsReduced A := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) A := hg.toAlgebra
  exact reduced_of_etale_domain (P := MvPolynomial (Fin n) k)

theorem reduced_of_smoothDimension {k A : Type} [Field k] [CommRing A]
    (n : ℕ) (f : k →+* A)
    (hf : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f) : IsReduced A := by
  obtain ⟨s, hs, h⟩ := hf
  let (a : s) : IsReduced (Localization.Away a.val) :=
    reduced_of_standardSmooth n _ (h _ a.property)
  exact isReduced_of_injective _ (Localization.algebraMap_injective_of_span_eq_top s hs)

private theorem subsingleton_of_cover {A : Type} [CommRing A] (s : Set A)
    (hs : Ideal.span s = ⊤) (h : ∀ a : s, Subsingleton (Localization.Away a.val)) :
    Subsingleton A := by
  refine ⟨fun x y => Localization.algebraMap_injective_of_span_eq_top s hs ?_⟩
  exact funext fun a => (h a).elim _ _

private theorem away_locally {k A T : Type} [CommRing k] [CommRing A] [CommRing T] [Algebra A T]
    (n : ℕ) (f : k →+* A) (r : A) [IsLocalization.Away r T]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) ((algebraMap A T).comp f) :=
  RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    T r f h

/-- Two distinct relative dimensions on all points of an affine scheme force it to be empty. -/
theorem subsingleton_of_distinct_smoothDimensions {k A : Type} [CommRing k] [CommRing A]
    {n m : ℕ} (hnm : n ≠ m) (f : k →+* A)
    (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f)
    (hm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) f) : Subsingleton A := by
  obtain ⟨s, hs, Hs⟩ := hn
  apply subsingleton_of_cover s hs
  intro a
  obtain ⟨t, ht, Ht⟩ := away_locally (T := Localization.Away a.val) m f a.val hm
  apply subsingleton_of_cover t ht
  intro b
  cases subsingleton_or_nontrivial (Localization.Away b.val) with
  | inl h => exact h
  | inr h =>
    let g := (algebraMap _ (Localization.Away b.val)).comp
      ((algebraMap _ (Localization.Away a.val)).comp f)
    have hg : g.IsStandardSmoothOfRelativeDimension n :=
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
        _ b.val _ (Hs a.val a.property)
    let := g.toAlgebra
    let := hg.toAlgebra
    let := (Ht b.val b.property).toAlgebra
    have eq := (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := k) (S := Localization.Away b.val) n).symm.trans
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
        (R := k) (S := Localization.Away b.val) m)
    exact (hnm (by exact_mod_cast eq)).elim

/-- A principal quotient of smaller constant smooth relative dimension cuts a regular
section on every component of the ambient smooth affine scheme. -/
theorem principal_regular_of_smooth_dimensions {k A : Type} [Field k] [CommRing A]
    (f : k →+* A) (a : A) {n m : ℕ} (hnm : n ≠ m)
    (hA : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f)
    (hQ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)
      ((Ideal.Quotient.mk (Ideal.span {a})).comp f)) :
    a ∈ nonZeroDivisors A := by
  let := reduced_of_smoothDimension n f hA
  apply mem_nonZeroDivisors_iff_right.mpr
  intro r hr
  let T := Localization.Away r
  let I := Ideal.span ({a} : Set A)
  let π := Ideal.Quotient.mk I
  let loc := algebraMap A T
  have ha : loc a = 0 := by
    apply (IsLocalization.Away.algebraMap_isUnit (S := T) r).mul_right_inj.mp
    simp [loc, ← map_mul, hr]
  have hI : I ≤ RingHom.ker loc := (Ideal.span_singleton_le_iff_mem _).mpr ha
  let θ : A ⧸ I →+* T := Ideal.Quotient.lift I loc (fun _ hx => hI hx)
  let := θ.toAlgebra
  have hθ (x : A) : algebraMap (A ⧸ I) T (π x) = loc x := rfl
  have : IsLocalization.Away (π r) T := by
    refine IsLocalization.Away.mk _ ?_ ?_ ?_
    · rw [hθ]; exact IsLocalization.Away.algebraMap_isUnit r
    · intro z
      obtain ⟨j, x, hx⟩ := IsLocalization.Away.surj r z
      exact ⟨j, π x, hx⟩
    · intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      intro he
      obtain ⟨j, hj⟩ := IsLocalization.Away.exists_of_eq (S := T) r he
      exact ⟨j, by simpa only [map_mul, map_pow] using congrArg π hj⟩
  have hdimA := away_locally (T := T) n f r hA
  have hdimQ := away_locally (T := T) m (π.comp f) (π r) hQ
  have hT : Subsingleton T := subsingleton_of_distinct_smoothDimensions hnm _ hdimA hdimQ
  obtain ⟨j, hj⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers r) (S := T)).mp hT
  exact (show IsNilpotent r from ⟨j, hj⟩).eq_zero

open AlgebraicGeometry in
/-- A principal smooth curve on a smooth affine surface over a field is a regular section. -/
theorem regular_of_smooth_curve_on_surface {k A : Type} [Field k] [CommRing A]
    (f : k →+* A) (a : A)
    (hs : SmoothOfRelativeDimension 2 (Spec.map (CommRingCat.ofHom f)))
    (hc : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {a})).comp f)))) :
    IsSMulRegular A a := by
  have h := principal_regular_of_smooth_dimensions f a (n := 2) (m := 1) (by decide)
    ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mp hs)
    ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hc)
  intro x y hxy
  apply sub_eq_zero.mp
  apply mem_nonZeroDivisors_iff_left.mp h
  change a * x = a * y at hxy
  simpa only [mul_sub, sub_eq_zero] using hxy

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartDimension
  CycleQ2IncidenceChartMinorCover CycleQ2IncidenceSeedChartMinorCover
  CycleQ2GeometricIncidenceProj CycleQ2RelativeCurveChart
  CycleQ2RelativeConstantSection CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveCoordinateChart CycleQ2SpecializedSectionIdeal
  CycleQ2FirstOrderLocalizedReduction CycleQ2FirstOrderCurveChartFlat
  CycleQ2FirstOrderCurvePivotCover CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts

attribute [local instance] CycleQ2RelativeCurveChart.dehomogenizedCommRing
  CycleQ2RelativeCurveChart.pointSurfaceCommRing
  CycleQ2FirstOrderCurveChartFlat.seedRefinementCommRing
  CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing
  CycleQ2RelativeCurveChartFiber.incidenceCurveChartCommRing
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2FirstOrderTensorReduction.firstOrderTensorCommRing
  CycleQ2FirstOrderChartFlatness.firstOrderTensorModule
  CycleQ2FirstOrderChartFlatness.firstOrderTensorSMul

private abbrev seed := seedPoint (57 : ℂ) Complex.I

private theorem seedChartDimension (i : Fin 4) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (algebraMap ℂ (DehomogenizedRing seed i)) := by
  let j := fun q : Fin 2 ↪ Option (Fin 3) => (prePresentation seed i q q.injective).jacobian
  refine ⟨Set.range j, ?_, ?_⟩
  · by_contra hne
    obtain ⟨P, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    have : P.IsPrime := hp.isPrime
    obtain ⟨a, b, _, hab⟩ := seed_prime_normalizedMinor_cover i P
    obtain ⟨q, hq, hminor⟩ := exists_chartMinor_not_mem seed i P a b hab
    apply hminor
    rw [← prePresentation_jacobian seed i q hq]
    exact hle (Ideal.subset_span ⟨⟨q, hq⟩, rfl⟩)
  · rintro _ ⟨q, rfl⟩
    change RingHom.IsStandardSmoothOfRelativeDimension 2
      ((algebraMap _ (JacobianPatch seed i q q.injective)).comp (algebraMap ℂ _))
    rw [← IsScalarTower.algebraMap_eq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr
      (patch_standardSmooth seed i q q.injective)

private theorem seedLocalizedIdeal (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    (affineSectionIdeal seed t i).map (algebraMap _ (SeedRefinement i p)) =
      Ideal.span {seedRefinedEquation t i p} := by
  let f := (algebraMap _ (SeedRefinement i p)).comp (surfaceToDehomogenized seed i)
  rw [affineSectionIdeal, Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range (fun j => f (relativeEquation seed t j))) =
    Ideal.span {f (relativeEquation seed t p.1)}
  exact image_rows_principal seed t seed_original_equations seed_leading_unit f p
    (IsLocalization.Away.algebraMap_isUnit (seedPivot i p))

/-- Smoothness in relative dimension one of the original projective seed curve makes its
selected row regular on each of the original thirty-six affine matrix-pivot charts. -/
theorem seedRefinedEquation_regular (t : Fin 3 → ℂ)
    (hc : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t))
    (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p) := by
  let R := DehomogenizedRing seed i
  let B := SeedRefinement i p
  let I := affineSectionIdeal seed t i
  let π := Ideal.Quotient.mk I
  have hs := away_locally (T := B) 2 (algebraMap ℂ R) (seedPivot i p) (seedChartDimension i)
  have H : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCurveChart seed t i)))) := by
    rw [← specializedCoordinateAffineChart_overBase]
    apply IsZariskiLocalAtSource.comp _ (specializedCoordinateAffineChart seed t i).inv
    exact IsZariskiLocalAtSource.comp hc (specializedCoordinatePatch seed t i).ι
  have hC := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp H
  have hQ := away_locally (T := LocalizedQuotient I (seedPivot i p)) 1
    (algebraMap ℂ (AffineCurveChart seed t i)) (π (seedPivot i p)) hC
  apply regular_of_smooth_curve_on_surface (algebraMap ℂ B)
  · apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mpr
    rwa [← IsScalarTower.algebraMap_eq] at hs
  · apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
    rw [← seedLocalizedIdeal]
    exact hQ

/-- The same smooth projective seed section has flat first-order affine curve charts. -/
theorem firstOrderCurveChart_flat_of_smooth_seed (t : Fin 3 → ℂ)
    (hc : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) (i : Fin 4) :
    Module.Flat (DualNumber ℂ) (FirstOrderCurveChart t i) := by
  apply curveChart_flat_of_refined
  intro p
  exact refinedCurveChart_flat t i p (seedRefinedEquation_regular t hc i p)

/-- The original first-order projective family is smooth for every section whose original
seed fibre is smooth of relative dimension one. -/
theorem firstOrderCurve_smooth_of_smooth_seed (t : Fin 3 → ℂ)
    (hc : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) :
    Smooth (firstOrderCurveToBase t) :=
  (CycleQ2LiteralAbelJacobiFamily.firstOrderCurve_smooth_iff_flat_and_smooth_seed t).mpr
    ⟨firstOrderCurveToBase_flat_of_affineCharts t (firstOrderCurveChart_flat_of_smooth_seed t hc),
      SmoothOfRelativeDimension.smooth 1 _⟩

#print axioms firstOrderCurve_smooth_of_smooth_seed
#print axioms seedRefinedEquation_regular
#print axioms firstOrderCurveChart_flat_of_smooth_seed
#print axioms regular_of_smooth_curve_on_surface

end CycleQ2LiteralAbelJacobiSeedLiftRegular
end
