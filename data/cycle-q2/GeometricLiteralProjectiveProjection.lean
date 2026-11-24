import Proposal.GeometricLiteralProjectiveKernel

/-!
# Reduction commutes with the actual degree-zero chart projection

The map on ordinary localizations and the map on native projective
chart rings are induced by the same original graded reduction. Their
square with the actual degree-zero projections commutes. The ordinary
localization kernel is also the original principal square-zero ideal.
Consequently projection is multiplicative on elements whose reductions
are genuine native chart fractions.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveProjection

open HomogeneousLocalization CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveKernel CycleQ2GradedLocalizationProjection

abbrev OrdinaryThick (a : Fin 4) (l : Fin 3) := Localization.Away (chartDenominator a l)
abbrev OrdinaryClosed (a : Fin 4) (l : Fin 3) := Localization.Away (refinedDenominator 57 1 a l)

def ordinaryReduction (a : Fin 4) (l : Fin 3) : OrdinaryThick a l →+* OrdinaryClosed a l :=
  IsLocalization.map (M := Submonoid.powers (chartDenominator a l))
    (T := Submonoid.powers (refinedDenominator 57 1 a l))
    (OrdinaryClosed a l) reduction.toRingHom (by
    rintro y ⟨n,rfl⟩
    change reduction (chartDenominator a l ^ n) ∈ Submonoid.powers (refinedDenominator 57 1 a l)
    rw [map_pow]
    change reductionGraded (chartDenominator a l) ^ n ∈ _
    rw [reduction_chartDenominator]
    exact ⟨n,rfl⟩)

theorem ordinaryReduction_fraction (a : Fin 4) (l : Fin 3) (n : ℕ) (p : GradedDeformation) :
    ordinaryReduction a l (fraction (chartDenominator a l) n p) =
      fraction (refinedDenominator 57 1 a l) n (reduction p) := by
  unfold ordinaryReduction fraction
  rw [IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  change reduction (chartDenominator a l ^ n) = refinedDenominator 57 1 a l ^ n
  rw [map_pow]
  exact congrArg (fun x => x ^ n) (reduction_chartDenominator a l)

theorem ordinaryReduction_val (a : Fin 4) (l : Fin 3) (x : ChartRing a l) :
    ordinaryReduction a l x.val = (chartReduction a l x).val := by
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective deformationGrade (chartDenominator_homogeneous a l) x
  rw [chartReduction_mk, Away.val_mk, Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk']
  exact ordinaryReduction_fraction a l n p

theorem reduction_projected_numerator (n : ℕ) (p : GradedDeformation) :
    reduction (GradedRing.proj deformationGrade n p) =
      GradedRing.proj (surfaceGrade 57 1) n (reduction p) :=
  reductionGraded.map_directSumDecompose

def thickProjection (a : Fin 4) (l : Fin 3) : OrdinaryThick a l →+ ChartRing a l :=
  degreeZeroAddHom deformationGrade (chartDenominator_homogeneous a l)

def closedProjection (a : Fin 4) (l : Fin 3) : OrdinaryClosed a l →+ RefinedRing 57 1 a l :=
  degreeZeroAddHom (surfaceGrade 57 1) (refinedDenominator_homogeneous 57 1 a l)

theorem thickProjection_val (a : Fin 4) (l : Fin 3) (x : ChartRing a l) :
    thickProjection a l x.val = x :=
  degreeZero_val deformationGrade (chartDenominator_homogeneous a l) x

theorem closedProjection_val (a : Fin 4) (l : Fin 3) (x : RefinedRing 57 1 a l) :
    closedProjection a l x.val = x :=
  degreeZero_val (surfaceGrade 57 1) (refinedDenominator_homogeneous 57 1 a l) x

/-- The cross-ring projection square uses the original graded reduction,
including all possible localization torsion. -/
theorem projection_reduction (a : Fin 4) (l : Fin 3) (z : OrdinaryThick a l) :
    chartReduction a l (thickProjection a l z) =
      closedProjection a l (ordinaryReduction a l z) := by
  obtain ⟨n,p,rfl⟩ := exists_fraction (chartDenominator a l) z
  change chartReduction a l (degreeZero deformationGrade (chartDenominator_homogeneous a l)
      (fraction (chartDenominator a l) n p)) = _
  rw [degreeZero_fraction, ordinaryReduction_fraction]
  change chartReduction a l (projectedFraction deformationGrade (chartDenominator_homogeneous a l) n p) =
    degreeZero (surfaceGrade 57 1) (refinedDenominator_homogeneous 57 1 a l)
      (fraction (refinedDenominator 57 1 a l) n (reduction p))
  rw [degreeZero_fraction]
  unfold projectedFraction
  rw [chartReduction_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, Localization.mk_eq_mk']
  congr 1
  exact reduction_projected_numerator _ p

theorem ordinaryReduction_fraction_eq_zero_iff (a : Fin 4) (l : Fin 3) (n : ℕ)
    (p : GradedDeformation) :
    ordinaryReduction a l (fraction (chartDenominator a l) n p) = 0 ↔
      ∃ k : ℕ, reduction (chartDenominator a l ^ k * p) = 0 := by
  rw [ordinaryReduction_fraction, fraction, IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨b,hb⟩,hz⟩
    obtain ⟨k,rfl⟩ := hb
    refine ⟨k, ?_⟩
    rw [map_mul, map_pow]
    change reductionGraded (chartDenominator a l) ^ k * reduction p = 0
    rw [reduction_chartDenominator]
    exact hz
  · rintro ⟨k,hk⟩
    refine ⟨⟨refinedDenominator 57 1 a l ^ k,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩, ?_⟩
    rw [map_mul, map_pow] at hk
    change reductionGraded (chartDenominator a l) ^ k * reduction p = 0 at hk
    rwa [reduction_chartDenominator] at hk

theorem ordinaryKernel_principal (a : Fin 4) (l : Fin 3) :
    RingHom.ker (ordinaryReduction a l) =
      Ideal.span ({algebraMap GradedDeformation (OrdinaryThick a l) epsilonElement} :
        Set (OrdinaryThick a l)) := by
  have he : RingHom.ker (ordinaryReduction a l) = (RingHom.ker reduction.toRingHom).map
      (algebraMap GradedDeformation (OrdinaryThick a l)) := by
    ext z
    obtain ⟨n,p,rfl⟩ := exists_fraction (chartDenominator a l) z
    change ordinaryReduction a l (fraction (chartDenominator a l) n p) = 0 ↔ _
    rw [ordinaryReduction_fraction_eq_zero_iff, fraction, IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨chartDenominator a l ^ k, ⟨k,rfl⟩, hk⟩
    · rintro ⟨t,⟨k,rfl⟩,hk⟩
      exact ⟨k,hk⟩
  rw [he, reduction_kernel_principal, Ideal.map_span, Set.image_singleton]

theorem ordinaryKernel_mul_zero (a : Fin 4) (l : Fin 3) (x y : OrdinaryThick a l)
    (hx : ordinaryReduction a l x = 0) (hy : ordinaryReduction a l y = 0) : x * y = 0 := by
  have hx' : x ∈ Ideal.span ({algebraMap GradedDeformation (OrdinaryThick a l) epsilonElement} :
      Set (OrdinaryThick a l)) := by rw [← ordinaryKernel_principal]; exact hx
  have hy' : y ∈ Ideal.span ({algebraMap GradedDeformation (OrdinaryThick a l) epsilonElement} :
      Set (OrdinaryThick a l)) := by rw [← ordinaryKernel_principal]; exact hy
  obtain ⟨u,rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨v,rfl⟩ := Ideal.mem_span_singleton'.mp hy'
  calc
    _ = (u * v) * algebraMap GradedDeformation (OrdinaryThick a l)
        (epsilonElement * epsilonElement) := by rw [map_mul]; ring
    _ = 0 := by rw [epsilonElement_square, map_zero, mul_zero]

/-- Projection becomes multiplicative on the subring whose original
reductions are degree-zero fractions. This is the condition satisfied
by a genuine splitting evaluated on the native projective chart. -/
theorem thickProjection_mul (a : Fin 4) (l : Fin 3) (x y : OrdinaryThick a l)
    (hx : ordinaryReduction a l x = (chartReduction a l (thickProjection a l x)).val)
    (hy : ordinaryReduction a l y = (chartReduction a l (thickProjection a l y)).val) :
    thickProjection a l (x * y) = thickProjection a l x * thickProjection a l y := by
  have hdx : ordinaryReduction a l (x - (thickProjection a l x).val) = 0 := by
    rw [map_sub, ordinaryReduction_val, hx, sub_self]
  have hdy : ordinaryReduction a l (y - (thickProjection a l y).val) = 0 := by
    rw [map_sub, ordinaryReduction_val, hy, sub_self]
  have hzero := ordinaryKernel_mul_zero a l (x - (thickProjection a l x).val)
    (y - (thickProjection a l y).val) hdx hdy
  have hprod : x * y = (thickProjection a l x).val * y +
      x * (thickProjection a l y).val - (thickProjection a l x).val * (thickProjection a l y).val := by
    linear_combination hzero
  rw [hprod, map_sub, map_add]
  change degreeZero deformationGrade (chartDenominator_homogeneous a l)
        ((thickProjection a l x).val * y) +
      degreeZero deformationGrade (chartDenominator_homogeneous a l)
        (x * (thickProjection a l y).val) -
      degreeZero deformationGrade (chartDenominator_homogeneous a l)
        ((thickProjection a l x).val * (thickProjection a l y).val) = _
  rw [degreeZero_mul_homogeneous, degreeZero_homogeneous_mul,
    degreeZero_mul_homogeneous, degreeZero_val]
  change thickProjection a l x * thickProjection a l y +
    thickProjection a l x * thickProjection a l y -
    thickProjection a l x * thickProjection a l y = _
  abel

end CycleQ2LiteralProjectiveProjection

end

#print axioms CycleQ2LiteralProjectiveProjection.projection_reduction
#print axioms CycleQ2LiteralProjectiveProjection.ordinaryKernel_mul_zero
#print axioms CycleQ2LiteralProjectiveProjection.thickProjection_mul
