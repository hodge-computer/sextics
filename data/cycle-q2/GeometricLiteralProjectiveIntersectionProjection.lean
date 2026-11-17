import Proposal.GeometricLiteralProjectiveIntersectionKernel

/-!
# The genuine degree-zero projection on finite chart intersections

The original reduction commutes with the actual degree-zero projections
on every finite product denominator. Its ordinary kernel is the original
square-zero epsilon ideal. Projection is multiplicative on lifts of
native functions, using that same actual kernel and reduced action.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveIntersectionProjection

open HomogeneousLocalization CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2GradedLocalizationProjection

def ordinaryReduction (s : Finset Vertex) : ThickCone s →+* ClosedCone s :=
  IsLocalization.map (M := Submonoid.powers (thickProduct s))
    (T := Submonoid.powers (closedProduct s))
    (ClosedCone s) reduction.toRingHom (by
    rintro y ⟨n,rfl⟩
    change reduction (thickProduct s ^ n) ∈ Submonoid.powers (closedProduct s)
    rw [map_pow]
    change reductionGraded (thickProduct s) ^ n ∈ _
    rw [reduction_thickProduct]
    exact ⟨n,rfl⟩)

theorem ordinaryReduction_fraction (s : Finset Vertex) (n : ℕ) (p : GradedDeformation) :
    ordinaryReduction s (fraction (thickProduct s) n p) =
      fraction (closedProduct s) n (reduction p) := by
  unfold ordinaryReduction fraction
  rw [IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  change reduction (thickProduct s ^ n) = closedProduct s ^ n
  rw [map_pow]
  exact congrArg (fun x => x ^ n) (reduction_thickProduct s)

theorem ordinaryReduction_val (s : Finset Vertex) (x : ThickRing s) :
    ordinaryReduction s x.val = (nativeReduction s x).val := by
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective deformationGrade (thickProduct_homogeneous s) x
  rw [nativeReduction_mk, Away.val_mk, Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk']
  exact ordinaryReduction_fraction s n p

theorem reduction_projected_numerator (n : ℕ) (p : GradedDeformation) :
    reduction (GradedRing.proj deformationGrade n p) =
      GradedRing.proj (surfaceGrade 57 1) n (reduction p) :=
  reductionGraded.map_directSumDecompose

def thickProjection (s : Finset Vertex) : ThickCone s →+ ThickRing s :=
  degreeZeroAddHom deformationGrade (thickProduct_homogeneous s)

def closedProjection (s : Finset Vertex) : ClosedCone s →+ ClosedRing s :=
  degreeZeroAddHom (surfaceGrade 57 1) (closedProduct_homogeneous s)

theorem thickProjection_val (s : Finset Vertex) (x : ThickRing s) :
    thickProjection s x.val = x :=
  degreeZero_val deformationGrade (thickProduct_homogeneous s) x

theorem closedProjection_val (s : Finset Vertex) (x : ClosedRing s) :
    closedProjection s x.val = x :=
  degreeZero_val (surfaceGrade 57 1) (closedProduct_homogeneous s) x

/-- The cross-ring projection square uses the original graded reduction,
including all possible localization torsion. -/
theorem projection_reduction (s : Finset Vertex) (z : ThickCone s) :
    nativeReduction s (thickProjection s z) =
      closedProjection s (ordinaryReduction s z) := by
  obtain ⟨n,p,rfl⟩ := exists_fraction (thickProduct s) z
  change nativeReduction s (degreeZero deformationGrade (thickProduct_homogeneous s)
      (fraction (thickProduct s) n p)) = _
  rw [degreeZero_fraction, ordinaryReduction_fraction]
  change nativeReduction s (projectedFraction deformationGrade (thickProduct_homogeneous s) n p) =
    degreeZero (surfaceGrade 57 1) (closedProduct_homogeneous s)
      (fraction (closedProduct s) n (reduction p))
  rw [degreeZero_fraction]
  unfold projectedFraction
  rw [nativeReduction_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, Localization.mk_eq_mk']
  congr 1
  exact reduction_projected_numerator _ p

theorem ordinaryReduction_fraction_eq_zero_iff (s : Finset Vertex) (n : ℕ)
    (p : GradedDeformation) :
    ordinaryReduction s (fraction (thickProduct s) n p) = 0 ↔
      ∃ k : ℕ, reduction (thickProduct s ^ k * p) = 0 := by
  rw [ordinaryReduction_fraction, fraction, IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨b,hb⟩,hz⟩
    obtain ⟨k,rfl⟩ := hb
    refine ⟨k, ?_⟩
    rw [map_mul, map_pow]
    change reductionGraded (thickProduct s) ^ k * reduction p = 0
    rw [reduction_thickProduct]
    exact hz
  · rintro ⟨k,hk⟩
    refine ⟨⟨closedProduct s ^ k,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩, ?_⟩
    rw [map_mul, map_pow] at hk
    change reductionGraded (thickProduct s) ^ k * reduction p = 0 at hk
    rwa [reduction_thickProduct] at hk

theorem ordinaryKernel_principal (s : Finset Vertex) :
    RingHom.ker (ordinaryReduction s) =
      Ideal.span ({algebraMap GradedDeformation (ThickCone s) epsilonElement} :
        Set (ThickCone s)) := by
  have he : RingHom.ker (ordinaryReduction s) = (RingHom.ker reduction.toRingHom).map
      (algebraMap GradedDeformation (ThickCone s)) := by
    ext z
    obtain ⟨n,p,rfl⟩ := exists_fraction (thickProduct s) z
    change ordinaryReduction s (fraction (thickProduct s) n p) = 0 ↔ _
    rw [ordinaryReduction_fraction_eq_zero_iff, fraction, IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨thickProduct s ^ k, ⟨k,rfl⟩, hk⟩
    · rintro ⟨t,⟨k,rfl⟩,hk⟩
      exact ⟨k,hk⟩
  rw [he, reduction_kernel_principal, Ideal.map_span, Set.image_singleton]

theorem ordinaryKernel_mul_zero (s : Finset Vertex) (x y : ThickCone s)
    (hx : ordinaryReduction s x = 0) (hy : ordinaryReduction s y = 0) : x * y = 0 := by
  have hx' : x ∈ Ideal.span ({algebraMap GradedDeformation (ThickCone s) epsilonElement} :
      Set (ThickCone s)) := by rw [← ordinaryKernel_principal]; exact hx
  have hy' : y ∈ Ideal.span ({algebraMap GradedDeformation (ThickCone s) epsilonElement} :
      Set (ThickCone s)) := by rw [← ordinaryKernel_principal]; exact hy
  obtain ⟨u,rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨v,rfl⟩ := Ideal.mem_span_singleton'.mp hy'
  calc
    _ = (u * v) * algebraMap GradedDeformation (ThickCone s)
        (epsilonElement * epsilonElement) := by rw [map_mul]; ring
    _ = 0 := by rw [epsilonElement_square, map_zero, mul_zero]

/-- Projection becomes multiplicative on the subring whose original
reductions are degree-zero fractions. This is the condition satisfied
by a genuine splitting evaluated on the native projective chart. -/
theorem thickProjection_mul (s : Finset Vertex) (x y : ThickCone s)
    (hx : ordinaryReduction s x = (nativeReduction s (thickProjection s x)).val)
    (hy : ordinaryReduction s y = (nativeReduction s (thickProjection s y)).val) :
    thickProjection s (x * y) = thickProjection s x * thickProjection s y := by
  have hdx : ordinaryReduction s (x - (thickProjection s x).val) = 0 := by
    rw [map_sub, ordinaryReduction_val, hx, sub_self]
  have hdy : ordinaryReduction s (y - (thickProjection s y).val) = 0 := by
    rw [map_sub, ordinaryReduction_val, hy, sub_self]
  have hzero := ordinaryKernel_mul_zero s (x - (thickProjection s x).val)
    (y - (thickProjection s y).val) hdx hdy
  have hprod : x * y = (thickProjection s x).val * y +
      x * (thickProjection s y).val - (thickProjection s x).val * (thickProjection s y).val := by
    linear_combination hzero
  rw [hprod, map_sub, map_add]
  change degreeZero deformationGrade (thickProduct_homogeneous s)
        ((thickProjection s x).val * y) +
      degreeZero deformationGrade (thickProduct_homogeneous s)
        (x * (thickProjection s y).val) -
      degreeZero deformationGrade (thickProduct_homogeneous s)
        ((thickProjection s x).val * (thickProjection s y).val) = _
  rw [degreeZero_mul_homogeneous, degreeZero_homogeneous_mul,
    degreeZero_mul_homogeneous, degreeZero_val]
  change thickProjection s x * thickProjection s y +
    thickProjection s x * thickProjection s y -
    thickProjection s x * thickProjection s y = _
  abel

end CycleQ2LiteralProjectiveIntersectionProjection

end

#print axioms CycleQ2LiteralProjectiveIntersectionProjection.projection_reduction
#print axioms CycleQ2LiteralProjectiveIntersectionProjection.ordinaryKernel_mul_zero
#print axioms CycleQ2LiteralProjectiveIntersectionProjection.thickProjection_mul
