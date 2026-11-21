import Proposal.GeometricSeedProjectiveImageChart
import Mathlib.Tactic.Group

/-!
# The degree-four transition of the actual seed image line

On the original coordinate cone overlap, the actual projective matrix is
`M/Xi^14`, and its left generators are `L/Xi^10`. The unique image-to-dual
map recovering vector entries on these left generators therefore changes
by `(Xi/Xj)^4` when the image vector changes by `(Xi/Xj)^14`.

All overlap rings, coefficient maps, matrices, ideals and units below
come from the original seed and the actual projective charts. The final
isomorphisms are module comparisons on those overlaps. Global descent to
an internal-Hom sheaf, the Chern-class identity, and a relative cycle-class
or Abel--Jacobi map are separate remaining constructions.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveImageTwist

open Matrix MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading CycleQ2SegreTangentLocal
  CycleQ2SeedProjectiveImageChart CycleQ2SegreFactorSequence
  CycleQ2SegreLinkageDuality CycleQ2SegreLinkageImage

namespace Regrading

variable {R : Type*} [CommRing R] (F : FactorData R)

abbrev Image := LinearMap.range F.matrix.mulVecLin

def imageDual : Image F ≃ₗ[R] (F.leftIdeal →ₗ[R] R) :=
  (rightEquivImage F).symm.trans (rightEquivLeftDual F)

theorem imageDual_selected (z : Image F) (a : Fin 3) :
    imageDual F z (leftElement F a) = z.val a := by
  obtain ⟨y, rfl⟩ := (rightEquivImage F).surjective z
  change pairing F ((rightEquivImage F).symm (rightEquivImage F y)) (leftElement F a) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (rightEquivImage_apply F y a).symm

theorem leftIdeal_eq_span : F.leftIdeal = Ideal.span (Set.range F.left) := by
  apply le_antisymm
  · intro x hx
    change (⟨x, hx⟩ : F.leftIdeal).val ∈ Ideal.span (Set.range F.left)
    rw [left_reconstruction F ⟨x, hx⟩]
    apply Ideal.sum_mem
    intro q _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q.1, rfl⟩)
  · exact Ideal.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact F.left_mem a)

theorem dual_ext (φ ψ : F.leftIdeal →ₗ[R] R)
    (h : ∀ a, φ (leftElement F a) = ψ (leftElement F a)) : φ = ψ := by
  ext x
  have hx : x = ∑ q : Fin 3 × Fin 3,
      (weights F q * pairing F (rightElement F q.2) x) • leftElement F q.1 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, leftElement] using
      left_reconstruction F x
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, map_smul, h]

def normalizedImageDual (u : Rˣ) : Image F ≃ₗ[R] (F.leftIdeal →ₗ[R] R) :=
  (imageDual F).trans (LinearEquiv.smulOfUnit (u ^ 10))

theorem normalizedImageDual_apply (u : Rˣ) (z : Image F) :
    normalizedImageDual F u z = (u : R) ^ 10 • imageDual F z := rfl

/-- A unit rescaling of the matrix preserves its actual image submodule. -/
theorem normalized_matrix_range (u : Rˣ) :
    LinearMap.range (((u⁻¹ : Rˣ) : R) ^ 14 • F.matrix).mulVecLin = Image F := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨((u⁻¹ : Rˣ) : R) ^ 14 • v, ?_⟩
    change F.matrix *ᵥ (((u⁻¹ : Rˣ) : R) ^ 14 • v) =
      (((u⁻¹ : Rˣ) : R) ^ 14 • F.matrix) *ᵥ v
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · rintro _ ⟨v, rfl⟩
    refine ⟨(u : R) ^ 14 • v, ?_⟩
    change (((u⁻¹ : Rˣ) : R) ^ 14 • F.matrix) *ᵥ ((u : R) ^ 14 • v) = F.matrix *ᵥ v
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, ← mul_pow,
      Units.inv_mul, one_pow, one_smul]

theorem normalizedImageDual_selected (u : Rˣ) (z : Image F) (a : Fin 3) :
    normalizedImageDual F u z
      (((u⁻¹ : Rˣ) : R) ^ 10 • leftElement F a) = z.val a := by
  rw [normalizedImageDual_apply, LinearMap.smul_apply, map_smul,
    smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul,
    imageDual_selected]

/-- The difference between the degree-fourteen vector and degree-ten
ideal generators is exactly the positive degree-four twist. -/
theorem normalizedImageDual_transition (u v : Rˣ) (z : Image F) :
    normalizedImageDual F v (((u / v : Rˣ) : R) ^ 14 • z) =
      ((u / v : Rˣ) : R) ^ 4 • normalizedImageDual F u z := by
  rw [normalizedImageDual_apply, normalizedImageDual_apply, map_smul, smul_smul, smul_smul]
  congr 1
  have h : v ^ 10 * (u / v) ^ 14 = (u / v) ^ 4 * u ^ 10 := by
    calc
      _ = (u / v) ^ 14 * v ^ 10 := mul_comm _ _
      _ = ((u / v) ^ 4 * (u / v) ^ 10) * v ^ 10 := by rw [← pow_add]
      _ = (u / v) ^ 4 * ((u / v) * v) ^ 10 := by rw [mul_pow, mul_assoc]
      _ = _ := by rw [div_mul_cancel]
  exact congrArg (fun w : Rˣ => (w : R)) h

end Regrading

open CycleQ2SegreFactorChartExact CycleQ2SegreFactorRestrictions

local instance overlapCommRing (s : Finset (Fin 3)) : CommRing (Chart s) := inferInstance
local instance overlapSelfModule (s : Finset (Fin 3)) : Module (Chart s) (Chart s) :=
  Algebra.toModule
local instance overlapDualModule (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Module (Chart s) ((factorData s hs).leftIdeal →ₗ[Chart s] Chart s) := inferInstance

def overlapPolynomial (s : Finset (Fin 3)) : WeightedPoly →+* Chart s :=
  (chartMap s).comp (CycleQ2SeedLinkagePrincipal.quotientMap (57 : ℂ) Complex.I)

def overlapCoefficient (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) :
    AffineRing i →+* Chart s :=
  (res (Finset.singleton_subset_iff.mpr hi)).comp (affineCoefficient i)

def coordinateUnit (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) : (Chart s)ˣ :=
  (CycleQ2SegreComplexChartExact.seed_coordinate_unit s i hi).unit

theorem coordinateUnit_val (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) :
    (coordinateUnit s i hi : Chart s) = overlapPolynomial s (X i.succ.castSucc) := by
  rw [coordinateUnit, IsUnit.unit_spec]
  change chartMap s (Ideal.Quotient.mk _
    (X (CycleQ2SeedQuotientFiniteFree.remainingIndex i))) = _
  rw [remainingIndex_eq]
  rfl

theorem restrict_conePolynomial (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s)
    (p : WeightedPoly) :
    res (Finset.singleton_subset_iff.mpr hi) (conePolynomial i p) = overlapPolynomial s p :=
  restriction_chartMap _ _

theorem overlapCoefficient_homogeneous (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    overlapCoefficient s i hi (affinePolynomial i p) *
      (coordinateUnit s i hi : Chart s) ^ n = overlapPolynomial s p := by
  have h := congrArg (res (Finset.singleton_subset_iff.mpr hi))
    (affineCoefficient_homogeneous i n p hp)
  have h0 : res (Finset.singleton_subset_iff.mpr hi)
        (affineCoefficient i (affinePolynomial i p)) *
      res (Finset.singleton_subset_iff.mpr hi) (conePolynomial i (X i.succ.castSucc)) ^ n =
      res (Finset.singleton_subset_iff.mpr hi) (conePolynomial i p) := by
    simpa only [map_mul, map_pow] using h
  have hX : res (Finset.singleton_subset_iff.mpr hi)
      (conePolynomial i (X i.succ.castSucc)) = (coordinateUnit s i hi : Chart s) :=
    (restrict_conePolynomial s i hi _).trans (coordinateUnit_val s i hi).symm
  exact (congrArg (fun x : Chart s =>
    overlapCoefficient s i hi (affinePolynomial i p) * x ^ n) hX.symm).trans
      (h0.trans (restrict_conePolynomial s i hi p))

theorem overlapCoefficient_normalized (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    overlapCoefficient s i hi (affinePolynomial i p) =
      ((coordinateUnit s i hi)⁻¹ : (Chart s)ˣ) ^ n • overlapPolynomial s p := by
  let u := coordinateUnit s i hi
  change overlapCoefficient s i hi (affinePolynomial i p) =
    (((u⁻¹ : (Chart s)ˣ) : Chart s) ^ n) * overlapPolynomial s p
  have h := overlapCoefficient_homogeneous s i hi n p hp
  calc
    _ = (overlapCoefficient s i hi (affinePolynomial i p) * (u : Chart s) ^ n) *
        ((u⁻¹ : (Chart s)ˣ) : Chart s) ^ n := by
      rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
    _ = overlapPolynomial s p * ((u⁻¹ : (Chart s)ˣ) : Chart s) ^ n := by rw [h]
    _ = _ := mul_comm (overlapPolynomial s p) (((u⁻¹ : (Chart s)ˣ) : Chart s) ^ n)

def overlapMatrix (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) :
    Matrix (Fin 3) (Fin 3) (Chart s) :=
  (overlapCoefficient s i hi).mapMatrix (chartFactorData i).matrix

/-- The overlap matrix is the actual dehomogenized seed matrix. -/
theorem overlapMatrix_eq (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) :
    overlapMatrix s i hi =
      (((coordinateUnit s i hi)⁻¹ : (Chart s)ˣ) : Chart s) ^ 14 • (factorData s hs).matrix := by
  ext a b
  change overlapCoefficient s i hi ((chartFactorData i).matrix a b) = _
  rw [chartMatrix_polynomial]
  exact overlapCoefficient_normalized s i hi 14 _
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2IncidenceEquations.rawSeedMatrix_homogeneous (57 : ℂ) a b))

theorem overlap_left (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (a : Fin 3) :
    overlapCoefficient s i hi ((chartFactorData i).left a) =
      (((coordinateUnit s i hi)⁻¹ : (Chart s)ˣ) : Chart s) ^ 10 * (factorData s hs).left a := by
  change overlapCoefficient s i hi (coneToChart i
    (conePolynomial i (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a))) = _
  rw [coneToChart_polynomial]
  exact overlapCoefficient_normalized s i hi 10 _
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57 : ℂ) a))

/-- Extending the actual chart orbit ideal to its cone overlap gives
the original literal orbit ideal, not a newly chosen rank-one module. -/
theorem overlap_orbitIdeal (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) :
    (OrbitIdeal i).map (overlapCoefficient s i hi) = (factorData s hs).leftIdeal := by
  change (chartFactorData i).leftIdeal.map (overlapCoefficient s i hi) = _
  rw [Regrading.leftIdeal_eq_span (chartFactorData i), Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [Function.comp_apply, overlap_left s hs i hi a]
    exact Ideal.mul_mem_left _ _ ((factorData s hs).left_mem a)
  · rw [Regrading.leftIdeal_eq_span (factorData s hs)]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hm : overlapCoefficient s i hi ((chartFactorData i).left a) ∈
        Ideal.span (Set.range ((overlapCoefficient s i hi) ∘ (chartFactorData i).left)) :=
      Ideal.subset_span ⟨a, rfl⟩
    have he : (factorData s hs).left a =
        (coordinateUnit s i hi : Chart s) ^ 10 *
          overlapCoefficient s i hi ((chartFactorData i).left a) := by
      rw [overlap_left s hs i hi a, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ hm

abbrev OverlapImage (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) :=
  LinearMap.range (overlapMatrix s i hi).mulVecLin

def overlapImageEquiv (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) :
    OverlapImage s i hi ≃ₗ[Chart s] Regrading.Image (factorData s hs) :=
  LinearEquiv.ofEq _ _ (by
    change LinearMap.range (overlapMatrix s i hi).mulVecLin = _
    rw [overlapMatrix_eq s hs i hi]
    exact Regrading.normalized_matrix_range (factorData s hs) (coordinateUnit s i hi))

def overlapImageDual (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) :
    OverlapImage s i hi ≃ₗ[Chart s] ((factorData s hs).leftIdeal →ₗ[Chart s] Chart s) :=
  (overlapImageEquiv s hs i hi).trans
    (Regrading.normalizedImageDual (factorData s hs) (coordinateUnit s i hi))

def overlapLeftElement (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (a : Fin 3) : (factorData s hs).leftIdeal :=
  ⟨overlapCoefficient s i hi ((chartFactorData i).left a), by
    rw [overlap_left s hs i hi a]
    exact Ideal.mul_mem_left _ _ ((factorData s hs).left_mem a)⟩

/-- The overlap comparison has the exact evaluation formula of the
actual chart comparison on its actual dehomogenized ideal generators. -/
theorem overlapImageDual_selected (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (z : OverlapImage s i hi) (a : Fin 3) :
    overlapImageDual s hs i hi z (overlapLeftElement s hs i hi a) = z.val a := by
  have he : overlapLeftElement s hs i hi a =
      (((coordinateUnit s i hi)⁻¹ : (Chart s)ˣ) : Chart s) ^ 10 •
        leftElement (factorData s hs) a := by
    apply Subtype.ext
    exact overlap_left s hs i hi a
  rw [he]
  exact Regrading.normalizedImageDual_selected (factorData s hs)
    (coordinateUnit s i hi) (overlapImageEquiv s hs i hi z) a

/-- The literal vector evaluations uniquely determine the overlap
functional. Thus the comparison is fixed by the original chart map. -/
theorem overlapImageDual_unique (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (z : OverlapImage s i hi)
    (φ : (factorData s hs).leftIdeal →ₗ[Chart s] Chart s)
    (hφ : ∀ a, φ (overlapLeftElement s hs i hi a) = z.val a) :
    φ = overlapImageDual s hs i hi z := by
  apply Regrading.dual_ext (factorData s hs)
  intro a
  have he : leftElement (factorData s hs) a =
      (coordinateUnit s i hi : Chart s) ^ 10 • overlapLeftElement s hs i hi a := by
    apply Subtype.ext
    change (factorData s hs).left a =
      (coordinateUnit s i hi : Chart s) ^ 10 *
        overlapCoefficient s i hi ((chartFactorData i).left a)
    rw [overlap_left s hs i hi a, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [he, map_smul, map_smul, hφ, overlapImageDual_selected]

def overlapImageTransition (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (j : Fin 3) (hj : j ∈ s) :
    OverlapImage s i hi ≃ₗ[Chart s] OverlapImage s j hj :=
  ((overlapImageEquiv s hs i hi).trans
    (LinearEquiv.smulOfUnit ((coordinateUnit s i hi / coordinateUnit s j hj) ^ 14))).trans
      (overlapImageEquiv s hs j hj).symm

/-- The actual normalized image vector has transition `(Xi/Xj)^14`. -/
theorem overlapImageTransition_val (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (j : Fin 3) (hj : j ∈ s)
    (z : OverlapImage s i hi) :
    (overlapImageTransition s hs i hi j hj z).val =
      ((coordinateUnit s i hi / coordinateUnit s j hj : (Chart s)ˣ) : Chart s) ^ 14 • z.val := rfl

/-- The literal linkage comparison has the positive fourth-power
transition, retaining `I_E^dual(4)` rather than discarding the twist. -/
theorem overlapImageDual_transition (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (j : Fin 3) (hj : j ∈ s)
    (z : OverlapImage s i hi) :
    overlapImageDual s hs j hj (overlapImageTransition s hs i hi j hj z) =
      ((coordinateUnit s i hi / coordinateUnit s j hj : (Chart s)ˣ) : Chart s) ^ 4 •
        overlapImageDual s hs i hi z := by
  simp only [overlapImageDual, overlapImageTransition, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact Regrading.normalizedImageDual_transition (factorData s hs)
    (coordinateUnit s i hi) (coordinateUnit s j hj) (overlapImageEquiv s hs i hi z)

#print axioms overlapMatrix_eq
#print axioms overlap_orbitIdeal
#print axioms overlapImageDual_selected
#print axioms overlapImageDual_unique
#print axioms overlapImageTransition_val
#print axioms overlapImageDual_transition

end CycleQ2SeedProjectiveImageTwist
end
