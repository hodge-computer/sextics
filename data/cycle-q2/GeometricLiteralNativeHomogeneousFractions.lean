import Proposal.GeometricLiteralConeIntersectionTransport

/-!
# Native homogeneous fractions with the original coordinate denominators

On an actual finite intersection containing a vertex v, the original
weight-one coordinate X_v is invertible. The explicit product complement
constructs p / X_v^k as a genuine degree-zero homogeneous fraction when
p has its original degree k. Its value, restriction, and unit properties
are proved using the actual product localization, with no cancellation
of a polynomial denominator in the original ring.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeHomogeneousFractions

open HomogeneousLocalization CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveVertexRestrictions CycleQ2GradedLocalizationProjection

def coordinateComplement (s : Finset Vertex) (v : Vertex) : GradedDeformation :=
  cartierElement v.1 * thickProduct (s.erase v)

def complementDegree (s : Finset Vertex) (v : Vertex) : ℕ :=
  coverDegree v.1 + productDegree (s.erase v)

theorem coordinateComplement_homogeneous (s : Finset Vertex) (v : Vertex) :
    coordinateComplement s v ∈ deformationGrade (complementDegree s v) :=
  SetLike.mul_mem_graded (cartierElement_homogeneous v.1) (thickProduct_homogeneous (s.erase v))

theorem productDegree_coordinate (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    productDegree s = complementDegree s v + 1 := by
  have h := (Finset.add_sum_erase s (fun w : Vertex => coverDegree w.1 + 1) hv).symm
  simpa only [productDegree, complementDegree, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem thickProduct_coordinate (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    thickProduct s = coordinateComplement s v * coordinateElement v.2 := by
  rw [thickVertex_factor s v hv]
  change (cartierElement v.1 * coordinateElement v.2) * thickProduct (s.erase v) = _
  exact mul_right_comm _ _ _

def coordinateValue (s : Finset Vertex) (v : Vertex) : ThickCone s :=
  algebraMap GradedDeformation (ThickCone s) (coordinateElement v.2)

theorem coordinateValue_isUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    IsUnit (coordinateValue s v) :=
  IsLocalization.Away.isUnit_of_dvd (thickProduct s)
    ⟨coordinateComplement s v, (thickProduct_coordinate s v hv).trans (mul_comm _ _)⟩

def coordinateUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : (ThickCone s)ˣ :=
  (coordinateValue_isUnit s v hv).unit

theorem coordinateUnit_value (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    (coordinateUnit s v hv : ThickCone s) = coordinateValue s v := IsUnit.unit_spec _

/-- The original fraction p / X_v^k, using only powers of the actual
homogeneous product denominator of this intersection. -/
def normalized (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k) : ThickRing s :=
  Away.mk deformationGrade (thickProduct_homogeneous s) k (p * coordinateComplement s v ^ k) (by
    simpa only [productDegree_coordinate s v hv, nsmul_eq_mul, Nat.cast_id,
      Nat.mul_add, Nat.mul_one, Nat.add_comm] using
      SetLike.mul_mem_graded hp (SetLike.pow_mem_graded k (coordinateComplement_homogeneous s v)))

theorem normalized_val_mul (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k) :
    (normalized s v hv p hp).val * coordinateValue s v ^ k =
      algebraMap GradedDeformation (ThickCone s) p := by
  have hu : IsUnit (algebraMap GradedDeformation (ThickCone s) (coordinateComplement s v)) :=
    IsLocalization.Away.isUnit_of_dvd (thickProduct s)
      ⟨coordinateElement v.2, thickProduct_coordinate s v hv⟩
  apply (hu.pow k).mul_right_cancel
  have hspec := IsLocalization.mk'_spec (ThickCone s) (p * coordinateComplement s v ^ k)
    (powerDenominator (thickProduct s) k)
  change fraction (thickProduct s) k (p * coordinateComplement s v ^ k) *
    algebraMap GradedDeformation (ThickCone s) (thickProduct s ^ k) = _ at hspec
  simp only [normalized, Away.val_mk, Localization.mk_eq_mk']
  change (fraction (thickProduct s) k (p * coordinateComplement s v ^ k) * coordinateValue s v ^ k) *
      algebraMap GradedDeformation (ThickCone s) (coordinateComplement s v) ^ k = _
  simpa only [thickProduct_coordinate s v hv, coordinateValue, map_mul, map_pow,
    mul_pow, mul_assoc, mul_comm, mul_left_comm] using hspec

theorem normalized_isUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (hu : IsUnit (algebraMap GradedDeformation (ThickCone s) p)) : IsUnit (normalized s v hv p hp) := by
  apply CycleQ2ProjectiveInverseIdeal.isUnit_of_isUnit_val deformationGrade (thickProduct_homogeneous s)
  have hprod : IsUnit ((normalized s v hv p hp).val * coordinateValue s v ^ k) := by
    rw [normalized_val_mul]
    exact hu
  exact isUnit_of_mul_isUnit_left hprod

def normalizedUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (hu : IsUnit (algebraMap GradedDeformation (ThickCone s) p)) : (ThickRing s)ˣ :=
  (normalized_isUnit s v hv p hp hu).unit

theorem normalizedUnit_value (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k)
    (hu : IsUnit (algebraMap GradedDeformation (ThickCone s) p)) :
    (normalizedUnit s v hv p hp hu : ThickRing s) = normalized s v hv p hp := IsUnit.unit_spec _

/-- Uniqueness after multiplication by the original invertible coordinate
proves compatibility with the actual native restriction. -/
theorem normalized_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k) :
    thickRestriction hst (normalized s v hv p hp) = normalized t v (hst hv) p hp := by
  apply HomogeneousLocalization.val_injective
  apply ((coordinateValue_isUnit t v (hst hv)).pow k).mul_right_cancel
  rw [thickRestriction_val]
  have he : thickConeRestriction hst (coordinateValue s v) = coordinateValue t v :=
    thickConeRestriction_base hst (coordinateElement v.2)
  calc
    thickConeRestriction hst (normalized s v hv p hp).val * coordinateValue t v ^ k =
        thickConeRestriction hst ((normalized s v hv p hp).val * coordinateValue s v ^ k) := by
      rw [map_mul, map_pow, he]
    _ = algebraMap GradedDeformation (ThickCone t) p := by
      rw [normalized_val_mul, thickConeRestriction_base]
    _ = (normalized t v (hst hv) p hp).val * coordinateValue t v ^ k :=
      (normalized_val_mul t v (hst hv) p hp).symm

end CycleQ2LiteralNativeHomogeneousFractions

end

#print axioms CycleQ2LiteralNativeHomogeneousFractions.normalized_val_mul
#print axioms CycleQ2LiteralNativeHomogeneousFractions.normalized_isUnit
#print axioms CycleQ2LiteralNativeHomogeneousFractions.normalized_restrict
