import Proposal.GeometricLiteralNativeTransitionUnits

/-!
# The original Cartier generators on the native intersections

The generators are restrictions of the already constructed original
refined generators of the actual curve ideal. Their values are the
original f2/X_l^2 and f1/X_l^2, and their regularity is proved on each
actual product localization using the original cofactor torsion bounds.
Reduction of the corresponding native homogeneous fractions gives
precisely these original generators.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCartierFrames

open HomogeneousLocalization CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveVertexRestrictions
  CycleQ2LiteralNativeHomogeneousFractions CycleQ2GradedLocalizationProjection

def closedCoordinateValue (s : Finset Vertex) (v : Vertex) : ClosedCone s :=
  algebraMap (SurfaceRing 57 1) (ClosedCone s)
    (CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 v.2)

theorem reduction_coordinateValue (s : Finset Vertex) (v : Vertex) :
    ordinaryReduction s (coordinateValue s v) = closedCoordinateValue s v := by
  change ordinaryReduction s (algebraMap GradedDeformation (ThickCone s) (coordinateElement v.2)) = _
  rw [CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base, reduction_coordinateElement]
  rfl

theorem closedCoordinateValue_isUnit (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    IsUnit (closedCoordinateValue s v) := by
  rw [← reduction_coordinateValue]
  exact (coordinateValue_isUnit s v hv).map (ordinaryReduction s)

def generator (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) : ClosedRing s :=
  closedVertexRestriction s v hv (refinedGenerator 57 1 v.1 v.2)

theorem generator_first_mul (s : Finset Vertex) (l : Fin 3) (hv : (0,l) ∈ s) :
    (generator s (0,l) hv).val * closedCoordinateValue s (0,l) ^ 2 =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 originalF2) := by
  rw [generator, closedVertexRestriction_val]
  have h := congrArg (closedVertexConeRestriction s (0,l) hv)
    (refinedGenerator_first_val_mul 57 1 l)
  rw [map_mul, map_pow, (closedVertexConeRestriction s (0,l) hv).commutes,
    (closedVertexConeRestriction s (0,l) hv).commutes] at h
  exact h

theorem generator_second_mul (s : Finset Vertex) (l : Fin 3) (hv : (1,l) ∈ s) :
    (generator s (1,l) hv).val * closedCoordinateValue s (1,l) ^ 2 =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 (originalF1 57)) := by
  rw [generator, closedVertexRestriction_val]
  have h := congrArg (closedVertexConeRestriction s (1,l) hv)
    (refinedGenerator_second_val_mul 57 1 l)
  rw [map_mul, map_pow, (closedVertexConeRestriction s (1,l) hv).commutes,
    (closedVertexConeRestriction s (1,l) hv).commutes] at h
  exact h

theorem generator_third (s : Finset Vertex) (l : Fin 3) (hv : (2,l) ∈ s) :
    generator s (2,l) hv = 1 := by
  change closedVertexRestriction s (2,l) hv 1 = 1
  exact map_one _

theorem generator_fourth (s : Finset Vertex) (l : Fin 3) (hv : (3,l) ∈ s) :
    generator s (3,l) hv = 1 := by
  change closedVertexRestriction s (3,l) hv 1 = 1
  exact map_one _

theorem first_polynomial_regular (s : Finset Vertex) (hv : Admissible s 0) :
    IsSMulRegular (ClosedCone s)
      (algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 originalF2)) := by
  apply regular_after_localizing
  intro x hx
  obtain ⟨q,hq⟩ := closedCartier_dvd hv
  change closedProduct s = surfaceQuotient 57 1 (originalG1 57) * q at hq
  rw [hq, mul_right_comm, first_generator_torsion 57 1 x hx, zero_mul]

theorem second_polynomial_regular (s : Finset Vertex) (hv : Admissible s 1) :
    IsSMulRegular (ClosedCone s)
      (algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 (originalF1 57))) := by
  apply regular_after_localizing
  intro x hx
  obtain ⟨q,hq⟩ := closedCartier_dvd hv
  change closedProduct s = surfaceQuotient 57 1 originalG2 * q at hq
  rw [hq, mul_right_comm, second_generator_torsion 57 1 x hx, zero_mul]

theorem generator_first_regular (s : Finset Vertex) (l : Fin 3) (hv : (0,l) ∈ s) :
    IsSMulRegular (ClosedRing s) (generator s (0,l) hv) := by
  apply isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply (first_polynomial_regular s ⟨l,hv⟩).right_eq_zero_of_smul
  change algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 originalF2) * x = 0
  change (generator s (0,l) hv).val * x = 0 at hx
  rw [← generator_first_mul s l hv]
  calc
    ((generator s (0,l) hv).val * closedCoordinateValue s (0,l) ^ 2) * x =
        closedCoordinateValue s (0,l) ^ 2 * ((generator s (0,l) hv).val * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

theorem generator_second_regular (s : Finset Vertex) (l : Fin 3) (hv : (1,l) ∈ s) :
    IsSMulRegular (ClosedRing s) (generator s (1,l) hv) := by
  apply isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply (second_polynomial_regular s ⟨l,hv⟩).right_eq_zero_of_smul
  change algebraMap (SurfaceRing 57 1) (ClosedCone s) (surfaceQuotient 57 1 (originalF1 57)) * x = 0
  change (generator s (1,l) hv).val * x = 0 at hx
  rw [← generator_second_mul s l hv]
  calc
    ((generator s (1,l) hv).val * closedCoordinateValue s (1,l) ^ 2) * x =
        closedCoordinateValue s (1,l) ^ 2 * ((generator s (1,l) hv).val * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

theorem generator_regular (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    IsSMulRegular (ClosedRing s) (generator s v hv) := by
  rcases v with ⟨a,l⟩
  fin_cases a
  · exact generator_first_regular s l hv
  · exact generator_second_regular s l hv
  · change IsSMulRegular (ClosedRing s) (generator s (2,l) hv)
    rw [generator_third s l hv]
    exact IsSMulRegular.one _
  · change IsSMulRegular (ClosedRing s) (generator s (3,l) hv)
    rw [generator_fourth s l hv]
    exact IsSMulRegular.one _

theorem reduction_normalized_mul (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    {k : ℕ} (p : GradedDeformation) (hp : p ∈ deformationGrade k) :
    (nativeReduction s (normalized s v hv p hp)).val * closedCoordinateValue s v ^ k =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) (reduction p) := by
  have h := congrArg (ordinaryReduction s) (normalized_val_mul s v hv p hp)
  rw [map_mul, map_pow, ordinaryReduction_val, reduction_coordinateValue,
    CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base] at h
  exact h

theorem reduced_normalized_first_generator (s : Finset Vertex) (l : Fin 3) (hv : (0,l) ∈ s) :
    nativeReduction s (normalized s (0,l) hv (cartierElement 3) (cartierElement_homogeneous 3)) =
      generator s (0,l) hv := by
  apply HomogeneousLocalization.val_injective
  apply ((closedCoordinateValue_isUnit s (0,l) hv).pow 2).mul_right_cancel
  rw [generator_first_mul]
  have h := reduction_normalized_mul s (0,l) hv (cartierElement 3) (cartierElement_homogeneous 3)
  rw [reduction_cartierElement] at h
  exact h

theorem reduced_normalized_second_generator (s : Finset Vertex) (l : Fin 3) (hv : (1,l) ∈ s) :
    nativeReduction s (normalized s (1,l) hv (cartierElement 2) (cartierElement_homogeneous 2)) =
      generator s (1,l) hv := by
  apply HomogeneousLocalization.val_injective
  apply ((closedCoordinateValue_isUnit s (1,l) hv).pow 2).mul_right_cancel
  rw [generator_second_mul]
  have h := reduction_normalized_mul s (1,l) hv (cartierElement 2) (cartierElement_homogeneous 2)
  rw [reduction_cartierElement] at h
  exact h

end CycleQ2LiteralNativeCartierFrames

end

#print axioms CycleQ2LiteralNativeCartierFrames.generator_regular
#print axioms CycleQ2LiteralNativeCartierFrames.reduced_normalized_first_generator
#print axioms CycleQ2LiteralNativeCartierFrames.reduced_normalized_second_generator
