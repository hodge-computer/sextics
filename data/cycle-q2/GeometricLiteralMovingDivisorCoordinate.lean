import Proposal.GeometricLiteralNativeDifferentialSections
import Proposal.GeometricSeedProjectiveImageCocycle
import Proposal.GeometricSurfaceSectionCoefficients

/-!
# The moving divisor's coordinate transition on the original surface

Reducing a normalized homogeneous fraction and passing to actual sections
gives the original chart polynomial section. For a coordinate numerator,
the lifted ratio from u to v is the inverse of the seed chart transition.
The equality persists under restriction to every subopen of an intersection.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingDivisorCoordinate

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
  CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2SurfaceCoordinateSections
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralNativeTransitionUnits CycleQ2LiteralNativeCartierTransitions

private theorem coordinate_reduces (i : Fin 3) :
    reduction (coordinateElement i) = coordinateDen 57 1 i.succ :=
  (reduction_coordinateElement i).trans
    (CycleQ2SurfaceSectionCoefficients.coordinateElement_eq 57 1 i)

private theorem closedProduct_coordinate (s : Finset Vertex) (u : Vertex) (hu : u ∈ s) :
    closedProduct s = coordinateDen 57 1 u.2.succ * reduction (coordinateComplement s u) := by
  have h := congrArg reduction (thickProduct_coordinate s u hu)
  rw [map_mul, coordinate_reduces, mul_comm] at h
  exact (reduction_thickProduct s).symm.trans h

theorem closedOpen_le_patch (s : Finset Vertex) (u : Vertex) (hu : u ∈ s) :
    closedOpen s ≤ Patch u.2 :=
  Proj.basicOpen_mono (surfaceGrade 57 1) _ _
    ⟨_, closedProduct_coordinate s u hu⟩

/-- The original chart's homogeneous numerator `p` represents exactly the
reduction of its lifted homogeneous fraction on every finite intersection. -/
theorem normalized_polynomialSection (s : Finset Vertex) (hs : s.Nonempty)
    (u : Vertex) (hu : u ∈ s) (k : ℕ)
    (a : GradedDeformation) (ha : a ∈ deformationGrade k)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight k)
    (hap : reduction a = surfaceQuotient 57 1 p) :
    closedSectionsEquiv s hs (nativeReduction s (normalized s u hu a ha)) =
      polynomialSection u.2 (closedOpen s) (closedOpen_le_patch s u hu) p := by
  let hc := reductionGraded.2 (coordinateComplement_homogeneous s u)
  let hf := closedProduct_coordinate s u hu
  let b := homogeneousFraction 57 1 u.2.succ k p hp
  have he : nativeReduction s (normalized s u hu a ha) =
      awayMap (surfaceGrade 57 1) hc hf b := by
    apply HomogeneousLocalization.val_injective
    simp only [normalized, nativeReduction_mk, b, homogeneousFraction, awayMap_mk,
      Away.val_mk, map_mul, map_pow, hap]
    rfl
  rw [he]
  change _ = coordinatePolynomialSection 57 1 u.2.succ _ _ p
  rw [coordinatePolynomialSection_fraction 57 1 u.2.succ _ _ k p hp]
  exact congrArg (fun f => f b) (Proj.awayMap_awayToSection (surfaceGrade 57 1) hc hf)

/-- The genuine reduced coordinate unit is X_v / X_u. -/
theorem sectionUnit_coordinateRatio (s : Finset Vertex) (hs : s.Nonempty)
    (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    CycleQ2LiteralNativeDifferentialSections.sectionUnit s hs
        (reduceUnit s (CycleQ2LiteralNativeTransitionUnits.coordinateRatio s u v hu hv)) =
      (transitionUnit u.2 v.2 (closedOpen s)
        (closedOpen_le_patch s u hu) (closedOpen_le_patch s v hv))⁻¹ := by
  apply Units.ext
  change closedSectionsEquiv s hs (nativeReduction s
    (normalizedConeUnit s u hu _ _ _ _ : ThickRing s)) = _
  rw [normalizedConeUnit_value]
  exact normalized_polynomialSection s hs u hu 1 (coordinateElement v.2)
    (coordinateElement_homogeneous v.2) (X v.2.succ.castSucc)
    (by simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight v.2.succ.castSucc)
    (coordinate_reduces v.2)

theorem restrict_coordinateRatio (s : Finset Vertex) (hs : s.Nonempty)
    (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ closedOpen s) :
    Units.map (Surface.presheaf.map (homOfLE hW).op).hom.toMonoidHom
      (CycleQ2LiteralNativeDifferentialSections.sectionUnit s hs
        (reduceUnit s (CycleQ2LiteralNativeTransitionUnits.coordinateRatio s u v hu hv))) =
      (transitionUnit u.2 v.2 W (hW.trans (closedOpen_le_patch s u hu))
        (hW.trans (closedOpen_le_patch s v hv)))⁻¹ := by
  rw [sectionUnit_coordinateRatio, map_inv, transitionUnit_restrict]

end CycleQ2LiteralMovingDivisorCoordinate

end

#print axioms CycleQ2LiteralMovingDivisorCoordinate.normalized_polynomialSection
#print axioms CycleQ2LiteralMovingDivisorCoordinate.restrict_coordinateRatio
