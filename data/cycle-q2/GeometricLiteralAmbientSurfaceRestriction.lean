import Proposal.GeometricLiteralAmbientSurface
import Proposal.GeometricLiteralMovingDivisorCoordinate
import Proposal.GeometricLiteralAffineCotangent
import Proposal.GeometricGradedAwaySpecialization

/-!
# Restriction of an ambient family chart to a closed surface intersection

Each vertex in the intersection contributes its weight-one coordinate to
the product denominator. Specializing the ambient chart, then restricting
to that product, recovers the native closed surface map and its fractions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientSurfaceRestriction

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
  CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceOverlap CycleQ2SurfaceCoordinateSections
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralNativeCartierTransitions CycleQ2GradedAwaySpecialization
  CycleQ2SeedProjectiveFamily CycleQ2GeometricIncidenceProj CycleQ2SeedCubicFamily
  CycleQ2LiteralAmbientSurface CycleQ2LiteralAffineCotangent

local instance familyCommRing (r : ℂ) : CommRing (FamilyRing r) :=
  Ideal.Quotient.commRing (familyIdeal r)

private abbrev sg (i : Fin 4) :=
  CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i
private abbrev fg (i : Fin 4) := CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i

theorem closedProduct_coordinate (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    closedProduct s = coordinateDen 57 1 v.2.succ * reduction (coordinateComplement s v) := by
  have hc : reduction (coordinateElement v.2) = coordinateDen 57 1 v.2.succ :=
    (reduction_coordinateElement v.2).trans
      (CycleQ2SurfaceSectionCoefficients.coordinateElement_eq 57 1 v.2)
  have h := congrArg reduction (thickProduct_coordinate s v hv)
  rw [map_mul, hc, mul_comm] at h
  exact (reduction_thickProduct s).symm.trans h

private theorem coordinate_specializes (i : Fin 4) :
    toSurfaceGraded (familyCoordinate 57 i.castSucc) = coordinateDen 57 1 i := by
  change surfaceQuotient 57 1 (MvPolynomial.map _ (X i.castSucc)) = surfaceQuotient 57 1 (X i.castSucc)
  rw [MvPolynomial.map_X]

private abbrev coordinateSpecialization (i : Fin 4) :=
  awayMapOfEq toSurfaceGraded (familyCoordinate 57 i.castSucc) (coordinateDen 57 1 i)
    (coordinate_specializes i)

/-- The actual ambient coordinate chart restricted to the closed intersection. -/
def restriction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :
    CycleQ2SeedFamilyChart.ChartRing 57 v.2.succ →+* ClosedRing s :=
  (awayMap (surfaceGrade 57 1) (reductionGraded.2 (coordinateComplement_homogeneous s v))
    (closedProduct_coordinate s v hv)).comp (coordinateSpecialization v.2.succ)

private theorem mapped_homogeneous {n : ℕ} (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p).IsWeightedHomogeneous weight n := by
  intro e he
  apply hp
  intro hz
  exact he (by rw [coeff_map, hz, map_zero])

/-- Restricting a homogeneous family polynomial gives the reduction of its
actual normalized fraction on the first-order intersection. -/
theorem restriction_fraction (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (n : ℕ) (p : FamilyPolynomial) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    restriction s v hv (CycleQ2SeedFamilyChart.homogeneousFraction 57 v.2.succ n p hp) =
      nativeReduction s (normalized s v hv
        (polynomialInGraded (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p))
        (quotientMap_mem_grade (includePolynomial_homogeneous (mapped_homogeneous p hp)))) := by
  apply HomogeneousLocalization.val_injective
  simp only [restriction, RingHom.comp_apply, CycleQ2SeedFamilyChart.homogeneousFraction,
    coordinateSpecialization, awayMapOfEq_mk _ _ _ _ (fg _) (sg _), awayMap_mk, normalized,
    nativeReduction_mk, Away.val_mk, map_mul, map_pow, reduction_polynomial]
  rfl

private theorem awayι_degree_congr {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (a : A) {d e : ℕ} (h : d = e)
    (hd : a ∈ G d) (he : a ∈ G e) (hd' : 0 < d) (he' : 0 < e) :
    Proj.awayι G a hd hd' = Proj.awayι G a he he' := by
  subst e
  rfl

private theorem restrict_surface (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    Spec.map (CommRingCat.ofHom (awayMap (surfaceGrade 57 1)
      (reductionGraded.2 (coordinateComplement_homogeneous s v)) (closedProduct_coordinate s v hv))) ≫
        Proj.awayι (surfaceGrade 57 1) (coordinateDen 57 1 v.2.succ) (sg _) (by decide) =
      closedAffineMap s hs := by
  rw [Proj.SpecMap_awayMap_awayι]
  exact awayι_degree_congr _ _ ((Nat.add_comm 1 _).trans (productDegree_coordinate s v hv).symm) _ _ _ _

private theorem spec_factor {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    {X Y : Scheme} (g : A →+* B) (k : B →+* C) (a : Spec (CommRingCat.of A) ⟶ Y)
    (b : Spec (CommRingCat.of B) ⟶ X) (c : Spec (CommRingCat.of C) ⟶ X) (q : X ⟶ Y)
    (h : b ≫ q = Spec.map (CommRingCat.ofHom g) ≫ a)
    (hk : Spec.map (CommRingCat.ofHom k) ≫ b = c) :
    Spec.map (CommRingCat.ofHom (k.comp g)) ≫ a = c ≫ q := by
  change Spec.map (CommRingCat.ofHom g ≫ CommRingCat.ofHom k) ≫ a = _
  rw [Spec.map_comp, Category.assoc, ← h, ← Category.assoc, hk]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
private theorem coordinate_square (i : Fin 4) :
    Proj.awayι (surfaceGrade 57 1) (coordinateDen 57 1 i) (sg i) (by decide) ≫ surfaceToFamily =
      Spec.map (CommRingCat.ofHom (coordinateSpecialization i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc) (fg i) (by decide) :=
  awayι_comp_map_of_eq (𝒜 := familyGrade 57) (ℬ := surfaceGrade 57 1)
    toSurfaceGraded CycleQ2LiteralAmbientSurface.irrelevant_le (familyCoordinate 57 i.castSucc)
      (coordinateDen 57 1 i) (coordinate_specializes i) (by decide : 0 < 1) (fg i) (sg i)

set_option maxHeartbeats 1200000 in
/-- The restricted ambient chart and the native closed surface immersion
give the same map to the full parameter family. -/
theorem restriction_toFamily (s : Finset Vertex) (hs : s.Nonempty) (v : Vertex) (hv : v ∈ s) :
    Spec.map (CommRingCat.ofHom (restriction s v hv)) ≫
      Proj.awayι (familyGrade 57) (familyCoordinate 57 v.2.succ.castSucc)
        (fg _) (by decide) = closedAffineMap s hs ≫ surfaceToFamily :=
  spec_factor (coordinateSpecialization v.2.succ)
    (awayMap (surfaceGrade 57 1) (reductionGraded.2 (coordinateComplement_homogeneous s v))
      (closedProduct_coordinate s v hv)) _ _ _ surfaceToFamily
    (coordinate_square v.2.succ)
    (restrict_surface s hs v hv)

end CycleQ2LiteralAmbientSurfaceRestriction
end

#print axioms CycleQ2LiteralAmbientSurfaceRestriction.restriction_fraction
#print axioms CycleQ2LiteralAmbientSurfaceRestriction.restriction_toFamily
