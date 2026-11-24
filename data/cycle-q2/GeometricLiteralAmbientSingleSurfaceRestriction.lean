import Proposal.GeometricLiteralAmbientSurface
import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricGradedAwaySpecialization

/-!
# Single-coordinate restriction from the ambient cubic family to its surface

The degree-zero localization map preserves each homogeneous fraction after
specializing its coefficients. Its spectrum gives the native restriction of
the graded surface inclusion on the whole weight-one chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientSingleSurfaceRestriction

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
  CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceOverlap CycleQ2GradedAwaySpecialization
  CycleQ2SeedProjectiveFamily CycleQ2GeometricIncidenceProj CycleQ2SeedCubicFamily
  CycleQ2LiteralAmbientSurface

local instance familyCommRing (r : ℂ) : CommRing (FamilyRing r) :=
  Ideal.Quotient.commRing (familyIdeal r)

private abbrev sg (i : Fin 4) :=
  CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i
private abbrev fg (i : Fin 4) := CycleQ2SeedFamilyChart.coordinate_mem_grade 57 i

private theorem coordinate_specializes (i : Fin 4) :
    toSurfaceGraded (familyCoordinate 57 i.castSucc) = coordinateDen 57 1 i := by
  change surfaceQuotient 57 1 (MvPolynomial.map _ (X i.castSucc)) = surfaceQuotient 57 1 (X i.castSucc)
  rw [MvPolynomial.map_X]

def coordinateSpecialization (i : Fin 4) :=
  awayMapOfEq toSurfaceGraded (familyCoordinate 57 i.castSucc) (coordinateDen 57 1 i)
    (coordinate_specializes i)

theorem mapped_homogeneous {n : ℕ} (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p).IsWeightedHomogeneous weight n := by
  intro e he
  apply hp
  intro hz
  exact he (by rw [coeff_map, hz, map_zero])

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
theorem coordinate_square (i : Fin 4) :
    Proj.awayι (surfaceGrade 57 1) (coordinateDen 57 1 i) (sg i) (by decide) ≫ surfaceToFamily =
      Spec.map (CommRingCat.ofHom (coordinateSpecialization i)) ≫
        Proj.awayι (familyGrade 57) (familyCoordinate 57 i.castSucc) (fg i) (by decide) :=
  awayι_comp_map_of_eq (𝒜 := familyGrade 57) (ℬ := surfaceGrade 57 1)
    toSurfaceGraded CycleQ2LiteralAmbientSurface.irrelevant_le (familyCoordinate 57 i.castSucc)
      (coordinateDen 57 1 i) (coordinate_specializes i) (by decide : 0 < 1) (fg i) (sg i)

/-- Fraction specialization on the given axis, before passing to any smaller open. -/
theorem coordinate_fraction (i : Fin 4) (n : ℕ) (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    coordinateSpecialization i (CycleQ2SeedFamilyChart.homogeneousFraction 57 i n p hp) =
      CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction 57 1 i n
        (MvPolynomial.map (coefficientEvaluation incidenceCoefficients) p)
        (mapped_homogeneous p hp) := by
  unfold coordinateSpecialization CycleQ2SeedFamilyChart.homogeneousFraction
    CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction
  rw [awayMapOfEq_mk _ _ _ _ (fg i) (sg i)]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk] <;> rfl

end CycleQ2LiteralAmbientSingleSurfaceRestriction
end

#print axioms CycleQ2LiteralAmbientSingleSurfaceRestriction.coordinate_square
#print axioms CycleQ2LiteralAmbientSingleSurfaceRestriction.coordinate_fraction
