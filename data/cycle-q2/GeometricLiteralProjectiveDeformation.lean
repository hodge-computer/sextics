import Proposal.GeometricLiteralGradedReduction
import Proposal.GeometricGradedAwaySpecialization

/-!
# The original deformation on the actual projective Cartier charts

The fixed-coordinate graded presentation gives a projective scheme.
Its actual reduction is a closed immersion of the original projective
surface. The twelve original Cartier-by-coordinate chart rings receive
surjective reduction maps from homogeneous chart rings of this scheme.
Their affine scheme squares commute with the actual closed-fibre map.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveDeformation

open MvPolynomial CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv
  CycleQ2LiteralGradedReduction CycleQ2GradedAwaySpecialization
  CycleQ2ProjectiveCartierIdeal

/-- The projectivization of the original F - epsilon B* deformation. -/
def projectiveDeformation : Scheme := Proj deformationGrade

theorem reduction_irrelevant_le :
    HomogeneousIdeal.irrelevant (surfaceGrade 57 1) ≤
      (HomogeneousIdeal.irrelevant deformationGrade).map reductionGraded := by
  change (HomogeneousIdeal.irrelevant (surfaceGrade 57 1)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant deformationGrade).map reductionGraded).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (surfaceGrade 57 1)).mpr
  intro n hn x hx
  obtain ⟨y,hy,rfl⟩ := reduction_homogeneous_surjective n x hx
  exact Ideal.mem_map_of_mem reductionGraded
    (HomogeneousIdeal.mem_irrelevant_of_mem deformationGrade hn hy)

/-- This is induced by the original reduction, with its literal surface. -/
def closedFiber : projectiveSurface 57 1 ⟶ projectiveDeformation :=
  Proj.map reductionGraded reduction_irrelevant_le

instance closedFiber_isClosedImmersion : IsClosedImmersion closedFiber :=
  CycleQ2GeometricLiteralSurface.projMap_isClosedImmersion deformationGrade
    (surfaceGrade 57 1) reductionGraded reduction_irrelevant_le
    reduction_homogeneous_surjective

@[simp] theorem closedFiber_preimage_basicOpen (p : GradedDeformation) :
    closedFiber ⁻¹ᵁ Proj.basicOpen deformationGrade p =
      Proj.basicOpen (surfaceGrade 57 1) (reduction p) := rfl

def cartierElement (a : Fin 4) : GradedDeformation :=
  polynomialInGraded (CycleQ2LiteralCartierSplittings.coverPolynomial a)

theorem cartierElement_homogeneous (a : Fin 4) :
    cartierElement a ∈ deformationGrade (coverDegree a) := by
  have hp : CycleQ2LiteralCartierSplittings.coverPolynomial a ∈ PolynomialGrade (coverDegree a) := by
    fin_cases a
    · exact originalG1_homogeneous 57
    · exact originalG2_homogeneous
    · exact originalF1_homogeneous 57
    · exact originalF2_homogeneous
  exact quotientMap_mem_grade (includePolynomial_homogeneous hp)

theorem reduction_cartierElement (a : Fin 4) :
    reduction (cartierElement a) = coverElement 57 1 a := by
  rw [cartierElement, reduction_polynomial]
  fin_cases a <;> rfl

def coordinateElement (l : Fin 3) : GradedDeformation :=
  coordinate (CycleQ2SeedQuotientFiniteFree.remainingIndex l)

theorem coordinateElement_homogeneous (l : Fin 3) :
    coordinateElement l ∈ deformationGrade 1 := by
  have h := coordinate_mem_grade (CycleQ2SeedQuotientFiniteFree.remainingIndex l)
  fin_cases l <;> exact h

theorem reduction_coordinateElement (l : Fin 3) :
    reduction (coordinateElement l) =
      CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 l := by
  have hc (i : Fin 5) : coordinate i = polynomialInGraded (X i) := by
    simp [coordinate, polynomialInGraded, includePolynomial]
  change reduction (coordinate _) = _
  rw [hc, reduction_polynomial]
  rfl

def chartDenominator (a : Fin 4) (l : Fin 3) : GradedDeformation :=
  cartierElement a * coordinateElement l

theorem chartDenominator_homogeneous (a : Fin 4) (l : Fin 3) :
    chartDenominator a l ∈ deformationGrade (coverDegree a + 1) :=
  SetLike.mul_mem_graded (cartierElement_homogeneous a) (coordinateElement_homogeneous l)

theorem reduction_chartDenominator (a : Fin 4) (l : Fin 3) :
    reductionGraded (chartDenominator a l) = refinedDenominator 57 1 a l := by
  change reduction (cartierElement a * coordinateElement l) = _
  rw [map_mul, reduction_cartierElement, reduction_coordinateElement]
  rfl

abbrev ChartRing (a : Fin 4) (l : Fin 3) :=
  Away deformationGrade (chartDenominator a l)

def chartOpen (a : Fin 4) (l : Fin 3) : projectiveDeformation.Opens :=
  Proj.basicOpen deformationGrade (chartDenominator a l)

/-- Reduction targets the exact existing native Cartier chart ring. -/
def chartReduction (a : Fin 4) (l : Fin 3) :
    ChartRing a l →+* RefinedRing 57 1 a l :=
  awayMapOfEq reductionGraded (chartDenominator a l)
    (refinedDenominator 57 1 a l) (reduction_chartDenominator a l)

theorem chartReduction_mk (a : Fin 4) (l : Fin 3) (n : ℕ)
    (p : GradedDeformation) (hp : p ∈ deformationGrade (n • (coverDegree a + 1))) :
    chartReduction a l (Away.mk deformationGrade (chartDenominator_homogeneous a l) n p hp) =
      Away.mk (surfaceGrade 57 1) (refinedDenominator_homogeneous 57 1 a l) n
        (reduction p) (reductionGraded.2 hp) :=
  awayMapOfEq_mk reductionGraded _ _ (reduction_chartDenominator a l)
    (chartDenominator_homogeneous a l) (refinedDenominator_homogeneous 57 1 a l) n p hp

theorem chartReduction_surjective (a : Fin 4) (l : Fin 3) :
    Function.Surjective (chartReduction a l) := by
  intro x
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (surfaceGrade 57 1)
    (refinedDenominator_homogeneous 57 1 a l) x
  obtain ⟨q,hq,rfl⟩ := reduction_homogeneous_surjective _ p hp
  exact ⟨Away.mk deformationGrade (chartDenominator_homogeneous a l) n q hq,
    chartReduction_mk a l n q hq⟩

theorem closedFiber_preimage_chartOpen (a : Fin 4) (l : Fin 3) :
    closedFiber ⁻¹ᵁ chartOpen a l = refinedOpen 57 1 a l := by
  change Proj.basicOpen (surfaceGrade 57 1) (reductionGraded (chartDenominator a l)) = _
  rw [reduction_chartDenominator]
  rfl

/-- The affine reduction is the ring map of the genuine Proj square. -/
@[reassoc] theorem chartReduction_scheme_square (a : Fin 4) (l : Fin 3) :
    Proj.awayι (surfaceGrade 57 1) (refinedDenominator 57 1 a l)
        (refinedDenominator_homogeneous 57 1 a l) (by omega) ≫ closedFiber =
      Spec.map (CommRingCat.ofHom (chartReduction a l)) ≫
        Proj.awayι deformationGrade (chartDenominator a l)
          (chartDenominator_homogeneous a l) (by omega) :=
  awayι_comp_map_of_eq reductionGraded reduction_irrelevant_le _ _
    (reduction_chartDenominator a l) (by omega)
    (chartDenominator_homogeneous a l) (refinedDenominator_homogeneous 57 1 a l)

instance chartReduction_isClosedImmersion (a : Fin 4) (l : Fin 3) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartReduction a l))) :=
  IsClosedImmersion.spec_of_surjective _ (chartReduction_surjective a l)

end CycleQ2LiteralProjectiveDeformation

end

#print axioms CycleQ2LiteralProjectiveDeformation.closedFiber_isClosedImmersion
#print axioms CycleQ2LiteralProjectiveDeformation.chartReduction_surjective
#print axioms CycleQ2LiteralProjectiveDeformation.chartReduction_scheme_square
