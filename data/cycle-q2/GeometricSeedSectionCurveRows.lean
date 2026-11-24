import Proposal.GeometricSeedSectionSheafImage
import Proposal.GeometricSpecializedCurveCoordinateChart
import Proposal.GeometricLiteralProjectiveBinding

/-!
# The existing specialized-curve rows in the original surface sections

The existing identity-on-polynomials graded equivalence carries the
normalized row fractions of the existing specialized curve to the
original Cartier coordinate fractions. Their actual projective sections
are exactly the rows already obtained as the global evaluation image.

Both the projective surface isomorphism and the specialized curve are the
previously defined objects. No second curve or surface model is introduced.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionCurveRows

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial Matrix
open CycleQ2SeedTrace CycleQ2GeometricSurfaceAdjunction
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionBalance CycleQ2SeedSectionSheafImage
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SurfaceCoordinateSections
  CycleQ2RelativeConstantSection CycleQ2RelativeCurveChart

abbrev seed := CycleQ2SeedConeSection.seed

/-- The existing graded equivalence sends each literal homogeneous
fraction to the fraction with the same numerator and denominator. -/
theorem literalCartierLocalizationEquiv_fraction (i : Fin 4) (n : ℕ)
    (p : WeightedPoly) (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n) :
    literalCartierLocalizationEquiv (X i.castSucc)
        (CycleQ2IncidenceDehomogenizedChart.homogeneousFraction seed i n p hp) =
      CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction 57 1 i n p hp := by
  have hpoly (q : WeightedPoly) :
      literalToCartierGraded (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed q) =
        CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 q :=
    literalToCartierGraded_polynomial q
  apply HomogeneousLocalization.val_injective _
  change Localization.mk
      (literalToCartierGraded
        (CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed p))
      (⟨literalToCartierGraded
        ((CycleQ2IncidenceDehomogenizedChart.surfaceQuotient seed (X i.castSucc)) ^ n),
        ⟨n, by simp only [map_pow, hpoly]⟩⟩ :
        Submonoid.powers (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
          (X i.castSucc))) =
    Localization.mk (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p)
      (⟨(CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
        (X i.castSucc)) ^ n, ⟨n, rfl⟩⟩ :
        Submonoid.powers (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
          (X i.castSucc)))
  simp only [map_pow, hpoly]

/-- The unchanged original affine matrix evaluates the same specialized
row polynomial as the already defined curve quotient. -/
theorem affinePolynomial_relativeSection (t : Fin 3 → ℂ) (i a : Fin 3) :
    affinePolynomial i (relativeSectionPolynomial seed t a) =
      ((chartFactorData i).matrix *ᵥ
        (fun b => algebraMap ℂ (AffineRing i) (t b))) a := by
  simp only [relativeSectionPolynomial, map_sum, map_mul,
    Algebra.algebraMap_self, RingHom.id_apply,
    CycleQ2SeedConeSection.pointMatrixPolynomial_seed,
    affinePolynomial_constant, ← chartMatrix_polynomial, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem sectionRows_polynomial (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (a : Fin 3) :
    sectionRows t i V hi a =
      polynomialSection i V hi (relativeSectionPolynomial seed t a) :=
  congrArg (chartSectionMap i V hi) (affinePolynomial_relativeSection t i a).symm

/-- The actual seed coordinate ring, read in the original Cartier
structure sheaf through the existing graded localization equivalence. -/
def seedCoordinateSectionsEquiv (i : Fin 3) :
    CycleQ2IncidenceDehomogenizedChart.CoordinateRing seed i.succ ≃+*
      Γ(Surface, Patch i) :=
  (literalCartierLocalizationEquiv (X i.succ.castSucc)).trans
    (Proj.basicOpenIsoAway (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
        (X i.succ.castSucc))
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i.succ)
      (by decide)).commRingCatIsoToRingEquiv

/-- The existing specialized normalized row is precisely the original
global-evaluation row section, with the same fixed complex vector. -/
theorem seedCoordinateSectionsEquiv_normalizedSection
    (t : Fin 3 → ℂ) (i a : Fin 3) :
    seedCoordinateSectionsEquiv i (normalizedSection seed t i.succ a) =
      sectionRows t i (Patch i) le_rfl a := by
  change (Proj.basicOpenIsoAway (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
        (X i.succ.castSucc))
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i.succ)
      (by decide)).hom
    (literalCartierLocalizationEquiv (X i.succ.castSucc)
      (CycleQ2IncidenceDehomogenizedChart.homogeneousFraction seed i.succ 14
        (relativeSectionPolynomial seed t a)
        (relativeSectionPolynomial_homogeneous seed t a))) = _
  rw [literalCartierLocalizationEquiv_fraction, sectionRows_polynomial]
  have h := coordinatePolynomialSection_fraction 57 1 i.succ (Patch i) le_rfl 14
    (relativeSectionPolynomial seed t a) (relativeSectionPolynomial_homogeneous seed t a)
  simpa only [homOfLE_refl, op_id, Surface.presheaf.map_id,
    ConcreteCategory.id_apply, polynomialSection, chartSectionMap,
    affinePolynomial, coordinatePolynomialSection] using h.symm

/-- The kernel generators of the actual specialized quotient map become
exactly the original row-image ideal in the actual surface section ring. -/
theorem normalizedSectionIdeal_map_to_sections (t : Fin 3 → ℂ) (i : Fin 3) :
    (normalizedSectionIdeal seed t i.succ).map (seedCoordinateSectionsEquiv i).toRingHom =
      Ideal.span (Set.range (sectionRows t i (Patch i) le_rfl)) := by
  rw [normalizedSectionIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact seedCoordinateSectionsEquiv_normalizedSection t i a

end CycleQ2SeedSectionCurveRows

end

#print axioms CycleQ2SeedSectionCurveRows.literalCartierLocalizationEquiv_fraction
#print axioms CycleQ2SeedSectionCurveRows.seedCoordinateSectionsEquiv_normalizedSection
#print axioms CycleQ2SeedSectionCurveRows.normalizedSectionIdeal_map_to_sections
