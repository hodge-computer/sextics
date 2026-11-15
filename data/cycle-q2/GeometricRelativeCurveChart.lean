import Proposal.GeometricRelativeConstantCurve
import Proposal.GeometricGradedIdealContraction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual weight-one chart quotients of the relative constant-section curve

On each original weight-one surface chart, the three homogeneous rows
are divided by the fourteenth power of that chart's coordinate. The
degree-zero ideal contraction theorem identifies their span with the
kernel of the actual homogeneous quotient's Away map. The existing
surface chart equivalence sends these fractions to the literal shifted
dehomogenized rows. Quotienting therefore identifies the actual curve
chart ring, over its original coefficient algebra, with that explicit
affine three-row quotient.

Source-only draft: no Lean elaboration or kernel replay has been run.
No flatness, nonemptiness, or global projective fiber assertion is made.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeCurveChart

open MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2RelativeConstantSection CycleQ2RelativeConstantCurve
  CycleQ2GradedLocalizationProjection CycleQ2GradedIdealContraction

variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4)

def normalizedSection (j : Fin 3) : CoordinateRing y i :=
  homogeneousFraction y i 14 (relativeSectionPolynomial y t j)
    (relativeSectionPolynomial_homogeneous y t j)

def normalizedSectionIdeal : Ideal (CoordinateRing y i) :=
  Ideal.span (Set.range (normalizedSection y t i))

def affineSectionEquation (j : Fin 3) : DehomogenizedRing y i :=
  dehomogenizedMap y i (dehomogenize i (relativeSectionPolynomial y t j))

def affineSectionIdeal : Ideal (DehomogenizedRing y i) :=
  Ideal.span (Set.range (affineSectionEquation y t i))

abbrev AffineCurveChart := DehomogenizedRing y i ⧸ affineSectionIdeal y t i

theorem normalizedSection_val_mul (j : Fin 3) :
    (normalizedSection y t i j).val *
      algebraMap (PointSurface y) (CoordinateLocalization y i)
        (surfaceQuotient y (X i.castSucc)) ^ 14 =
      algebraMap (PointSurface y) (CoordinateLocalization y i) (relativeEquation y t j) := by
  have hs := IsLocalization.mk'_spec (CoordinateLocalization y i)
    (relativeEquation y t j) (powerDenominator (surfaceQuotient y (X i.castSucc)) 14)
  simpa only [normalizedSection, homogeneousFraction, relativeEquation,
    surfaceQuotient, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    powerDenominator, map_pow] using hs

/-- Inverting the coordinate makes the homogeneous rows and their
degree-zero normalized fractions generate the same ordinary ideal. -/
theorem relativeSectionIdeal_localize_coordinate :
    (relativeSectionIdeal y t).map
        (algebraMap (PointSurface y) (CoordinateLocalization y i)) =
      (normalizedSectionIdeal y t i).map
        (algebraMap (CoordinateRing y i) (CoordinateLocalization y i)) := by
  simp only [relativeSectionIdeal, normalizedSectionIdeal, Ideal.map_span,
    Set.image_range, Ideal.span_range_eq_iSup]
  apply iSup_congr
  intro j
  change Ideal.span {algebraMap (PointSurface y) (CoordinateLocalization y i)
    (relativeEquation y t j)} = Ideal.span {(normalizedSection y t i j).val}
  rw [← normalizedSection_val_mul,
    Ideal.span_singleton_mul_right_unit
      ((IsLocalization.Away.algebraMap_isUnit (surfaceQuotient y (X i.castSucc))).pow 14)]

abbrev CurveCoordinateRing :=
  Away (relativeCurveGrade y t)
    (relativeCurveRingMap y t (surfaceQuotient y (X i.castSucc)))

/-- Coefficients are induced through the original surface chart map. -/
instance curveCoordinateAlgebra : Algebra S (CurveCoordinateRing y t i) :=
  ((Away.map (relativeCurveRingMap y t) (surfaceQuotient y (X i.castSucc))).comp
    (algebraMap S (CoordinateRing y i))).toAlgebra

def coordinateCurveMap : CoordinateRing y i →ₐ[S] CurveCoordinateRing y t i where
  toRingHom := Away.map (relativeCurveRingMap y t) (surfaceQuotient y (X i.castSucc))
  commutes' _ := rfl

theorem coordinateCurveMap_surjective : Function.Surjective (coordinateCurveMap y t i) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (relativeCurveGrade y t)
    ((relativeCurveRingMap y t).2 (coordinate_mem_grade y i)) z
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨Away.mk (surfaceGrade y) (coordinate_mem_grade y i) n a ha, ?_⟩
  change Away.map (relativeCurveRingMap y t) (surfaceQuotient y (X i.castSucc))
    (Away.mk (surfaceGrade y) (coordinate_mem_grade y i) n a ha) = _
  simp only [Away.map_mk]

/-- The actual coordinate-chart map has exactly the three normalized
rows as its kernel, for every parameter point and every fixed vector. -/
theorem coordinateCurveMap_ker :
    RingHom.ker (coordinateCurveMap y t i) = normalizedSectionIdeal y t i := by
  change RingHom.ker (Away.map (relativeCurveRingMap y t)
    (surfaceQuotient y (X i.castSucc))) = _
  rw [CycleQ2UniversalCurveCartier.gradedAwayMap_ker (surfaceGrade y) (relativeCurveGrade y t)
    (relativeCurveRingMap y t) (surfaceQuotient y (X i.castSucc)) (coordinate_mem_grade y i),
    relativeCurveRingMap_ker, relativeSectionIdeal_localize_coordinate,
    ideal_map_comap_val (surfaceGrade y) (coordinate_mem_grade y i)]

@[simp] theorem chartEquiv_normalizedSection (j : Fin 3) :
    familyCoordinateChartEquiv y i (normalizedSection y t i j) =
      affineSectionEquation y t i j :=
  familyCoordinateChartEquiv_homogeneousFraction y i 14
    (relativeSectionPolynomial y t j) (relativeSectionPolynomial_homogeneous y t j)

theorem normalizedSectionIdeal_map :
    (normalizedSectionIdeal y t i).map (familyCoordinateChartEquiv y i).toRingHom =
      affineSectionIdeal y t i := by
  simp only [normalizedSectionIdeal, affineSectionIdeal, Ideal.map_span, Set.image_range]
  apply congrArg (fun g : Fin 3 → DehomogenizedRing y i => Ideal.span (Set.range g))
  funext j
  exact chartEquiv_normalizedSection y t i j

def coordinateQuotientEquiv :
    (CoordinateRing y i ⧸ normalizedSectionIdeal y t i) ≃ₐ[S] CurveCoordinateRing y t i :=
  (Ideal.quotientEquivAlgOfEq S (coordinateCurveMap_ker y t i).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (coordinateCurveMap_surjective y t i))

@[simp] theorem coordinateQuotientEquiv_mk (a : CoordinateRing y i) :
    coordinateQuotientEquiv y t i (Ideal.Quotient.mk (normalizedSectionIdeal y t i) a) =
      coordinateCurveMap y t i a := by
  rw [coordinateQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The actual homogeneous curve chart is the explicit quotient of the
original shifted dehomogenized surface chart, with its S-algebra map. -/
def curveCoordinateChartEquiv :
    CurveCoordinateRing y t i ≃ₐ[S] AffineCurveChart y t i :=
  (coordinateQuotientEquiv y t i).symm.trans
    (Ideal.quotientEquivAlg (normalizedSectionIdeal y t i) (affineSectionIdeal y t i)
      (familyCoordinateChartEquiv y i) (normalizedSectionIdeal_map y t i).symm)

@[simp] theorem curveCoordinateChartEquiv_map (a : CoordinateRing y i) :
    curveCoordinateChartEquiv y t i (coordinateCurveMap y t i a) =
      Ideal.Quotient.mk (affineSectionIdeal y t i) (familyCoordinateChartEquiv y i a) := by
  rw [← coordinateQuotientEquiv_mk y t i a, curveCoordinateChartEquiv,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlg_mk]

#print axioms coordinateCurveMap_ker
#print axioms normalizedSectionIdeal_map
#print axioms curveCoordinateChartEquiv
#print axioms curveCoordinateChartEquiv_map

end CycleQ2RelativeCurveChart
end
