import Proposal.GeometricRegularSeedSection
import Proposal.GeometricIncidenceChartSeedFiber

/-!
# The same constant section over the original incidence parameter algebra

One complex vector is retained while the incidence coefficients vary. Its
three equations are the original rows of `M*t`, with the complex entries
mapped into the original coefficient algebra. They are homogeneous of
degree fourteen and are the literal evaluation of the existing universal
section equations. At the retained seed map they specialize to the same
constant equations used by the regular seed-section construction.

This constructs the relative homogeneous section ideal. No regularity or
flatness away from the seed, and no nonempty curve, is asserted here.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeConstantSection

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceGenericPointSemantics CycleQ2GeometricIncidenceProj
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2IncidenceEtaleParameter CycleQ2IncidencePolynomialJacobianBinding

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The section coefficients are fixed complex numbers, while the
original incidence point is allowed to vary over its coefficient ring. -/
def relativeSectionPolynomial (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i : Fin 3) : MvPolynomial (Fin 5) S :=
  ∑ j, C (algebraMap ℂ S (t j)) * pointMatrixPolynomial y i j

theorem relativeSectionPolynomial_homogeneous (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i : Fin 3) :
    relativeSectionPolynomial y t i ∈ PolynomialGrade S 14 := by
  apply (PolynomialGrade S 14).sum_mem
  intro j _
  exact (pointMatrixPolynomial_homogeneous y i j).C_mul (algebraMap ℂ S (t j))

/-- The row in the unchanged original surface quotient. -/
def relativeEquation (y : ParameterIndex → S) (t : Fin 3 → ℂ)
    (i : Fin 3) : PointSurface y :=
  Ideal.Quotient.mk (pointEquations y) (relativeSectionPolynomial y t i)

theorem relativeEquation_homogeneous (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i : Fin 3) :
    relativeEquation y t i ∈ surfaceGrade y 14 :=
  ⟨_, relativeSectionPolynomial_homogeneous y t i, rfl⟩

theorem relativePivot_homogeneous (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) : basePivot y p ∈ surfaceGrade y 14 := by
  have hp : basePivot y p = Ideal.Quotient.mk (pointEquations y)
      (pointMatrixPolynomial y p.1 p.2) := by
    rw [pointMatrixPolynomial_eq]
    rfl
  rw [hp]
  exact ⟨_, pointMatrixPolynomial_homogeneous y p.1 p.2, rfl⟩

theorem relativeEquation_eq_sum (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i : Fin 3) :
    relativeEquation y t i =
      ∑ j, algebraMap ℂ S (t j) • basePivot y (i, j) := by
  simp only [relativeEquation, relativeSectionPolynomial, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [pointMatrixPolynomial_eq, Algebra.smul_def]
  rfl

/-- The actual ordinary localization keeps the same fixed complex
coefficient vector used in the simultaneous regularity argument. -/
theorem relativeEquation_localize_row (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) (i : Fin 3) :
    algebraMap (PointSurface y) (CoefficientPivot y p) (relativeEquation y t i) =
      ∑ j, t j • localizedMatrix y p i j := by
  rw [relativeEquation_eq_sum]
  change (IsScalarTower.toAlgHom S (PointSurface y) (CoefficientPivot y p))
    (∑ j, algebraMap ℂ S (t j) • basePivot y (i, j)) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact IsScalarTower.algebraMap_smul S (t j) (localizedMatrix y p i j)

abbrev RelativeProjectivePivot (y : ParameterIndex → S)
    (p : CycleQ2SegreCech.Chart) :=
  HomogeneousLocalization.Away (surfaceGrade y) (basePivot y p)

def relativeProjectiveEquation (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) : RelativeProjectivePivot y p :=
  HomogeneousLocalization.Away.mk (surfaceGrade y)
    (relativePivot_homogeneous y p) 1 (relativeEquation y t p.1) (by
      simpa only [one_smul] using relativeEquation_homogeneous y t p.1)

theorem relativeProjectiveEquation_val_mul (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) :
    (relativeProjectiveEquation y t p).val *
      algebraMap _ (CoefficientPivot y p) (basePivot y p) =
        algebraMap _ (CoefficientPivot y p) (relativeEquation y t p.1) := by
  have hs := IsLocalization.mk'_spec (CoefficientPivot y p)
    (relativeEquation y t p.1)
    (CycleQ2GradedLocalizationProjection.powerDenominator (basePivot y p) 1)
  simpa only [relativeProjectiveEquation, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', CycleQ2GradedLocalizationProjection.powerDenominator,
    pow_one] using hs

theorem relativeProjectiveEquation_regular (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart)
    (hreg : IsSMulRegular (CoefficientPivot y p)
      (algebraMap _ (CoefficientPivot y p) (relativeEquation y t p.1))) :
    IsSMulRegular (RelativeProjectivePivot y p) (relativeProjectiveEquation y t p) := by
  apply CycleQ2GradedLocalizationProjection.isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  apply hreg.right_eq_zero_of_smul
  change algebraMap _ (CoefficientPivot y p) (relativeEquation y t p.1) * a = 0
  change (relativeProjectiveEquation y t p).val * a = 0 at ha
  rw [← relativeProjectiveEquation_val_mul]
  calc
    ((relativeProjectiveEquation y t p).val *
          algebraMap _ (CoefficientPivot y p) (basePivot y p)) * a =
        algebraMap _ (CoefficientPivot y p) (basePivot y p) *
          ((relativeProjectiveEquation y t p).val * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

def relativeSectionIdeal (y : ParameterIndex → S) (t : Fin 3 → ℂ) :
    Ideal (PointSurface y) :=
  Ideal.span (Set.range (relativeEquation y t))

theorem relativeSectionIdeal_homogeneous (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) :
    (relativeSectionIdeal y t).IsHomogeneous (surfaceGrade y) := by
  apply Ideal.homogeneous_span
  rintro a ⟨i, rfl⟩
  exact ⟨14, relativeEquation_homogeneous y t i⟩

abbrev RelativeCurveRing (y : ParameterIndex → S) (t : Fin 3 → ℂ) :=
  PointSurface y ⧸ relativeSectionIdeal y t

/-- Over the complex numbers this is the existing regular-section row. -/
theorem relativeEquation_complex (y : ParameterIndex → ℂ)
    (t : Fin 3 → ℂ) (i : Fin 3) :
    relativeEquation y t i = constantEquation y t i := by
  simp only [relativeEquation, relativeSectionPolynomial, map_sum, map_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  unfold constantEquation
  apply Finset.sum_congr rfl
  intro j _
  rw [basePivot_eq_quotient, Algebra.smul_def]
  rfl

theorem relativeProjectiveEquation_complex (y : ParameterIndex → ℂ)
    (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) :
    relativeProjectiveEquation y t p = constantProjectiveEquation y t p := by
  unfold relativeProjectiveEquation constantProjectiveEquation
  congr 1
  exact relativeEquation_complex y t p.1

theorem relative_matrix_specialization (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i j : Fin 3) :
    MvPolynomial.map (MvPolynomial.eval (fun k => algebraMap ℂ S (t k)))
      (pointMatrixPolynomial (sectionPoint y) i j) = pointMatrixPolynomial y i j := by
  rw [pointMatrixPolynomial_sectionPoint, MvPolynomial.map_map]
  have hc : (MvPolynomial.eval (fun k => algebraMap ℂ S (t k))).comp
      (C : S →+* SectionBase S) = RingHom.id S := by
    ext a
    simp
  rw [hc, MvPolynomial.map_id]

/-- The relative equations are the literal evaluation of the original
universal `M*T` equations, with one fixed complex vector. -/
theorem relativeSectionPolynomial_eq_specialization (y : ParameterIndex → S)
    (t : Fin 3 → ℂ) (i : Fin 3) :
    MvPolynomial.map (MvPolynomial.eval (fun j => algebraMap ℂ S (t j)))
      (genericSectionEquation y i) = relativeSectionPolynomial y t i := by
  simp only [genericSectionEquation, relativeSectionPolynomial, map_sum,
    map_mul, MvPolynomial.map_C, MvPolynomial.eval_X, relative_matrix_specialization]

theorem relativeSectionIdeal_eq_map (y : ParameterIndex → S) (t : Fin 3 → ℂ) :
    relativeSectionIdeal y t =
      (genericSectionIdeal y).map
        ((Ideal.Quotient.mk (pointEquations y)).comp
          (MvPolynomial.map (MvPolynomial.eval (fun j => algebraMap ℂ S (t j))))) := by
  rw [relativeSectionIdeal, genericSectionIdeal, Ideal.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨genericSectionEquation y i, ⟨i, rfl⟩, ?_⟩
    change Ideal.Quotient.mk (pointEquations y)
      (MvPolynomial.map (MvPolynomial.eval (fun j => algebraMap ℂ S (t j)))
        (genericSectionEquation y i)) = _
    rw [relativeSectionPolynomial_eq_specialization]
    rfl
  · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    change relativeEquation y t i = Ideal.Quotient.mk (pointEquations y)
      (MvPolynomial.map (MvPolynomial.eval (fun j => algebraMap ℂ S (t j)))
        (genericSectionEquation y i))
    rw [relativeSectionPolynomial_eq_specialization]
    rfl

/-- The actual matrix coefficients specialize along the retained seed
map; the geometric variables are unchanged. -/
theorem pointMatrixPolynomial_seed (i j : Fin 3) :
    MvPolynomial.map seedMap (pointMatrixPolynomial incidencePoint i j) =
      pointMatrixPolynomial (seedPoint (57 : ℂ) Complex.I) i j := by
  have h := congrArg (fun M => M i j)
    (map_incidenceMatrix seedMap (57 : ParameterAlgebra) (pointMatrix incidencePoint))
  simpa only [pointMatrixPolynomial, RingHom.mapMatrix_apply, map_ofNat,
    pointMatrix, seedMap_incidencePoint] using h

theorem relativeSectionPolynomial_seed (t : Fin 3 → ℂ) (i : Fin 3) :
    MvPolynomial.map seedMap (relativeSectionPolynomial incidencePoint t i) =
      relativeSectionPolynomial (seedPoint (57 : ℂ) Complex.I) t i := by
  simp only [relativeSectionPolynomial, map_sum, map_mul, MvPolynomial.map_C,
    CycleQ2IncidenceSeedFiber.seedMap_complex, pointMatrixPolynomial_seed,
    Algebra.algebraMap_self, RingHom.id_apply]

#print axioms relativeSectionIdeal_homogeneous
#print axioms relativeEquation_localize_row
#print axioms relativeProjectiveEquation_regular
#print axioms relativeEquation_complex
#print axioms relativeSectionIdeal_eq_map
#print axioms pointMatrixPolynomial_seed
#print axioms relativeSectionPolynomial_seed

end CycleQ2RelativeConstantSection
end
