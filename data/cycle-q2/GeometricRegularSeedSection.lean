import Proposal.GeometricSimultaneousRegularSection
import Proposal.GeometricUniversalCurveCartier
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# A regular constant specialization of the original seed section equations

Status: source-only proof draft, 14 November 2026. No Lean elaboration or
independent kernel replay has been run for this module.

One nonzero complex coefficient vector is chosen simultaneously for the
nine original matrix-pivot rings. Its row equations are nonzerodivisors
in those ordinary localizations. Dividing by the degree-fourteen pivot
then gives regular equations in the actual degree-zero projective rings.
The polynomial-specialization identity retains the original `M*T` family.

This is a regularity statement at a fixed coefficient point, including
the literal seed. It does not assert a nonempty divisor, flatness over
the incidence parameters, or an Abel--Jacobi or residue comparison.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RegularSeedSection

open CycleQ2IncidencePolynomialJacobianBinding

open MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2UniversalCurveCartier CycleQ2GradedLocalizationProjection

variable (y : ParameterIndex → ℂ)

local instance pointCommRing : CommRing (PointSurface y) := inferInstance

theorem basePivot_eq_quotient (p : CycleQ2SegreCech.Chart) :
    basePivot y p = Ideal.Quotient.mk (pointEquations y)
      (pointMatrixPolynomial y p.1 p.2) := by
  rw [pointMatrixPolynomial_eq]
  rfl

theorem basePivot_homogeneous (p : CycleQ2SegreCech.Chart) :
    basePivot y p ∈ surfaceGrade y 14 := by
  rw [basePivot_eq_quotient]
  exact ⟨_, pointMatrixPolynomial_homogeneous y p.1 p.2, rfl⟩

/-- The original row of `M*T` after a constant complex specialization. -/
def constantEquation (t : Fin 3 → ℂ) (i : Fin 3) : PointSurface y :=
  ∑ j, t j • basePivot y (i, j)

theorem constantEquation_homogeneous (t : Fin 3 → ℂ) (i : Fin 3) :
    constantEquation y t i ∈ surfaceGrade y 14 := by
  apply (surfaceGrade y 14).sum_mem
  intro j _
  exact (surfaceGrade y 14).smul_mem (t j) (basePivot_homogeneous y (i, j))

theorem pointMatrixPolynomial_specialize (t : Fin 3 → ℂ) (i j : Fin 3) :
    MvPolynomial.map (MvPolynomial.eval t)
      (pointMatrixPolynomial (sectionPoint y) i j) =
        pointMatrixPolynomial y i j := by
  rw [pointMatrixPolynomial_sectionPoint, MvPolynomial.map_map]
  have hc : (MvPolynomial.eval t).comp (C : ℂ →+* SectionBase ℂ) =
      RingHom.id ℂ := by
    ext a
    simp
  rw [hc, MvPolynomial.map_id]

/-- This row is the specialization of the existing universal polynomial,
not an independently chosen equation on the surface. -/
theorem constantEquation_eq_specialization (t : Fin 3 → ℂ) (i : Fin 3) :
    Ideal.Quotient.mk (pointEquations y)
      (MvPolynomial.map (MvPolynomial.eval t) (genericSectionEquation y i)) =
        constantEquation y t i := by
  simp only [genericSectionEquation, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.eval_X, pointMatrixPolynomial_specialize]
  change (∑ j, Ideal.Quotient.mk (pointEquations y) (C (t j)) *
    Ideal.Quotient.mk (pointEquations y) (pointMatrixPolynomial y i j)) = _
  unfold constantEquation
  apply Finset.sum_congr rfl
  intro j _
  rw [basePivot_eq_quotient, Algebra.smul_def]
  rfl

theorem constantEquation_localize (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) :
    algebraMap (PointSurface y) (CoefficientPivot y p) (constantEquation y t p.1) =
      ∑ j, t j • localizedMatrix y p p.1 j := by
  change (IsScalarTower.toAlgHom ℂ (PointSurface y) (CoefficientPivot y p))
      (∑ j, t j • basePivot y (p.1, j)) = _
  simp only [map_sum, map_smul]
  rfl

/-- One coefficient vector works at once on all nine pivot localizations.
Empty pivot charts are permitted; no integrality assumption is used. -/
theorem exists_regular_ordinary_equations :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (CoefficientPivot y p)
          (algebraMap (PointSurface y) (CoefficientPivot y p)
            (constantEquation y t p.1)) := by
  obtain ⟨t, ht, hreg⟩ :=
    CycleQ2SimultaneousRegularSection.exists_nonzero_simultaneous_regular
      (k := ℂ) (fun p : CycleQ2SegreCech.Chart => CoefficientPivot y p)
      (fun p j => localizedMatrix y p p.1 j)
      (fun p => ⟨p.2, localizedMatrix_pivot_isUnit y p⟩)
  refine ⟨t, ht, fun p => ?_⟩
  rw [constantEquation_localize]
  exact hreg p

abbrev ConstantProjectivePivot (p : CycleQ2SegreCech.Chart) :=
  HomogeneousLocalization.Away (surfaceGrade y) (basePivot y p)

/-- The actual degree-zero fraction `(M*t)i / Mij` on the original
projective surface, after the section parameters have become constants. -/
def constantProjectiveEquation (t : Fin 3 → ℂ) (p : CycleQ2SegreCech.Chart) :
    ConstantProjectivePivot y p :=
  HomogeneousLocalization.Away.mk (surfaceGrade y)
    (basePivot_homogeneous y p) 1 (constantEquation y t p.1) (by
      simpa only [one_smul] using constantEquation_homogeneous y t p.1)

theorem constantProjectiveEquation_val_mul (t : Fin 3 → ℂ)
    (p : CycleQ2SegreCech.Chart) :
    (constantProjectiveEquation y t p).val *
      algebraMap _ (CoefficientPivot y p) (basePivot y p) =
        algebraMap _ (CoefficientPivot y p) (constantEquation y t p.1) := by
  have hs := IsLocalization.mk'_spec (CoefficientPivot y p)
    (constantEquation y t p.1) (powerDenominator (basePivot y p) 1)
  simpa only [constantProjectiveEquation, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', powerDenominator, pow_one] using hs

theorem constantProjectiveEquation_regular (t : Fin 3 → ℂ)
    (p : CycleQ2SegreCech.Chart)
    (hreg : IsSMulRegular (CoefficientPivot y p)
      (algebraMap _ (CoefficientPivot y p) (constantEquation y t p.1))) :
    IsSMulRegular (ConstantProjectivePivot y p) (constantProjectiveEquation y t p) := by
  apply isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  apply hreg.right_eq_zero_of_smul
  change algebraMap _ (CoefficientPivot y p) (constantEquation y t p.1) * a = 0
  change (constantProjectiveEquation y t p).val * a = 0 at ha
  rw [← constantProjectiveEquation_val_mul]
  calc
    ((constantProjectiveEquation y t p).val *
          algebraMap _ (CoefficientPivot y p) (basePivot y p)) * a =
        algebraMap _ (CoefficientPivot y p) (basePivot y p) *
          ((constantProjectiveEquation y t p).val * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

/-- Regularity survives the actual constant specialization and holds in
the degree-zero projective chart rings, with one shared nonzero vector. -/
theorem exists_regular_projective_equations :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (ConstantProjectivePivot y p) (constantProjectiveEquation y t p) := by
  obtain ⟨t, ht, hreg⟩ := exists_regular_ordinary_equations y
  exact ⟨t, ht, fun p => constantProjectiveEquation_regular y t p (hreg p)⟩

/-- The literal original seed needs no regular-section premise from a
caller. This does not assert flatness or nonempty zero loci. -/
theorem exists_seed_regular_equations :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      ∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular
          (ConstantProjectivePivot (seedPoint (57 : ℂ) Complex.I) p)
          (constantProjectiveEquation (seedPoint (57 : ℂ) Complex.I) t p) :=
  exists_regular_projective_equations (seedPoint (57 : ℂ) Complex.I)

#print axioms exists_regular_ordinary_equations
#print axioms constantEquation_eq_specialization
#print axioms exists_seed_regular_equations

end CycleQ2RegularSeedSection
end
