import Proposal.GeometricSectionUnitCech

/-!
# Emptiness forces the original row equations to generate the unit ideal

This uses the existing specializedCurve and its actual projective equation
units. The target algebra is arbitrary; only the original matrix entries
must span the unit ideal there. A maximal-ideal quotient selects a unit
pivot, where the existing projective equation would be both zero and a unit.

Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2EmptySectionRows

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2GeometricIncidenceProj
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveNonemptyCriterion
  CycleQ2SectionUnitCech

variable (y : ParameterIndex → ℂ) (t : Fin 3 → ℂ)
variable {R : Type} [CommRing R] [Algebra ℂ R]

/-- No point of an auxiliary scheme is assumed. A hypothetical proper row
ideal itself supplies the prime used in the argument. -/
theorem row_span_of_isEmpty [IsEmpty (specializedCurve y t)]
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (f : PointSurface y →ₐ[ℂ] R)
    (hentries : Ideal.span (Set.range
      (fun p : CycleQ2SegreCech.Chart => f (basePivot y p))) = ⊤) :
    Ideal.span (Set.range (fun a : Fin 3 => f (constantEquation y t a))) = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span (Set.range (fun a : Fin 3 => f (constantEquation y t a)))) hproper
  letI : m.IsMaximal := hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hpivot : ∃ p : CycleQ2SegreCech.Chart, f (basePivot y p) ∉ m := by
    by_contra h
    have hall : ∀ p : CycleQ2SegreCech.Chart, f (basePivot y p) ∈ m := by
      intro p
      by_contra hp
      exact h ⟨p, hp⟩
    have hspan : Ideal.span (Set.range
        (fun p : CycleQ2SegreCech.Chart => f (basePivot y p))) ≤ m := by
      apply Ideal.span_le.mpr
      rintro _ ⟨p, rfl⟩
      exact hall p
    have htop : (⊤ : Ideal R) ≤ m := hentries ▸ hspan
    exact (inferInstance : m.IsPrime).one_notMem (htop (show (1 : R) ∈ (⊤ : Ideal R) from
      Submodule.mem_top))
  obtain ⟨p, hp⟩ := hpivot
  let g : PointSurface y →ₐ[ℂ] (R ⧸ m) := (Ideal.Quotient.mkₐ ℂ m).comp f
  have hp0 : g (basePivot y p) ≠ 0 := by
    intro hz
    exact hp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hv : IsUnit (g (basePivot y p)) := isUnit_iff_ne_zero.mpr hp0
  have hr : g (constantEquation y t p.1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hle (Ideal.subset_span ⟨p.1, rfl⟩)
  have heq := (equation_isUnit_of_isEmpty y t he hu p).map
    (projectiveToOverlap y g p hv.unit hv.unit_spec)
  rw [projectiveToOverlap_equation, hr, mul_zero] at heq
  exact not_isUnit_zero heq

/-- Rows spanning one determine a scalar by its products with those rows. -/
theorem scalar_eq_of_row_products {S : Type*} [CommRing S]
    (v : Fin 3 → S) (hspan : Ideal.span (Set.range v) = ⊤)
    (a b : S) (h : ∀ i, v i * a = v i * b) : a = b := by
  classical
  have hmem : (1 : S) ∈ Ideal.span (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  calc
    a = (∑ i, c i * v i) * a := by rw [hc, one_mul]
    _ = ∑ i, c i * (v i * a) := by simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ i, c i * (v i * b) := by simp only [h]
    _ = (∑ i, c i * v i) * b := by simp only [Finset.sum_mul, mul_assoc]
    _ = b := by rw [hc, one_mul]

end CycleQ2EmptySectionRows

end

#print axioms CycleQ2EmptySectionRows.row_span_of_isEmpty
#print axioms CycleQ2EmptySectionRows.scalar_eq_of_row_products
