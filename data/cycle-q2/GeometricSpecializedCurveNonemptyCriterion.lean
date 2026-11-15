import Proposal.GeometricSpecializedProjectiveCurve

/-!
# A nonunit original projective equation gives a point of the original curve

The exact kernel of the actual homogeneous-localization map is the ideal
of the existing fixed-section equation. If that equation is not a unit,
the target chart ring is nontrivial. A prime of that ring gives a point
of the original `specializedCurve` through its actual Proj chart map.

Consequently, if the original curve is empty, every one of its existing
projective equations is a unit. This gives local units for a subsequent
transition-cocycle argument. No nonunit equation is supplied here, so the
nonemptiness of the chosen regular seed curve remains unresolved.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SpecializedCurveNonemptyCriterion

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceGenericPointSemantics CycleQ2GeometricIncidenceProj
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2SpecializedSectionIdeal CycleQ2SpecializedProjectiveCurve

variable (y : ParameterIndex → ℂ) (t : Fin 3 → ℂ)
variable (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
variable (hu : IsUnit (aeval y (leadingProduct ℂ)))

/-- The target of the actual chart quotient is nonzero as soon as its
actual principal kernel has a nonunit generator. -/
theorem nonempty_of_equation_not_isUnit (p : CycleQ2SegreCech.Chart)
    (hn : ¬ IsUnit (constantProjectiveEquation y t p)) :
    Nonempty (specializedCurve y t) := by
  let B := Away (specializedCurveGrade y t)
    (specializedCurveRingMap y t (basePivot y p))
  have h10 : (1 : B) ≠ 0 := by
    intro hzero
    apply hn
    apply Ideal.span_singleton_eq_top.mp
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← specializedAwayMap_ker_principal y t he hu p]
    change Away.map (specializedCurveRingMap y t) (basePivot y p) 1 = 0
    simpa only [map_one] using hzero
  letI : Nontrivial B := ⟨1, 0, h10⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum B))
  exact ⟨(Proj.awayι (specializedCurveGrade y t)
    (specializedCurveRingMap y t (basePivot y p))
    ((specializedCurveRingMap y t).2 (basePivot_homogeneous y p))
    (by decide)) x⟩

theorem equation_isUnit_of_isEmpty [IsEmpty (specializedCurve y t)]
    (p : CycleQ2SegreCech.Chart) : IsUnit (constantProjectiveEquation y t p) := by
  classical
  by_contra hn
  obtain ⟨x⟩ := nonempty_of_equation_not_isUnit y t he hu p hn
  exact isEmptyElim x

/-- These witnesses are obtained from actual emptiness, not postulated. -/
def emptyEquationUnit [IsEmpty (specializedCurve y t)]
    (p : CycleQ2SegreCech.Chart) : (ConstantProjectivePivot y p)ˣ :=
  Classical.choose (equation_isUnit_of_isEmpty y t he hu p)

@[simp] theorem emptyEquationUnit_val [IsEmpty (specializedCurve y t)]
    (p : CycleQ2SegreCech.Chart) :
    (emptyEquationUnit y t he hu p : ConstantProjectivePivot y p) =
      constantProjectiveEquation y t p :=
  Classical.choose_spec (equation_isUnit_of_isEmpty y t he hu p)

theorem seed_nonempty_of_equation_not_isUnit (t : Fin 3 → ℂ)
    (p : CycleQ2SegreCech.Chart)
    (hn : ¬ IsUnit (constantProjectiveEquation (seedPoint (57 : ℂ) Complex.I) t p)) :
    Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) :=
  nonempty_of_equation_not_isUnit (seedPoint (57 : ℂ) Complex.I) t
    seed_original_equations seed_leading_unit p hn

#print axioms nonempty_of_equation_not_isUnit
#print axioms equation_isUnit_of_isEmpty
#print axioms seed_nonempty_of_equation_not_isUnit

end CycleQ2SpecializedCurveNonemptyCriterion
end
