import Proposal.GeometricRelativeConstantSection
import Mathlib.RingTheory.FiniteType

/-!
# One complex section regular on the incidence family and its seed

The finite associated-prime avoidance argument is applied to the disjoint
union of the nine relative pivot rings and the nine literal seed pivot
rings. This chooses one nonzero complex vector whose equations are
regular in both sets of actual rings. The degree-zero equations inherit
regularity by the already proved numerator identity and injective
homogeneous-localization inclusion.

The incidence parameter algebra is Noetherian because it is finite type
over the finite polynomial trace ring. No geometric regularity premise
is supplied for the final simultaneous choice. This is regularity on the
total space and on the specified seed; flatness of the quotient over the
parameter base and nonemptiness of its projective zero locus remain open.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeRegularSection

open CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceEtaleParameter
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2RelativeConstantSection

section TwoCoefficientPoints

variable {S T : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
  [IsNoetherianRing S] [IsNoetherianRing T]

/-- Both coefficient points use one and the same complex vector. No
relationship between their coefficient rings is needed for avoidance. -/
theorem exists_pair_regular (y : ParameterIndex → S) (z : ParameterIndex → T) :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      (∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (RelativeProjectivePivot y p) (relativeProjectiveEquation y t p)) ∧
      (∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (RelativeProjectivePivot z p) (relativeProjectiveEquation z t p)) := by
  let Index := Sum CycleQ2SegreCech.Chart CycleQ2SegreCech.Chart
  let R : Index → Type := fun a =>
    match a with
    | .inl p => CoefficientPivot y p
    | .inr p => CoefficientPivot z p
  letI : ∀ a, CommRing (R a) := fun a => by
    cases a <;> dsimp only [R] <;> infer_instance
  letI : ∀ a, Algebra ℂ (R a) := fun a => by
    cases a <;> dsimp only [R] <;> infer_instance
  letI : ∀ a, IsNoetherianRing (R a) := fun a => by
    cases a <;> dsimp only [R] <;> infer_instance
  let c : (a : Index) → Fin 3 → R a := fun a =>
    match a with
    | .inl p => fun j => localizedMatrix y p p.1 j
    | .inr p => fun j => localizedMatrix z p p.1 j
  have hc (a : Index) : ∃ j, IsUnit (c a j) := by
    cases a with
    | inl p => exact ⟨p.2, localizedMatrix_pivot_isUnit y p⟩
    | inr p => exact ⟨p.2, localizedMatrix_pivot_isUnit z p⟩
  obtain ⟨t, ht, hreg⟩ :=
    CycleQ2SimultaneousRegularSection.exists_nonzero_simultaneous_regular
      (k := ℂ) R c hc
  refine ⟨t, ht, ?_, ?_⟩
  · intro p
    apply relativeProjectiveEquation_regular y t p
    rw [relativeEquation_localize_row]
    exact hreg (Sum.inl p)
  · intro p
    apply relativeProjectiveEquation_regular z t p
    rw [relativeEquation_localize_row]
    exact hreg (Sum.inr p)

end TwoCoefficientPoints

/-- The actual parameter algebra is finite type over its original
Noetherian trace-polynomial coefficient ring. -/
theorem parameter_noetherian : IsNoetherianRing ParameterAlgebra := by
  letI : IsNoetherianRing CycleQ2IncidenceTraceFamily.TraceRing := inferInstance
  exact Algebra.FiniteType.isNoetherianRing
    CycleQ2IncidenceTraceFamily.TraceRing ParameterAlgebra

/-- A fixed nonzero complex section is regular on the actual relative
incidence surface and on its literal original seed at the same time. -/
theorem exists_incidence_and_seed_regular :
    ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
      (∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (RelativeProjectivePivot incidencePoint p)
          (relativeProjectiveEquation incidencePoint t p)) ∧
      (∀ p : CycleQ2SegreCech.Chart,
        IsSMulRegular (ConstantProjectivePivot (seedPoint (57 : ℂ) Complex.I) p)
          (constantProjectiveEquation (seedPoint (57 : ℂ) Complex.I) t p)) := by
  letI := parameter_noetherian
  obtain ⟨t, ht, hrelative, hseed⟩ :=
    exists_pair_regular incidencePoint (seedPoint (57 : ℂ) Complex.I)
  refine ⟨t, ht, hrelative, fun p => ?_⟩
  rw [← relativeProjectiveEquation_complex]
  exact hseed p

#print axioms exists_pair_regular
#print axioms parameter_noetherian
#print axioms exists_incidence_and_seed_regular

end CycleQ2RelativeRegularSection
end
