import Proposal.GeometricIncidenceChartMinor
import Proposal.GeometricIncidenceChartSeedFiber
import Proposal.GeometricSeedSurfaceGradient

/-!
# The original seed Jacobian minors cover every actual incidence chart

Status: source-only proof draft. No elaboration or kernel replay was run.

A prime of an actual shifted dehomogenized chart pulls back to a prime
of the original polynomial ring containing the literal seed equations.
The chosen weight-one coordinate maps to one, so the pulled-back prime
is relevant. The existing seed gradient cover then supplies a nonzero
minor, whose image is exactly the normalized minor of this chart.

This component proves only the actual seed chart cover. The geometric
strategy is due to Ben Diamond and the collaborators cited in solution.md.
Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSeedChartMinorCover

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceChartSeedFiber

/-- The ordered relative F,h minor at the literal seed is the original
minor appearing in the verified seed gradient cover. -/
theorem literal_surfaceMinor (j k : Fin 5) :
    CycleQ2IncidenceChartMinor.surfaceMinor (seedPoint (57 : ℂ) Complex.I) j k =
      CycleQ2SeedSurfaceGradient.surfaceMinor j k := by
  rw [CycleQ2IncidenceChartMinor.surfaceMinor_eq,
    literal_pointEquationF, literal_pointEquationH]
  rfl

/-- Every prime of each actual seed chart misses a normalized Jacobian
minor with two distinct geometric columns. -/
theorem seed_prime_normalizedMinor_cover (i : Fin 4)
    (P : Ideal (DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i)) [P.IsPrime] :
    ∃ j k : Fin 5, j ≠ k ∧
      normalizedMinor (seedPoint (57 : ℂ) Complex.I) i j k ∉ P := by
  let φ : Poly ℂ →+* DehomogenizedRing (seedPoint (57 : ℂ) Complex.I) i :=
    (surfaceToDehomogenized (seedPoint (57 : ℂ) Complex.I) i).comp
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I))
  let Q : Ideal (Poly ℂ) := P.comap φ
  letI : Q.IsPrime := Ideal.IsPrime.comap φ
  have hF : smoothF (57 : ℂ) Complex.I ∈ Q := by
    change surfaceToDehomogenized (seedPoint (57 : ℂ) Complex.I) i
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
        (smoothF (57 : ℂ) Complex.I)) ∈ P
    rw [← literal_pointEquationF]
    have hz : surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
        (pointEquationF (seedPoint (57 : ℂ) Complex.I)) = 0 :=
      surfaceQuotient_equation (seedPoint (57 : ℂ) Complex.I) 0
    rw [hz, map_zero]
    exact P.zero_mem
  have hH : smoothH Complex.I ∈ Q := by
    change surfaceToDehomogenized (seedPoint (57 : ℂ) Complex.I) i
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (smoothH Complex.I)) ∈ P
    rw [← literal_pointEquationH]
    have hz : surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
        (pointEquationH (seedPoint (57 : ℂ) Complex.I)) = 0 :=
      surfaceQuotient_equation (seedPoint (57 : ℂ) Complex.I) 1
    rw [hz, map_zero]
    exact P.zero_mem
  have hx : ∃ a : Fin 5, (X a : Poly ℂ) ∉ Q := by
    refine ⟨i.castSucc, ?_⟩
    intro h
    change surfaceToDehomogenized (seedPoint (57 : ℂ) Complex.I) i
      (surfaceQuotient (seedPoint (57 : ℂ) Complex.I) (X i.castSucc)) ∈ P at h
    rw [surfaceToDehomogenized_self] at h
    exact Ideal.notMem_of_isUnit P isUnit_one h
  obtain ⟨j, k, hjk⟩ := CycleQ2SeedSurfaceGradient.prime_minor_cover Q hF hH hx
  have hne : j ≠ k := by
    intro h
    subst k
    apply hjk
    simpa only [CycleQ2SeedSurfaceGradient.surfaceMinor, sub_self] using Q.zero_mem
  refine ⟨j, k, hne, ?_⟩
  intro h
  apply hjk
  change surfaceToDehomogenized (seedPoint (57 : ℂ) Complex.I) i
    (surfaceQuotient (seedPoint (57 : ℂ) Complex.I)
      (CycleQ2SeedSurfaceGradient.surfaceMinor j k)) ∈ P
  rw [surfaceToDehomogenized_surfaceQuotient, ← literal_surfaceMinor]
  exact h

end CycleQ2IncidenceSeedChartMinorCover

end

#print axioms CycleQ2IncidenceSeedChartMinorCover.literal_surfaceMinor
#print axioms CycleQ2IncidenceSeedChartMinorCover.seed_prime_normalizedMinor_cover
