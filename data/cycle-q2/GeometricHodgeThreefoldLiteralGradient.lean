import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricHodgeEuler

/-!
# The Jacobian opens cover the original normalized incidence sextic

The previously checked fixed-sextic Jacobian certificate applies after
identifying the defining polynomials. Pull back any maximal ideal of the
dehomogenized chart. The original certificate and the Euler equation
supply a retained affine derivative outside this ideal.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefoldIncidence

open MvPolynomial CycleQ2IncidenceEquations CycleQ2IncidenceNormalForm CycleQ2GeometricHodgeThreefold
  CycleQ2HodgeEuler CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCylinder

theorem literal_equation : equation literalEval = smoothF (57 : ℂ) Complex.I :=
  (equation_eq point).trans CycleQ2IncidenceChartSeedFiber.literal_pointEquationF

theorem literal_chartGradient_span (i : Fin 4) :
    Ideal.span (Set.range (fun j : Fin 4 => chartMap literalEval i (pderiv j (F literalEval i)))) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let : m.IsMaximal := hm
  let ρ := (chartMap literalEval i).toRingHom.comp (dehom (R := ℂ) i).toRingHom
  let J := m.comap ρ
  have hi : X i.castSucc - 1 ∈ J := by
    change ρ (X i.castSucc - 1) ∈ m
    simp [ρ]
  have hF : smoothF (57 : ℂ) Complex.I ∈ J := by
    rw [← literal_equation]
    change chartMap literalEval i (F literalEval i) ∈ m
    rw [chartMap_F]
    exact m.zero_mem
  haveI : J.IsPrime := inferInstanceAs (m.comap ρ).IsPrime
  obtain ⟨j, hj⟩ := literal_exists_other_derivative 57 i J hF hi (literal_jacobian_cover J i hi hF)
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq j.property
  apply hj
  rw [← literal_equation, ← ha]
  change conePartial literalEval i (i.castSucc.succAbove a) ∈ m
  rw [partial_succAbove]
  exact hle (Ideal.subset_span (Set.mem_range_self a))

end CycleQ2GeometricHodgeThreefoldIncidence
end

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.literal_chartGradient_span
