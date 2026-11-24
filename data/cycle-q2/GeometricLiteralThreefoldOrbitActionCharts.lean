import Proposal.GeometricLiteralThreefoldOrbitAction
import Proposal.GeometricLiteralAmbientCharts

/-! The normalized polynomial substitution on each weight-one chart of the
fixed threefold. It acts triangularly on the shifted weight-two variable.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitAction

open MvPolynomial CycleQ2SeedCyclicAction CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientCylinder

def baseScale (z : ℂ) (i : Fin 4) : ℂ := (char z i.castSucc)⁻¹

def linearScale (z : ℂ) (i k : Fin 4) : ℂ := char z k.castSucc * baseScale z i

theorem char_ne_zero (z : ℂ) (hz : z^3 = 1) (j : Fin 5) : char z j ≠ 0 := by
  intro h
  simpa [h] using char_cube z hz j

theorem baseScale_cube (z : ℂ) (hz : z^3 = 1) (i : Fin 4) : baseScale z i ^ 3 = 1 := by
  rw [baseScale, inv_pow, char_cube z hz, inv_one]

theorem baseScale_six (z : ℂ) (hz : z^3 = 1) (i : Fin 4) : baseScale z i ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3*2 by decide, pow_mul, baseScale_cube z hz, one_pow]

def chartPolynomialAction (z : ℂ) (i : Fin 4) : ChartPolynomial ℂ →ₐ[ℂ] ChartPolynomial ℂ :=
  aeval fun j => match j with
    | some k => C (linearScale z i (i.succAbove k)) * X (some k)
    | none => C (baseScale z i ^ 2) * X none +
        C (linearScale z i 2 ^ 2 - baseScale z i ^ 2) * linearCoordinate i 2 ^ 2

theorem chartPolynomialAction_normal (z : ℂ) (i : Fin 4) :
    chartPolynomialAction z i (X none) = C (baseScale z i ^ 2) * X none +
      C (linearScale z i 2 ^ 2 - baseScale z i ^ 2) * linearCoordinate i 2 ^ 2 :=
  aeval_X _ _

theorem chartPolynomialAction_linear (z : ℂ) (hz : z^3 = 1) (i k : Fin 4) :
    chartPolynomialAction z i (linearCoordinate i k) = C (linearScale z i k) * linearCoordinate i k := by
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · simp [linearScale, baseScale, char_ne_zero z hz]
  · simp only [linearCoordinate_succAbove, chartPolynomialAction, aeval_X]

private theorem dehomogenize_C (i : Fin 4) (a : ℂ) : dehomogenize i (C a) = C a := aeval_C _ _

theorem chartPolynomialAction_homogeneous (z : ℂ) (hz : z^3 = 1) (i : Fin 4)
    {n : ℕ} {p : MvPolynomial (Fin 5) ℂ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartPolynomialAction z i (dehomogenize i p) =
      C (baseScale z i ^ n) * dehomogenize i (polynomialAction z p) := by
  let v : Fin 5 → ChartPolynomial ℂ := fun j => dehomogenize i (polynomialAction z (X j))
  let c : ChartPolynomial ℂ := C (baseScale z i)
  have h : (chartPolynomialAction z i).comp (dehomogenize i) = aeval (fun j => c^geometricWeight j * v j) := by
    apply MvPolynomial.algHom_ext
    intro j
    induction j using Fin.lastCases with
    | cast j =>
      simp only [AlgHom.comp_apply, dehomogenize_castSucc, chartPolynomialAction_linear z hz,
        aeval_X, weight_castSucc, pow_one, v, action_X, map_mul, dehomogenize_C]
      rw [linearScale, map_mul]
      ring
    | last =>
      simp only [AlgHom.comp_apply, dehomogenize_last, map_sub, map_pow,
        chartPolynomialAction_linear z hz, chartPolynomialAction_normal, aeval_X,
        v, action_X, map_mul, dehomogenize_C]
      change _ = C (baseScale z i) ^ 2 * (C 1 * (X none - linearCoordinate i 2 ^ 2))
      simp only [map_one, one_mul, map_sub, map_pow]
      ring
  have hv : (dehomogenize i).comp (polynomialAction z) = aeval v := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X]
  have he := weighted_homogeneous_eval_scale C v c p n hp
  change ((chartPolynomialAction z i).comp (dehomogenize i)) p =
    C (baseScale z i ^ n) * ((dehomogenize i).comp (polynomialAction z)) p
  rw [h, hv, map_pow]
  exact he

theorem chartPolynomialAction_seedF (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    chartPolynomialAction z i (seedF i) = seedF i := by
  rw [seedF, chartPolynomialAction_homogeneous z hz i (pointEquationF_homogeneous _),
    equation_fixed z hz, baseScale_six z hz, map_one, one_mul]

def chartAction (z : ℂ) (hz : z^3 = 1) (i : Fin 4) : T i →ₐ[ℂ] T i :=
  Ideal.quotientMapₐ (fixedIdeal i) (chartPolynomialAction z i) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change chartPolynomialAction z i (seedF i) ∈ fixedIdeal i
    rw [chartPolynomialAction_seedF z hz i]
    exact Ideal.subset_span (Set.mem_singleton _))

theorem chartAction_mk (z : ℂ) (hz : z^3 = 1) (i : Fin 4) (p : ChartPolynomial ℂ) :
    chartAction z hz i (Ideal.Quotient.mk (fixedIdeal i) p) =
      Ideal.Quotient.mk (fixedIdeal i) (chartPolynomialAction z i p) := rfl

end CycleQ2LiteralThreefoldOrbitAction
end

#print axioms CycleQ2LiteralThreefoldOrbitAction.chartPolynomialAction_homogeneous
#print axioms CycleQ2LiteralThreefoldOrbitAction.chartPolynomialAction_seedF
