import Proposal.GeometricHodgeEuler
import Mathlib.Tactic.Module

/-!
# The cotangent change of a weight-one projective anchor

For the weights one and two, changing the affine anchor by a unit scales
coordinate and coefficient by inverse powers. The discrepancy of the
resulting ordinary differential is exactly the weighted radial coefficient
multiplied by dlog of the anchor. It vanishes on the actual Euler kernel.
This is a chart identity; no global cotangent cohomology assertion is made.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeCotangentEulerTransition

variable {K S M : Type} [CommRing K] [CommRing S] [Algebra K S]
  [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
  (D : Derivation K S M) (u : Sˣ)

private theorem normalized_one (a x : S) :
    ((u : S) * a) • D ((↑u⁻¹ : S) * x) =
      a • D x - (a * x * (↑u⁻¹ : S)) • D (u : S) := by
  have hu : (u : S) * (↑u⁻¹ : S) = 1 := by simp
  have hd : D (↑u⁻¹ : S) = -((↑u⁻¹ : S)^2) • D (u : S) :=
    D.leibniz_of_mul_eq_one (by simp)
  have h1 : ((u : S) * a) * (↑u⁻¹ : S) = a := by
    calc
      _ = a * ((u : S) * (↑u⁻¹ : S)) := by ring
      _ = a := by rw [hu, mul_one]
  have h2 : ((u : S) * a) * x * (↑u⁻¹ : S)^2 = a*x*(↑u⁻¹ : S) := by
    calc
      _ = ((u : S) * (↑u⁻¹ : S)) * (a*x*(↑u⁻¹ : S)) := by ring
      _ = _ := by rw [hu, one_mul]
  calc
    _ = (((u : S) * a) * (↑u⁻¹ : S)) • D x -
        (((u : S) * a) * x * (↑u⁻¹ : S)^2) • D (u : S) := by
      rw [D.leibniz, hd]
      module
    _ = _ := by rw [h1,h2]

private theorem normalized_two (a x : S) :
    ((u : S)^2 * a) • D ((↑u⁻¹ : S)^2 * x) =
      a • D x - ((2:S) * a * x * (↑u⁻¹ : S)) • D (u : S) := by
  have hu : (u : S) * (↑u⁻¹ : S) = 1 := by simp
  have h1 : (u : S)^2*a = (u : S)*((u:S)*a) := by ring
  have h2 : (↑u⁻¹ : S)^2*x = (↑u⁻¹ : S)*((↑u⁻¹ : S)*x) := by ring
  have hc : ((u:S)*a)*((↑u⁻¹:S)*x)*(↑u⁻¹:S) = a*x*(↑u⁻¹:S) := by
    calc
      _ = ((u:S)*(↑u⁻¹:S))*(a*x*(↑u⁻¹:S)) := by ring
      _ = _ := by rw [hu,one_mul]
  rw [h1,h2,normalized_one D u ((u:S)*a) ((↑u⁻¹:S)*x), normalized_one D u a x,hc]
  module

theorem normalized_term (n : ℕ) (hn : n = 1 ∨ n = 2) (a x : S) :
    ((u:S)^n*a) • D ((↑u⁻¹:S)^n*x) =
      a • D x - ((n:S)*a*x*(↑u⁻¹:S)) • D (u:S) := by
  rcases hn with rfl | rfl
  · simpa only [pow_one, Nat.cast_one, one_mul] using normalized_one D u a x
  · exact normalized_two D u a x

variable {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀ i, w i = 1 ∨ w i = 2)
  (x a : ι → S)

include hw in
/-- The correction is the weighted Euler coefficient, with its original factor two. -/
theorem chart_change :
    (∑ i, ((u:S)^(w i)*a i) • D ((↑u⁻¹:S)^(w i)*x i)) =
      (∑ i, a i • D (x i)) -
        ((∑ i, (w i:S)*a i*x i)*(↑u⁻¹:S)) • D (u:S) := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => normalized_term D u (w i) (hw i) (a i) (x i))
  simpa only [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_mul] using h

include hw in
/-- The ambient differential of a radial-zero homogeneous tuple is independent
of the chosen weight-one anchor on every actual unit overlap. -/
theorem basic_invariance (h : ∑ i, (w i:S)*a i*x i = 0) :
    (∑ i, ((u:S)^(w i)*a i) • D ((↑u⁻¹:S)^(w i)*x i)) =
      ∑ i, a i • D (x i) := by
  rw [chart_change D u w hw x a, h, zero_mul, zero_smul, sub_zero]

/-- The original weighted coordinates have the required four linear slots and
one quadratic slot, so the same formula applies to their cotangent tuples. -/
theorem original_weights (x a : Fin 5 → S)
    (h : ∑ i, (CycleQ2GeometricIncidenceProj.geometricWeight i:S)*a i*x i = 0) :
    (∑ i, ((u:S)^(CycleQ2GeometricIncidenceProj.geometricWeight i)*a i) •
      D ((↑u⁻¹:S)^(CycleQ2GeometricIncidenceProj.geometricWeight i)*x i)) =
      ∑ i, a i • D (x i) :=
  basic_invariance D u CycleQ2GeometricIncidenceProj.geometricWeight
    (by intro i; fin_cases i <;> simp [CycleQ2GeometricIncidenceProj.geometricWeight]) x a h

end CycleQ2HodgeCotangentEulerTransition
end

#print axioms CycleQ2HodgeCotangentEulerTransition.chart_change
#print axioms CycleQ2HodgeCotangentEulerTransition.basic_invariance

#print axioms CycleQ2HodgeCotangentEulerTransition.original_weights
