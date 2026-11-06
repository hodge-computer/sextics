import HodgeComputer.Constructions.RationalFields.EulerCorrection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-!
# Actual affine-to-homogeneous field transfer

The chart sends affine coordinates x_i to X_(i+1)/X0, with a=X0. Its
chain rules are recorded explicitly. They imply zero Euler degree on every
chart function, derive the homogenized divergence, and discharge the degree-zero
premise in the final Euler correction. No desired divergence is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Conic

variable {R S : Type*} [Field R] [Field S] [Algebra ℚ R] [Algebra ℚ S]

/-- The explicit first-derivative rules of the projective affine chart. -/
structure HomogeneousChart (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x : Fin 5 → R) : Prop where
  a_ne_zero : a ≠ 0
  a_zero : θ 0 a = 1
  a_succ : ∀ i : Fin 5, θ i.succ a = 0
  map_zero : ∀ z, θ 0 (f z) = -a⁻¹ * f (fieldAction δ x z)
  map_succ : ∀ (i : Fin 5) (z : R), θ i.succ (f z) = a⁻¹ * f (δ i z)
  coordinate_diagonal : ∀ i, δ i (x i) = 1

/-- v0=0 and v_(i+1)=a*p_i on the chart. -/
def homogenizedField (f : R →+* S) (a : S) (p : Fin 5 → R) : Fin 6 → S :=
  Fin.cases 0 (fun i => a * f (p i))

/-- The six-coordinate Euler field in chart coordinates. -/
def chartEuler (f : R →+* S) (a : S) (x : Fin 5 → R) : Fin 6 → S :=
  Fin.cases a (fun i => a * f (x i))

/-- Homogenizing the field transports its actual divergence without a scaling factor. -/
theorem homogenizedField_divergence (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x p : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) :
    fieldDivergence θ (homogenizedField f a p) = f (fieldDivergence δ p) := by
  unfold fieldDivergence
  rw [Fin.sum_univ_succ]
  simp only [homogenizedField, Fin.cases_zero,
    Fin.cases_succ, map_zero, zero_add, Derivation.leibniz, smul_eq_mul,
    h.a_succ, h.map_succ, mul_zero, add_zero, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [h.a_ne_zero]

/-- A degree-six function has the displayed homogenized contraction. -/
theorem homogenizedField_contraction (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x p : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) (H : R) :
    fieldAction θ (homogenizedField f a p) (a ^ 6 * f H) =
      a ^ 6 * f (fieldAction δ p H) := by
  rw [fieldAction_apply, Fin.sum_univ_succ]
  simp only [fieldAction_apply, homogenizedField, Fin.cases_zero,
    Fin.cases_succ, zero_mul, zero_add, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, h.a_succ, h.map_succ, mul_zero, smul_zero, add_zero, map_sum, map_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [h.a_ne_zero]

/-- Every pulled-back chart function has Euler degree zero. -/
theorem chartEuler_map (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) (z : R) :
    fieldAction θ (chartEuler f a x) (f z) = 0 := by
  rw [fieldAction_apply, Fin.sum_univ_succ]
  simp only [fieldAction_apply, chartEuler, Fin.cases_zero,
    Fin.cases_succ, h.map_zero, h.map_succ]
  have hfirst : a * (-a⁻¹ * f (∑ i, x i * δ i z)) = -f (∑ i, x i * δ i z) := by
    field_simp [h.a_ne_zero]
  rw [hfirst, map_sum]
  have hs : (∑ i, a * f (x i) * (a⁻¹ * f (δ i z))) =
      ∑ i, f (x i * δ i z) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    field_simp [h.a_ne_zero]
  rw [hs]
  exact neg_add_cancel _

/-- The Euler field differentiates the homogeneous scale by its degree. -/
theorem chartEuler_a (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) : fieldAction θ (chartEuler f a x) a = a := by
  rw [fieldAction_apply, Fin.sum_univ_succ]
  simp [chartEuler, h.a_zero, h.a_succ]

/-- Six-coordinate divergence of the Euler field is exactly six. -/
theorem chartEuler_divergence (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) : fieldDivergence θ (chartEuler f a x) = 6 := by
  unfold fieldDivergence
  rw [Fin.sum_univ_succ]
  simp only [chartEuler, Fin.cases_zero,
    Fin.cases_succ, h.a_zero, Derivation.leibniz, smul_eq_mul, h.a_succ,
    h.map_succ, h.coordinate_diagonal, map_one, mul_one, mul_zero, add_zero]
  norm_num [mul_inv_cancel₀ h.a_ne_zero]

/-- The homogeneous sextic has Euler degree six, derived from the chart rules. -/
theorem chartEuler_sextic (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) (H : R) :
    fieldAction θ (chartEuler f a x) (a ^ 6 * f H) = 6 * (a ^ 6 * f H) := by
  rw [Derivation.leibniz, chartEuler_map δ θ f a x h H, Derivation.leibniz_pow,
    chartEuler_a δ θ f a x h]
  simp only [smul_eq_mul, mul_zero, zero_add, nsmul_eq_mul]
  norm_num
  ring

/-- Homogenization transports the raw game identity exactly. -/
theorem homogenizedField_game (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x p : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) (H A : R)
    (hgame : A - fieldAction δ p H + H * fieldDivergence δ p = 0) :
    a ^ 6 * f A - fieldAction θ (homogenizedField f a p) (a ^ 6 * f H) +
      (a ^ 6 * f H) * fieldDivergence θ (homogenizedField f a p) = 0 := by
  rw [homogenizedField_contraction δ θ f a x p h H,
    homogenizedField_divergence δ θ f a x p h]
  have hh := congrArg f hgame
  simp only [map_add, map_sub, map_mul, map_zero] at hh
  linear_combination a ^ 6 * hh

variable [CharZero S]

/-- Actual chart homogenization followed by Euler subtraction is strict.
The degree-zero condition on the raw divergence is proved from the chart rules. -/
theorem homogenizedField_strict (δ : Fin 5 → Derivation ℚ R R)
    (θ : Fin 6 → Derivation ℚ S S) (f : R →+* S) (a : S) (x p : Fin 5 → R)
    (h : HomogeneousChart δ θ f a x) (H A : R)
    (hgame : A - fieldAction δ p H + H * fieldDivergence δ p = 0) :
    fieldAction θ (eulerCorrection θ (chartEuler f a x) (homogenizedField f a p))
        (a ^ 6 * f H) = a ^ 6 * f A ∧
      fieldDivergence θ (eulerCorrection θ (chartEuler f a x) (homogenizedField f a p)) = 0 := by
  apply eulerCorrection_strict
  · exact chartEuler_sextic δ θ f a x h H
  · exact chartEuler_divergence δ θ f a x h
  · rw [homogenizedField_divergence δ θ f a x p h]
    exact chartEuler_map δ θ f a x h _
  · exact homogenizedField_game δ θ f a x p h H A hgame

end HodgeTestbed.Conic
