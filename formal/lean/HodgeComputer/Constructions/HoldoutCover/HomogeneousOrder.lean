import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/- Source component: HomogeneousOrder -/
section
/-!
Finite homogeneous-component calculus for clearing a rational field.
No formal power series or Laurent series occur in this construction.
These are intermediate lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

/-- Every monomial has degree at least `n`; the zero polynomial satisfies
this condition for every `n`. -/
def HasOrder (n : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < n → p.coeff m = 0

theorem HasOrder.mono {n k : ℕ} {p : MvPolynomial σ R}
    (h : HasOrder n p) (hk : k ≤ n) : HasOrder k p :=
  fun m hm => h m (lt_of_lt_of_le hm hk)

theorem hasOrder_zero (n : ℕ) : HasOrder n (0 : MvPolynomial σ R) := by
  intro m _
  simp

theorem hasOrder_zero_degree (p : MvPolynomial σ R) : HasOrder 0 p := by
  intro m hm
  omega

theorem HasOrder.add {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p+q) := by
  intro m hm
  simp [hp m hm, hq m hm]

theorem HasOrder.sub {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p-q) := by
  intro m hm
  simp [hp m hm, hq m hm]

theorem HasOrder.neg {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder n (-p) := by
  intro m hm
  simp [hp m hm]

theorem HasOrder.sum {ι : Type*} (s : Finset ι) {n : ℕ}
    (p : ι → MvPolynomial σ R) (hp : ∀ i ∈ s, HasOrder n (p i)) :
    HasOrder n (∑ i ∈ s, p i) := by
  intro m hm
  simp only [coeff_sum]
  exact Finset.sum_eq_zero fun i hi => hp i hi m hm

theorem HasOrder.mul {n k : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder k q) : HasOrder (n+k) (p*q) := by
  classical
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp ha)
  simp only [map_add] at he
  by_cases h : a.1.degree < n
  · rw [hp _ h, zero_mul]
  · have h' : a.2.degree < k := by omega
    rw [hq _ h', mul_zero]

theorem HasOrder.pow {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (k : ℕ) : HasOrder (k*n) (p^k) := by
  induction k with
  | zero => simpa using hasOrder_zero_degree (1 : MvPolynomial σ R)
  | succ k ih =>
    simpa only [pow_succ, Nat.succ_mul] using ih.mul hp

theorem HasOrder.pderiv {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (i : σ) : HasOrder (n-1) (pderiv i p) := by
  intro m hm
  rw [coeff_pderiv]
  have hd : (m + Finsupp.single i 1).degree < n := by
    simp only [map_add, Finsupp.degree_single]
    omega
  rw [hp _ hd, zero_mul]

theorem isHomogeneous_hasOrder {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : HasOrder n p := by
  intro m hm
  exact hp.coeff_eq_zero (ne_of_lt hm)

theorem HasOrder.component_eq_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) {k : ℕ} (hk : k < n) : homogeneousComponent k p = 0 := by
  classical
  ext m
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact hp m (h ▸ hk)
  · rfl

theorem hasOrder_of_components_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ k < n, homogeneousComponent k p = 0) : HasOrder n p := by
  intro m hm
  have h := congrArg (·.coeff m) (hp m.degree hm)
  simpa [coeff_homogeneousComponent] using h

/-- Multiplication of the first possible homogeneous components. -/
theorem component_mul_initial {n k : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder k q) :
    homogeneousComponent (n+k) (p*q) =
      homogeneousComponent n p * homogeneousComponent k q := by
  classical
  ext m
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  rw [Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  intro a ha
  have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp ha)
  simp only [map_add] at he
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  by_cases h1 : a.1.degree < n
  · simp [hp _ h1, ne_of_lt h1]
  by_cases h2 : a.2.degree < k
  · simp [hq _ h2, ne_of_lt h2]
  by_cases h1' : a.1.degree = n
  · by_cases h2' : a.2.degree = k
    · have hm : m.degree = n+k := by omega
      simp [h1', h2', hm]
    · have hm : m.degree ≠ n+k := by omega
      simp [h2', hm]
  · have hm : m.degree ≠ n+k := by omega
    simp [h1', hm]

theorem pderiv_component (n : ℕ) (p : MvPolynomial σ R) (i : σ) :
    pderiv i (homogeneousComponent (n+1) p) =
      homogeneousComponent n (pderiv i p) := by
  classical
  ext m
  simp only [coeff_pderiv, coeff_homogeneousComponent, map_add,
    Finsupp.degree_single, Nat.add_right_cancel_iff, ite_mul, zero_mul]

theorem component_mul_homogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (k : ℕ) (q : MvPolynomial σ R) :
    homogeneousComponent (n+k) (p*q) = p*homogeneousComponent k q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : MvPolynomial σ R).IsHomogeneous m.degree :=
      isHomogeneous_monomial _ rfl
    rw [homogeneousComponent_of_mem (hp.mul hm), homogeneousComponent_of_mem hm]
    simp only [Nat.add_left_cancel_iff]
    split_ifs <;> simp
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]

theorem pderiv_isHomogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous (n+1)) (i : σ) : (pderiv i p).IsHomogeneous n := by
  have h := pderiv_component n p i
  rw [homogeneousComponent_eq_self hp] at h
  rw [h]
  exact homogeneousComponent_isHomogeneous n _

/-- Subtracting the least component raises the order strictly. -/
theorem order_sub_initial {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder (n+1) (homogeneousComponent n p - p) := by
  classical
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = n
  · simp [h]
  · have hlt : m.degree < n := by omega
    simp [h, hp _ hlt]

end HoldoutConstruction

#print axioms HoldoutConstruction.component_mul_initial
#print axioms HoldoutConstruction.pderiv_component
end
end
