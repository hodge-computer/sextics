import Mathlib.Algebra.GroupWithZero.Associated
import HodgeComputer.Constructions.HoldoutCover.HomogeneousOrder

/- Source component: HomogeneousIdeal -/
section
/-!
Finite homogeneous ideal calculus and cancellation at a legal leading term.
These are intermediate construction lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

theorem component_component (n k : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (homogeneousComponent k p) =
      if n = k then homogeneousComponent k p else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous k p)

/-- A homogeneous principal ideal contains every homogeneous component of
each of its elements. This proof uses only a finite decomposition. -/
theorem component_dvd_of_dvd {F p : MvPolynomial σ R} {f : ℕ}
    (hF : F.IsHomogeneous f) (hp : F ∣ p) (n : ℕ) :
    F ∣ homogeneousComponent n p := by
  classical
  obtain ⟨q, rfl⟩ := hp
  rw [← sum_homogeneousComponent q, Finset.mul_sum, map_sum]
  apply Finset.dvd_sum
  intro i _
  rw [homogeneousComponent_of_mem (hF.mul (homogeneousComponent_isHomogeneous i q))]
  split_ifs
  · exact dvd_mul_right F _
  · exact dvd_zero F

/-- Sum of the components of degree strictly below `n`. -/
def truncateBelow (n : ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ k ∈ Finset.range n, homogeneousComponent k p

theorem component_truncateBelow (n k : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent k (truncateBelow n p) =
      if k < n then homogeneousComponent k p else 0 := by
  classical
  simp [truncateBelow, component_component]

theorem order_sub_truncateBelow (n : ℕ) (p : MvPolynomial σ R) :
    HasOrder n (p - truncateBelow n p) := by
  apply hasOrder_of_components_zero
  intro k hk
  simp [component_truncateBelow, hk]

theorem component_sub_truncateBelow (n : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (p - truncateBelow n p) = homogeneousComponent n p := by
  simp [component_truncateBelow]

/-- Cancellation of a denominator's legal initial component, proved by
induction over finitely many homogeneous components. -/
theorem component_dvd_of_product {F C B : MvPolynomial σ R} {f c : ℕ}
    (hF : F.IsHomogeneous f) (hprime : Prime F)
    (hC : HasOrder c C) (hlegal : ¬ F ∣ homogeneousComponent c C)
    (n : ℕ)
    (hproduct : ∀ k ≤ n, F ∣ homogeneousComponent (c+k) (C*B)) :
    F ∣ homogeneousComponent n B := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have htrunc : F ∣ truncateBelow n B := by
      apply Finset.dvd_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      exact ih k hkn (fun j hj => hproduct j (le_trans hj (Nat.le_of_lt hkn)))
    have hprod : F ∣ homogeneousComponent (c+n) (C*(B-truncateBelow n B)) := by
      rw [mul_sub, map_sub]
      exact dvd_sub (hproduct n le_rfl)
        (component_dvd_of_dvd hF (dvd_mul_of_dvd_right htrunc C) (c+n))
    rw [component_mul_initial hC (order_sub_truncateBelow n B),
      component_sub_truncateBelow] at hprod
    exact (hprime.dvd_mul.mp hprod).resolve_left hlegal

/-- A polynomial nonzero modulo `F` can be replaced, modulo `F`, by one
whose least homogeneous component is already nonzero modulo `F`. Only the
finitely many preceding homogeneous components are discarded. -/
theorem exists_legal_initial_representative (F p : MvPolynomial σ R)
    (hp : ¬ F ∣ p) :
    ∃ d : ℕ, ∃ q : MvPolynomial σ R,
      F ∣ p-q ∧ HasOrder d q ∧ ¬ F ∣ homogeneousComponent d q := by
  classical
  have hex : ∃ d : ℕ, ¬ F ∣ homogeneousComponent d p := by
    by_contra h
    push Not at h
    apply hp
    rw [← sum_homogeneousComponent p]
    exact Finset.dvd_sum (fun i _ => h i)
  let d := Nat.find hex
  have hfirst : ¬ F ∣ homogeneousComponent d p := Nat.find_spec hex
  have hprevious : ∀ k < d, F ∣ homogeneousComponent k p := by
    intro k hk
    by_contra hbad
    have hmin : d ≤ k := Nat.find_min' hex hbad
    omega
  have htrunc : F ∣ truncateBelow d p := by
    apply Finset.dvd_sum
    intro k hk
    exact hprevious k (Finset.mem_range.mp hk)
  refine ⟨d, p-truncateBelow d p, ?_, order_sub_truncateBelow d p, ?_⟩
  · simpa only [sub_sub_cancel] using htrunc
  · rwa [component_sub_truncateBelow]

/-- Multiplication by a fixed homogeneous normal derivative preserves a
legal initial component and makes its degree positive. -/
theorem legal_initial_mul_homogeneous {F g q : MvPolynomial σ R} {k d : ℕ}
    (hprime : Prime F) (hg : g.IsHomogeneous k) (hglegal : ¬ F ∣ g)
    (hq : HasOrder d q) (hqlegal : ¬ F ∣ homogeneousComponent d q) :
    HasOrder (k+d) (g*q) ∧ ¬ F ∣ homogeneousComponent (k+d) (g*q) := by
  refine ⟨(isHomogeneous_hasOrder hg).mul hq, ?_⟩
  rw [component_mul_initial (isHomogeneous_hasOrder hg) hq,
    homogeneousComponent_eq_self hg]
  intro h
  exact (hprime.dvd_mul.mp h).elim hglegal hqlegal

end HoldoutConstruction

#print axioms HoldoutConstruction.component_dvd_of_product
#print axioms HoldoutConstruction.exists_legal_initial_representative
end
end
