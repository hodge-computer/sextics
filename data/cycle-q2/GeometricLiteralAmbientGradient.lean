import Proposal.GeometricLiteralAmbientEquation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination

/-! Homogeneity and reduction to the ordinary chart at the literal trace seed.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAmbientEquation

open MvPolynomial

theorem gradient_scale {R : Type*} [CommRing R] (t a b c d : R) (j : Fin 4) :
    gradient (t*a) (t*b) (t*c) (t*d) j = t^5 * gradient a b c d j := by
  fin_cases j <;> simp [gradient, cubic] <;> ring

/-- The four integral gradient polynomials are all homogeneous of degree five,
also after any change of coefficient ring. -/
theorem gradient_homogeneous {R : Type*} [CommRing R] (j : Fin 4) :
    (gradient (X 0) (X 1) (X 2) (X 3) j : MvPolynomial (Fin 4) R).IsHomogeneous 5 := by
  let V := MvPolynomial (Fin 4) R
  have hx (i : Fin 4) := isHomogeneous_X R i
  have hp (i : Fin 4) (n : ℕ) := isHomogeneous_X_pow (R := R) i n
  have h2 : (2 : V).IsHomogeneous 0 := by
    rw [← (map_ofNat (C : R →+* V) 2)]
    exact isHomogeneous_C _ _
  have h3 : (3 : V).IsHomogeneous 0 := by
    rw [← (map_ofNat (C : R →+* V) 3)]
    exact isHomogeneous_C _ _
  have h6 : (6 : V).IsHomogeneous 0 := by
    rw [← (map_ofNat (C : R →+* V) 6)]
    exact isHomogeneous_C _ _
  have hl : (3*(2-57^3) : V).IsHomogeneous 0 := by
    have he : (C : R →+* V) (3*(2-57^3)) = 3*(2-57^3) := by
      simp only [map_mul, map_sub, map_pow, map_ofNat]
    rw [← he]
    exact isHomogeneous_C _ _
  have hc : (cubic (X 0) (X 1) (X 2) (X 3) : V).IsHomogeneous 3 :=
    (((((hp 3 3).add (hp 2 3)).add (((hx 1).mul (hx 2)).mul (hx 3))).add
      (((hx 0).mul (hx 2)).mul (hx 3))).add ((hx 0).mul (hp 1 2))).add (hp 0 3)
  fin_cases j
  · exact (h6.mul (hp 0 5)).add ((h2.mul hc).mul ((((hx 2).mul (hx 3)).add
      (hp 1 2)).add (h3.mul (hp 0 2))))
  · exact ((h6.mul (hp 1 5)).add ((hl.mul (hp 1 2)).mul (hp 3 3))).add
      ((h2.mul hc).mul (((hx 2).mul (hx 3)).add ((h2.mul (hx 0)).mul (hx 1))))
  · exact (h6.mul (hp 2 5)).add ((h2.mul hc).mul (((h3.mul (hp 2 2)).add
      ((hx 1).mul (hx 3))).add ((hx 0).mul (hx 3))))
  · exact ((h6.mul (hp 3 5)).add ((hl.mul (hp 1 3)).mul (hp 3 2))).add
      ((h2.mul hc).mul (((h3.mul (hp 3 2)).add ((hx 1).mul (hx 2))).add
        ((hx 0).mul (hx 2))))

private theorem binary_gradient_zero {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0) (x y s : K)
    (hs : s = x^3+y^3)
    (hx : 6*x^5+2*s*(3*x^2) = 0) (hy : 6*y^5+2*s*(3*y^2) = 0) :
    x = 0 ∧ y = 0 := by
  have h6 : (6:K) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; norm_num
  have split (v : K) (hv : 6*v^5+2*s*(3*v^2) = 0) : v = 0 ∨ v^3+s = 0 := by
    have hp : 6*(v^2*(v^3+s)) = 0 := by linear_combination hv
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left h6) with h | h
    · exact Or.inl (eq_zero_of_pow_eq_zero h)
    · exact Or.inr h
  rcases split x hx with h | h <;> rcases split y hy with h' | h'
  · exact ⟨h,h'⟩
  · subst x
    simp only [zero_pow (by decide : 3 ≠ 0), zero_add] at hs
    have hp : 2*y^3 = 0 := by linear_combination h' - hs
    exact ⟨rfl, eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hp).resolve_left h2)⟩
  · subst y
    simp only [zero_pow (by decide : 3 ≠ 0), add_zero] at hs
    have hp : 2*x^3 = 0 := by linear_combination h - hs
    exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hp).resolve_left h2), rfl⟩
  · have hp : 3*s = 0 := by linear_combination h+h'+hs
    have hz := (mul_eq_zero.mp hp).resolve_left h3
    rw [hz, add_zero] at h h'
    exact ⟨eq_zero_of_pow_eq_zero h, eq_zero_of_pow_eq_zero h'⟩

/-- On the hyperplane b = 0, the second gradient equation forces the cubic,
c, or d to vanish. The two remaining pure powers then vanish. -/
theorem gradient_zero_at_b_zero {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0) (a c d : K)
    (hg : ∀ j, gradient a 0 c d j = 0) : a = 0 ∧ c = 0 ∧ d = 0 := by
  have h6 : (6:K) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; norm_num
  have ha := hg 0
  have hb := hg 1
  have hc := hg 2
  have hd := hg 3
  simp [gradient] at ha hb hc hd
  rcases hb with (h | h) | h | h
  · exact (h2 h).elim
  · rw [h] at ha hc hd
    simp only [mul_zero, zero_mul, add_zero] at ha hc hd
    exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp ha).resolve_left h6),
      eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hc).resolve_left h6),
      eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hd).resolve_left h6)⟩
  · subst c
    simp at ha hd
    have hs : cubic a 0 0 d = a^3+d^3 := by simp [cubic]; ring
    obtain ⟨ha',hd'⟩ := binary_gradient_zero h2 h3 a d _ hs ha hd
    exact ⟨ha',rfl,hd'⟩
  · subst d
    simp at ha hc
    have hs : cubic a 0 c 0 = a^3+c^3 := by simp [cubic]; ring
    obtain ⟨ha',hc'⟩ := binary_gradient_zero h2 h3 a c _ hs ha hc
    exact ⟨ha',hc',rfl⟩

/-- Reduction to the normalized chart b = 1, valid over any field of
characteristic different from two and three. -/
theorem gradient_zero_of_chart {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0)
    (chart : ∀ a c d : K, (∀ j, gradient a 1 c d j = 0) → False)
    (a b c d : K) (hg : ∀ j, gradient a b c d j = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  by_cases hb : b = 0
  · subst b
    obtain ⟨ha,hc,hd⟩ := gradient_zero_at_b_zero h2 h3 a c d hg
    exact ⟨ha,rfl,hc,hd⟩
  · apply False.elim
    apply chart (b⁻¹*a) (b⁻¹*c) (b⁻¹*d)
    intro j
    simpa only [inv_mul_cancel₀ hb, hg j, mul_zero] using gradient_scale b⁻¹ a b c d j

end CycleQ2LiteralAmbientEquation
