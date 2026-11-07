import Proposal.SymmetricNegativeSource

/-! The only monomials that can multiply the five partial derivatives
into the negative weighted-sextic piece. -/

namespace SymmetricNegativeSource

set_option backward.isDefEq.respectTransparency false

theorem exponent_ext_five {e f : Exponent}
    (h0 : e 0 = f 0) (h1 : e 1 = f 1) (h2 : e 2 = f 2)
    (h3 : e 3 = f 3) (h4 : e 4 = f 4) : e = f := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem odd_linear_exponent {e : Exponent} (hdeg : weightedDegree e = 1)
    (hodd : (e 2 + e 3) % 2 = 1) :
    e = Finsupp.single 2 1 ∨ e = Finsupp.single 3 1 := by
  unfold weightedDegree at hdeg
  have h : (e 2 = 1 ∧ e 3 = 0) ∨ (e 2 = 0 ∧ e 3 = 1) := by omega
  rcases h with h | h
  · left
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega
  · right
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega

theorem even_linear_exponent {e : Exponent} (hdeg : weightedDegree e = 1)
    (heven : (e 2 + e 3) % 2 = 0) :
    e = Finsupp.single 0 1 ∨ e = Finsupp.single 1 1 := by
  unfold weightedDegree at hdeg
  have h : (e 0 = 1 ∧ e 1 = 0) ∨ (e 0 = 0 ∧ e 1 = 1) := by omega
  rcases h with h | h
  · left
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega
  · right
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega

theorem odd_quadratic_exponent {e : Exponent} (hdeg : weightedDegree e = 2)
    (hodd : (e 2 + e 3) % 2 = 1) :
    e = Finsupp.single 0 1 + Finsupp.single 2 1 ∨
    e = Finsupp.single 0 1 + Finsupp.single 3 1 ∨
    e = Finsupp.single 1 1 + Finsupp.single 2 1 ∨
    e = Finsupp.single 1 1 + Finsupp.single 3 1 := by
  unfold weightedDegree at hdeg
  have ha : e 0 = 1 ∨ e 1 = 1 := by omega
  have hc : e 2 = 1 ∨ e 3 = 1 := by omega
  rcases ha with ha | ha <;> rcases hc with hc | hc
  · left
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega
  · right; left
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega
  · right; right; left
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega
  · right; right; right
    apply exponent_ext_five <;> norm_num [Finsupp.single_apply, Fin.ext_iff] <;> omega

end SymmetricNegativeSource
