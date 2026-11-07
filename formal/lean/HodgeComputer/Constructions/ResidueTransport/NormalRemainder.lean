import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Strict currents of bounded degree in one normal coordinate

Over a coefficient field, a legal cleared current at positive pole parameter
`q` can be reduced componentwise modulo `f^q`. The resulting polynomial
current has degree less than `q * natDegree f` in the normal coordinate.
If the source has degree less than `(q+1) * natDegree f`, and the coordinate
derivations do not increase normal degree, its defect vanishes identically.

The inverse of the denominator modulo `f^q` is constructed from Bezout.
Derivations are not assumed to descend to that quotient. Instead the exact
identity for adding `f^q` times a field preserves the defect modulo
`f^(q+1)`. The theorem retains arbitrary rational coefficients in the base
field and does not bound their poles or assert that a current exists.
-/

noncomputable section

namespace NormalRemainder

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Calculus

variable {R ι : Type*} [CommRing R] [Fintype ι]

def action (δ : ι → Derivation ℤ R R) (N : ι → R) (f : R) : R :=
  ∑ i, N i*δ i f

def divergence (δ : ι → Derivation ℤ R R) (N : ι → R) : R :=
  ∑ i, δ i (N i)

def operator (δ : ι → Derivation ℤ R R) (f : R) (q : ℕ) (N : ι → R) : R :=
  (q:R)*action δ N f-f*divergence δ N

def clearedDefect (δ : ι → Derivation ℤ R R) (f P D : R)
    (q : ℕ) (N : ι → R) : R :=
  P*D^2-(q:R)*D*action δ N f+
    f*(D*divergence δ N-action δ N D)

theorem action_add (δ : ι → Derivation ℤ R R) (N M : ι → R) (f : R) :
    action δ (fun i => N i+M i) f = action δ N f+action δ M f := by
  simp only [action, add_mul, Finset.sum_add_distrib]

theorem action_mul (δ : ι → Derivation ℤ R R) (N : ι → R) (s f : R) :
    action δ (fun i => s*N i) f = s*action δ N f := by
  simp only [action, mul_assoc, Finset.mul_sum]

theorem divergence_add (δ : ι → Derivation ℤ R R) (N M : ι → R) :
    divergence δ (fun i => N i+M i) = divergence δ N+divergence δ M := by
  simp only [divergence, map_add, Finset.sum_add_distrib]

theorem divergence_mul (δ : ι → Derivation ℤ R R) (N : ι → R) (s : R) :
    divergence δ (fun i => s*N i) = action δ N s+s*divergence δ N := by
  simp only [divergence, action, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem action_power_weighted (δ : ι → Derivation ℤ R R)
    (N : ι → R) (f : R) (q : ℕ) :
    f*action δ N (f^q) = (q:R)*f^q*action δ N f := by
  cases q with
  | zero => simp [action]
  | succ q =>
    simp only [action, Derivation.leibniz_pow, smul_eq_mul,
      Nat.add_sub_cancel, Finset.mul_sum, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- This exact cancellation, not a derivation on the residue ring, makes
componentwise reduction modulo `f^q` preserve the certificate equation. -/
theorem operator_power_multiple (δ : ι → Derivation ℤ R R)
    (T : ι → R) (f : R) (q : ℕ) :
    operator δ f q (fun i => f^q*T i) = -f^(q+1)*divergence δ T := by
  rw [operator, action_mul, divergence_mul]
  have h := action_power_weighted δ T f q
  rw [pow_succ]
  linear_combination -h

/-- The full denominator-cleared identity after extracting a polynomial
representative. All derivatives of the old denominator are retained. -/
theorem cleared_decomposition (δ : ι → Derivation ℤ R R)
    (f P D : R) (q : ℕ) (U T : ι → R) :
    clearedDefect δ f P D q (fun i => D*U i+f^q*T i) =
      D^2*(P-operator δ f q U)+
        f^(q+1)*(D*divergence δ T-action δ T D) := by
  simp only [clearedDefect, action_add, action_mul, divergence_add,
    divergence_mul, operator]
  have h := action_power_weighted δ T f q
  rw [pow_succ]
  linear_combination D*h

end Calculus

section PolynomialReduction

variable {K ι : Type*} [Field K] [Fintype ι]

open Polynomial

omit [Fintype ι] in
/-- Invert the denominator modulo the selected equation power and take
literal polynomial remainders. This supplies both the degree bound and the
exact numerator decomposition needed by `cleared_decomposition`. -/
theorem polynomial_representatives
    (f D : K[X]) (N : ι → K[X]) (q : ℕ)
    (hf : 0 < f.natDegree) (hq : 0 < q) (hcop : IsCoprime f D) :
    ∃ U T : ι → K[X],
      (∀ i, (U i).natDegree < q*f.natDegree) ∧
      (∀ i, N i = D*U i+f^q*T i) := by
  obtain ⟨a,b,hab⟩ := hcop.pow_left (m := q)
  let U : ι → K[X] := fun i => (b*N i) % (f^q)
  let T : ι → K[X] := fun i => a*N i+D*((b*N i)/(f^q))
  refine ⟨U,T,?_,?_⟩
  · intro i
    have hp : (f^q).natDegree ≠ 0 := by
      rw [natDegree_pow]
      exact Nat.ne_of_gt (Nat.mul_pos hq hf)
    simpa only [U, natDegree_pow] using natDegree_mod_lt (b*N i) hp
  · intro i
    have hrem := EuclideanDomain.mod_add_div (b*N i) (f^q)
    dsimp [U,T]
    linear_combination -(N i)*hab-D*hrem

/-- Ordinary coefficient derivatives and the normal derivative satisfy this
bound. They need not commute, nor preserve the ideal generated by `f`. -/
def PreservesDegree (δ : ι → Derivation ℤ K[X] K[X]) : Prop :=
  ∀ i p, (δ i p).natDegree ≤ p.natDegree

theorem residual_degree_bound
    (δ : ι → Derivation ℤ K[X] K[X]) (hδ : PreservesDegree δ)
    (f P : K[X]) (q : ℕ) (U : ι → K[X])
    (hf : 0 < f.natDegree) (hq : 0 < q)
    (hP : P.natDegree < (q+1)*f.natDegree)
    (hU : ∀ i, (U i).natDegree < q*f.natDegree) :
    (P-operator δ f q U).natDegree < (q+1)*f.natDegree := by
  have hqm : 0 < q*f.natDegree := Nat.mul_pos hq hf
  have hdiv : (divergence δ U).natDegree ≤ q*f.natDegree-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    have h := (hδ i (U i)).trans_lt (hU i)
    omega
  have hact : (action δ U f).natDegree ≤ (q+1)*f.natDegree-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    have hm := natDegree_mul_le (p := U i) (q := δ i f)
    have hd := hδ i f
    have hu := hU i
    rw [Nat.add_mul, one_mul]
    omega
  have hscale : ((q : K[X])*action δ U f).natDegree ≤
      (q+1)*f.natDegree-1 := by
    have hm := natDegree_mul_le (p := (q : K[X])) (q := action δ U f)
    have hz : (q : K[X]).natDegree = 0 := by
      rw [← map_natCast (Polynomial.C : K →+* K[X])]
      exact natDegree_C _
    rw [hz, zero_add] at hm
    exact hm.trans hact
  have hprod : (f*divergence δ U).natDegree ≤ (q+1)*f.natDegree-1 := by
    have hm := natDegree_mul_le (p := f) (q := divergence δ U)
    rw [Nat.add_mul, one_mul]
    omega
  have hop : (operator δ f q U).natDegree ≤ (q+1)*f.natDegree-1 := by
    exact (natDegree_sub_le _ _).trans (max_le hscale hprod)
  have hr := natDegree_sub_le P (operator δ f q U)
  have ht : 0 < (q+1)*f.natDegree := Nat.mul_pos (by omega) hf
  omega

/-- Every legal current under the stated normal-degree bound has a strict
polynomial representative of degree less than `q*deg(f)` in that coordinate.
The coefficient field retains all base-space denominator freedom. -/
theorem strict_polynomial_representative
    (δ : ι → Derivation ℤ K[X] K[X]) (hδ : PreservesDegree δ)
    (f P D Q : K[X]) (q : ℕ) (N : ι → K[X])
    (hf : 0 < f.natDegree) (hq : 0 < q) (hcop : IsCoprime f D)
    (hP : P.natDegree < (q+1)*f.natDegree)
    (hgame : clearedDefect δ f P D q N = f^(q+1)*Q) :
    ∃ U : ι → K[X],
      (∀ i, (U i).natDegree < q*f.natDegree) ∧ operator δ f q U = P := by
  obtain ⟨U,T,hU,hN⟩ := polynomial_representatives f D N q hf hq hcop
  have hfun : N = fun i => D*U i+f^q*T i := funext hN
  rw [hfun, cleared_decomposition] at hgame
  have hmul : f^(q+1) ∣ D^2*(P-operator δ f q U) := by
    refine ⟨Q-(D*divergence δ T-action δ T D), ?_⟩
    linear_combination hgame
  have hcop' : IsCoprime (f^(q+1)) (D^2) := hcop.pow
  have hdvd := hcop'.dvd_of_dvd_mul_left hmul
  have hsmall := residual_degree_bound δ hδ f P q U hf hq hP hU
  have hz : P-operator δ f q U = 0 := by
    by_contra hn
    have hle := natDegree_le_of_dvd hdvd hn
    rw [natDegree_pow] at hle
    omega
  exact ⟨U,hU,(sub_eq_zero.mp hz).symm⟩

/-- The usual relative-primality interface suffices over the coefficient
field's univariate polynomial ring. -/
theorem strict_polynomial_representative_of_relPrime
    (δ : ι → Derivation ℤ K[X] K[X]) (hδ : PreservesDegree δ)
    (f P D Q : K[X]) (q : ℕ) (N : ι → K[X])
    (hf : 0 < f.natDegree) (hq : 0 < q) (hcop : IsRelPrime f D)
    (hP : P.natDegree < (q+1)*f.natDegree)
    (hgame : clearedDefect δ f P D q N = f^(q+1)*Q) :
    ∃ U : ι → K[X],
      (∀ i, (U i).natDegree < q*f.natDegree) ∧ operator δ f q U = P :=
  strict_polynomial_representative δ hδ f P D Q q N hf hq hcop.isCoprime hP hgame

/-- Under the degree hypotheses, bounded strict polynomial currents and
arbitrary legal cleared currents have exactly the same existence problem.
The denominators inside the coefficient field remain unrestricted. -/
theorem existence_iff_bounded_strict
    (δ : ι → Derivation ℤ K[X] K[X]) (hδ : PreservesDegree δ)
    (f P : K[X]) (q : ℕ) (hf : 0 < f.natDegree) (hq : 0 < q)
    (hP : P.natDegree < (q+1)*f.natDegree) :
    (∃ (D Q : K[X]) (N : ι → K[X]), D ≠ 0 ∧ IsRelPrime f D ∧
      clearedDefect δ f P D q N = f^(q+1)*Q) ↔
      ∃ U : ι → K[X],
        (∀ i, (U i).natDegree < q*f.natDegree) ∧ operator δ f q U = P := by
  constructor
  · rintro ⟨D,Q,N,_,hcop,hgame⟩
    exact strict_polynomial_representative_of_relPrime δ hδ f P D Q q N
      hf hq hcop hP hgame
  · rintro ⟨U,_,hU⟩
    refine ⟨1,0,U,one_ne_zero,isRelPrime_one_right,?_⟩
    simp only [clearedDefect, one_pow, mul_one, one_mul, mul_zero,
      action, Derivation.map_one_eq_zero, Finset.sum_const_zero, sub_zero]
    change P-(q:K[X])*action δ U f+f*divergence δ U = 0
    unfold operator at hU
    linear_combination -hU

end PolynomialReduction

#print axioms operator_power_multiple
#print axioms polynomial_representatives
#print axioms strict_polynomial_representative_of_relPrime
#print axioms existence_iff_bounded_strict

end NormalRemainder
