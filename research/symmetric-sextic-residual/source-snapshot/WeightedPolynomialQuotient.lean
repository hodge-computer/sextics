import WeightedPolynomialBindings
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
The actual monomial quotient and its coefficient coordinates.
In particular the original binomial expression D*(L^2+u)^5 has the
coefficient matrices already checked for its two-term truncation Q.
-/
namespace WeightedSupport.PolynomialModel

open MvPolynomial

def cap (i : Fin 6) : ℕ := if i = 5 then 1 else 4
def Bounded (e : Exponent) : Prop := ∀ i, e i ≤ cap i

instance (e : Exponent) : Decidable (Bounded e) := by unfold Bounded; infer_instance

noncomputable def truncationIdeal : Ideal Poly :=
  Ideal.span (Set.range fun i : Fin 6 => (X i : Poly) ^ (cap i + 1))

abbrev TruncatedRing := Poly ⧸ truncationIdeal

theorem coeff_variable_power_mul_zero (e : Exponent) (i : Fin 6) (n : ℕ)
    (h : e i < n) (p : Poly) : coeff (exponent e) (X i ^ n * p) = 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  have hn : ¬ Finsupp.single i n ≤ exponent e := by
    simpa only [Finsupp.single_le_iff, exponent_apply] using Nat.not_le.mpr h
  rw [if_neg hn]

theorem coeff_truncationIdeal_zero (e : Exponent) (he : Bounded e)
    (p : Poly) (hp : p ∈ truncationIdeal) : coeff (exponent e) p = 0 := by
  have haux : ∀ r : Poly, coeff (exponent e) (r * p) = 0 := by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro r
      rw [mul_comm]
      exact coeff_variable_power_mul_zero e i _ (Nat.lt_succ_of_le (he i)) r
    | zero =>
      intro r
      simp
    | add x y hx hy ihx ihy =>
      intro r
      rw [mul_add, MvPolynomial.coeff_add, ihx r, ihy r, zero_add]
    | smul a x hx ih =>
      intro r
      simpa only [smul_eq_mul, mul_assoc] using ih (r * a)
  simpa using haux 1

theorem coeff_eq_of_quotient_eq (e : Exponent) (he : Bounded e) (p q : Poly)
    (h : Ideal.Quotient.mk truncationIdeal p = Ideal.Quotient.mk truncationIdeal q) :
    coeff (exponent e) p = coeff (exponent e) q := by
  have hz := coeff_truncationIdeal_zero e he (p - q) (Ideal.Quotient.eq.mp h)
  rw [coeff_sub, sub_eq_zero] at hz
  exact hz

noncomputable def quotientCoeff (e : Exponent) (p : TruncatedRing) : ℤ :=
  coeff (exponent e) (Quotient.out p)

theorem quotientCoeff_mk (e : Exponent) (he : Bounded e) (p : Poly) :
    quotientCoeff e (Ideal.Quotient.mk truncationIdeal p) = coeff (exponent e) p := by
  apply coeff_eq_of_quotient_eq e he
  exact Ideal.Quotient.mk_out _

theorem q_binomial_remainder :
    D * (L ^ 2 + X 5) ^ 5 = Q +
      X 5 ^ 2 * (D * (10 * L ^ 6 + 10 * L ^ 4 * X 5 + 5 * L ^ 2 * X 5 ^ 2 + X 5 ^ 3)) := by
  unfold Q
  rw [map_ofNat]
  ring

theorem quotient_Q_binomial :
    Ideal.Quotient.mk truncationIdeal (D * (L ^ 2 + X 5) ^ 5) =
      Ideal.Quotient.mk truncationIdeal Q := by
  have hu : Ideal.Quotient.mk truncationIdeal ((X 5 : Poly) ^ 2) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    exact ⟨5, by simp [cap]⟩
  rw [q_binomial_remainder, map_add, map_mul, hu, zero_mul, add_zero]

theorem q_targets_bounded : ∀ i : Fin 120, Bounded (qTargetExponent i) := by
  decide +kernel

theorem hq_targets_bounded : ∀ i : Fin 74, Bounded (hqTargetExponent i) := by
  decide +kernel

noncomputable def QQuotientMatrix : Matrix (Fin 120) (Fin 82) ℤ := fun i j =>
  quotientCoeff (qTargetExponent i)
    (Ideal.Quotient.mk truncationIdeal (D * (L ^ 2 + X 5) ^ 5) *
      Ideal.Quotient.mk truncationIdeal (orbitPolynomial (sourceExponent j)))

noncomputable def HQQuotientMatrix : Matrix (Fin 74) (Fin 82) ℤ := fun i j =>
  quotientCoeff (hqTargetExponent i)
    (Ideal.Quotient.mk truncationIdeal H *
      Ideal.Quotient.mk truncationIdeal (D * (L ^ 2 + X 5) ^ 5) *
      Ideal.Quotient.mk truncationIdeal (orbitPolynomial (sourceExponent j)))

theorem Q_quotient_matrix_eq : QQuotientMatrix = CheckedRank.QMatrix := by
  rw [← Q_polynomial_matrix_eq]
  ext i j
  change quotientCoeff _ (_ * _) = _
  rw [quotient_Q_binomial, ← map_mul, quotientCoeff_mk _ (q_targets_bounded i)]
  rfl

theorem HQ_quotient_matrix_eq : HQQuotientMatrix = CheckedRank.HQMatrix := by
  rw [← HQ_polynomial_matrix_eq]
  ext i j
  change quotientCoeff _ (_ * _ * _) = _
  rw [quotient_Q_binomial, ← map_mul, ← map_mul, quotientCoeff_mk _ (hq_targets_bounded i)]
  rfl

theorem Q_quotient_rational_rank :
    (QQuotientMatrix.map (Int.castRingHom ℚ)).rank = 82 := by
  rw [Q_quotient_matrix_eq]
  exact CheckedRank.Q_rational_rank

theorem HQ_quotient_rational_rank :
    (HQQuotientMatrix.map (Int.castRingHom ℚ)).rank = 74 := by
  rw [HQ_quotient_matrix_eq]
  exact CheckedRank.HQ_rational_rank

#print axioms Q_quotient_rational_rank
#print axioms HQ_quotient_rational_rank

end WeightedSupport.PolynomialModel
