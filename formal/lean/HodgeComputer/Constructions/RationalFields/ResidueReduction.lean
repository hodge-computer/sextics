import HodgeComputer.Constructions.RationalFields.Calculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-!
# The explicit residue-to-field correction

For alpha=i_T(volume), the primitive equation d(alpha/H²)=A*volume/H² is
H*div(T)-2*T(H)=A*H. A normal field n with n(H)=1 then supplies the displayed
bracket correction. Its divergence is proved, never postulated.
-/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Conic

variable {ι R : Type*} [Fintype ι] [Field R] [CharZero R] [Algebra ℚ R]

/-- Derivations annihilate the constant factor one half. -/
theorem derivation_half (D : Derivation ℚ R R) (f : R) : D (f / 2) = D f / 2 := by
  have htwo : D (2 : R) = 0 := D.map_natCast 2
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    htwo, smul_eq_mul, mul_zero]
  ring

def residueScalar (δ : ι → Derivation ℚ R R) (A : R) (T : ι → R) : R :=
  (fieldDivergence δ T - A) / 2

/-- W=[n,T]+div(n)*T-(div(T)+A)*n/2, with the reviewed contraction sign. -/
def residueCorrection (δ : ι → Derivation ℚ R R) (A : R) (n T : ι → R) (i : ι) : R :=
  fieldBracket δ n T i + fieldDivergence δ n * T i -
    ((fieldDivergence δ T + A) / 2) * n i

/-- The actual divergence of the residue correction is div(S*n). -/
theorem residueCorrection_divergence (δ : ι → Derivation ℚ R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (A : R) (n T : ι → R) :
    fieldDivergence δ (residueCorrection δ A n T) =
      fieldDivergence δ (fun i => residueScalar δ A T * n i) := by
  unfold residueCorrection
  rw [fieldDivergence_sub, fieldDivergence_add, fieldDivergence_bracket δ hcomm,
    fieldDivergence_scale, fieldDivergence_scale, fieldDivergence_scale]
  simp only [residueScalar, derivation_half, map_add, map_sub]
  ring

/-- The primitive relation makes the contraction H*S. -/
theorem residue_contraction (δ : ι → Derivation ℚ R R) (H A : R) (T : ι → R)
    (hprimitive : H * fieldDivergence δ T - 2 * fieldAction δ T H = A * H) :
    fieldAction δ T H = H * residueScalar δ A T := by
  unfold residueScalar
  linear_combination -(1 / 2 : R) * hprimitive

/-- The actual contraction of W, using its explicit bracket formula. -/
theorem residueCorrection_contraction (δ : ι → Derivation ℚ R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (H A : R) (n T : ι → R)
    (hn : fieldAction δ n H = 1)
    (hprimitive : H * fieldDivergence δ T - 2 * fieldAction δ T H = A * H) :
    fieldAction δ (residueCorrection δ A n T) H =
      -A + H * fieldDivergence δ (fun i => residueScalar δ A T * n i) := by
  have hT := residue_contraction δ H A T hprimitive
  unfold residueCorrection
  rw [fieldAction_sub, fieldAction_add, fieldAction_bracket δ hcomm,
    fieldAction_scale, fieldAction_scale, hn, hT,
    Derivation.map_one_eq_zero, fieldDivergence_scale]
  simp only [Derivation.leibniz, smul_eq_mul, hn, residueScalar]
  ring

/-- Negating W gives the exact unnormalized game identity. -/
theorem residueCorrection_game (δ : ι → Derivation ℚ R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (H A : R) (n T : ι → R)
    (hn : fieldAction δ n H = 1)
    (hprimitive : H * fieldDivergence δ T - 2 * fieldAction δ T H = A * H) :
    A - fieldAction δ (fun i => -residueCorrection δ A n T i) H +
      H * fieldDivergence δ (fun i => -residueCorrection δ A n T i) = 0 := by
  have hc := residueCorrection_contraction δ hcomm H A n T hn hprimitive
  have hd := residueCorrection_divergence δ hcomm A n T
  have ha : fieldAction δ (fun i => -residueCorrection δ A n T i) H =
      -fieldAction δ (residueCorrection δ A n T) H := by
    simp only [fieldAction_apply, neg_mul, Finset.sum_neg_distrib]
  have hv : fieldDivergence δ (fun i => -residueCorrection δ A n T i) =
      -fieldDivergence δ (residueCorrection δ A n T) := by
    simp only [fieldDivergence, map_neg, Finset.sum_neg_distrib]
  rw [ha, hv, hc, hd]
  ring

end HodgeTestbed.Conic
