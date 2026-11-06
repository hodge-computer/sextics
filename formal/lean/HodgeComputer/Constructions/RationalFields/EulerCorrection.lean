import HodgeComputer.Constructions.RationalFields.ResidueReduction

/-! Extracted from `benediamond`’s accepted two-ternary dense Hessian
construction. The application and its mathematical credit are linked in README.md. -/


/-!
# Homogeneous Euler correction of the actual raw field

The degree-zero premise is E(div(v))=0. With E(F)=6F and div(E)=6,
the displayed correction turns the raw game identity into strict contraction
and zero divergence. It does not assume either desired conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Conic

variable {ι R : Type*} [Fintype ι] [Field R] [CharZero R] [Algebra ℚ R]

/-- Derivations annihilate the constant factor one sixth. -/
theorem derivation_sixth (D : Derivation ℚ R R) (f : R) : D (f / 6) = D f / 6 := by
  have hsix : D (6 : R) = 0 := D.map_natCast 6
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    hsix, smul_eq_mul, mul_zero]
  ring

def eulerCorrection (δ : ι → Derivation ℚ R R) (E v : ι → R) (i : ι) : R :=
  v i - (fieldDivergence δ v / 6) * E i

/-- The exact Euler subtraction yields both strict equations. -/
theorem eulerCorrection_strict (δ : ι → Derivation ℚ R R) (F A : R) (E v : ι → R)
    (hF : fieldAction δ E F = 6 * F) (hE : fieldDivergence δ E = 6)
    (hdegree : fieldAction δ E (fieldDivergence δ v) = 0)
    (hgame : A - fieldAction δ v F + F * fieldDivergence δ v = 0) :
    fieldAction δ (eulerCorrection δ E v) F = A ∧
      fieldDivergence δ (eulerCorrection δ E v) = 0 := by
  constructor
  · unfold eulerCorrection
    rw [fieldAction_sub, fieldAction_scale, hF]
    linear_combination -hgame
  · unfold eulerCorrection
    rw [fieldDivergence_sub, fieldDivergence_scale, derivation_sixth, hdegree, hE]
    ring

/-- The reviewed residue correction followed by Euler subtraction is strict,
under the explicit Euler degree-zero condition on its raw divergence. -/
theorem residue_euler_strict (δ : ι → Derivation ℚ R R)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j)) (F A : R) (n T E : ι → R)
    (hn : fieldAction δ n F = 1)
    (hprimitive : F * fieldDivergence δ T - 2 * fieldAction δ T F = A * F)
    (hF : fieldAction δ E F = 6 * F) (hE : fieldDivergence δ E = 6)
    (hdegree : fieldAction δ E
      (fieldDivergence δ (fun i => -residueCorrection δ A n T i)) = 0) :
    fieldAction δ (eulerCorrection δ E (fun i => -residueCorrection δ A n T i)) F = A ∧
      fieldDivergence δ (eulerCorrection δ E (fun i => -residueCorrection δ A n T i)) = 0 :=
  eulerCorrection_strict δ F A E _ hF hE hdegree
    (residueCorrection_game δ hcomm F A n T hn hprimitive)

end HodgeTestbed.Conic
