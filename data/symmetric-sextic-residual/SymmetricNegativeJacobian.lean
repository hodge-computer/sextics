import Proposal.WeightedFiberSmoothness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Twelve independent negative Jacobian directions for the exact weighted fiber

The polynomial is the already bound `WeightedFiberSmoothness.weightedG` at
lambda = 1.  The columns are the actual partial derivatives multiplied by
`c,d,c,d,a,b,a,b,ac,ad,bc,bd`, respectively.  A selected coefficient minor
of their integral counterparts is diagonal after reduction modulo five.
This proves independence over C without evaluating a large determinant.

No contact curve, Hodge comparison, or rational primitive is assumed here.
-/

noncomputable section

namespace SymmetricNegativeJacobian

open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev IntPoly := MvPolynomial (Fin 5) ℤ
abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev ModPoly := MvPolynomial (Fin 5) (ZMod 5)

def partialIndex : Fin 12 → Fin 5 := ![0,0,1,1,2,2,3,3,4,4,4,4]

def multiplier : Fin 12 → IntPoly :=
  ![X 2, X 3, X 2, X 3, X 0, X 1, X 0, X 1,
    X 0 * X 2, X 0 * X 3, X 1 * X 2, X 1 * X 3]

def integerDirection (j : Fin 12) : IntPoly :=
  multiplier j * pderiv (partialIndex j) WeightedFiberSmoothness.integerWeighted

/-- The twelve actual polynomial Jacobian directions, over the target field. -/
def direction (j : Fin 12) : Poly :=
  map (Int.castRingHom ℂ) (multiplier j) *
    pderiv (partialIndex j) WeightedFiberSmoothness.weightedG

def exponent : Fin 12 → (Fin 5 →₀ ℕ) :=
  ![Finsupp.single 0 5 + Finsupp.single 2 1,
    Finsupp.single 0 5 + Finsupp.single 3 1,
    Finsupp.single 1 5 + Finsupp.single 2 1,
    Finsupp.single 1 5 + Finsupp.single 3 1,
    Finsupp.single 0 1 + Finsupp.single 2 5,
    Finsupp.single 1 1 + Finsupp.single 2 5,
    Finsupp.single 0 1 + Finsupp.single 3 5,
    Finsupp.single 1 1 + Finsupp.single 3 5,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 4 2,
    Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 2,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 4 2,
    Finsupp.single 1 1 + Finsupp.single 3 1 + Finsupp.single 4 2]

def modDiagonal : Fin 12 → ZMod 5 := ![4,4,2,2,4,4,2,2,4,4,4,4]

def encodeExponent (e : Fin 5 →₀ ℕ) : ℕ :=
  e 0 + 8 * e 1 + 64 * e 2 + 512 * e 3 + 4096 * e 4

def exponentCode : Fin 12 → ℕ :=
  ![69,517,104,552,321,328,2561,2568,8257,8705,8264,8712]

theorem exponent_code (j : Fin 12) : encodeExponent (exponent j) = exponentCode j := by
  fin_cases j <;> norm_num [encodeExponent, exponent, exponentCode,
    Finsupp.single_apply, Fin.ext_iff]

theorem exponent_injective : Function.Injective exponent := by
  have hinj : Function.Injective exponentCode := by decide
  intro i j h
  apply hinj
  simpa only [exponent_code] using congrArg encodeExponent h

theorem integerWeighted_mod_five :
    map (Int.castRingHom (ZMod 5)) WeightedFiberSmoothness.integerWeighted =
      C 4 * X 0 ^ 6 + C 2 * X 1 ^ 6 + C 4 * X 2 ^ 6 +
        C 2 * X 3 ^ 6 + C 3 * X 4 ^ 3 := by
  have : CharP ModPoly 5 := inferInstance
  norm_num [WeightedFiberSmoothness.integerWeighted,
    WeightedFiberSmoothness.leftQuadric, WeightedFiberSmoothness.rightQuadric,
    map_ofNat] <;> ring_nf <;> reduce_mod_char! <;> rfl

theorem integerDirection_mod_five (j : Fin 12) :
    map (Int.castRingHom (ZMod 5)) (integerDirection j) =
      monomial (exponent j) (modDiagonal j) := by
  have : CharP ModPoly 5 := inferInstance
  rw [integerDirection, map_mul, ← pderiv_map, integerWeighted_mod_five]
  have hd2 (i : Fin 5) : pderiv i (2 : ModPoly) = 0 :=
    Derivation.map_natCast _ 2
  have hd3 (i : Fin 5) : pderiv i (3 : ModPoly) = 0 :=
    Derivation.map_natCast _ 3
  have hd4 (i : Fin 5) : pderiv i (4 : ModPoly) = 0 :=
    Derivation.map_natCast _ 4
  fin_cases j <;>
    simp [multiplier, partialIndex, exponent, modDiagonal,
      pderiv_C_mul, pderiv_pow, pderiv_X, hd2, hd3, hd4,
      Pi.single_apply, monomial_add_single, ← C_mul_X_pow_eq_monomial] <;>
    norm_num [Fin.ext_iff, map_ofNat] <;> ring_nf <;> reduce_mod_char! <;> rfl

/-- The minor uses coefficients of the actual twelve integral polynomials. -/
def integerMinor : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j => coeff (exponent i) (integerDirection j)

theorem integerMinor_mod_five :
    integerMinor.map (Int.castRingHom (ZMod 5)) = Matrix.diagonal modDiagonal := by
  ext i j
  change (Int.castRingHom (ZMod 5)) (coeff (exponent i) (integerDirection j)) = _
  rw [← coeff_map, integerDirection_mod_five, coeff_monomial]
  have he : exponent j = exponent i ↔ i = j := by
    constructor
    · exact fun h => (exponent_injective h).symm
    · rintro rfl; rfl
  by_cases h : i = j
  · subst j; simp [Matrix.diagonal]
  · simp [he, Matrix.diagonal, h, Ne.symm h]

theorem integerMinor_det_mod_five :
    (Int.castRingHom (ZMod 5)) integerMinor.det = 1 := by
  rw [RingHom.map_det]
  change (integerMinor.map (Int.castRingHom (ZMod 5))).det = 1
  rw [integerMinor_mod_five, Matrix.det_diagonal]
  decide

theorem integerMinor_det_ne_zero : integerMinor.det ≠ 0 := by
  intro h
  have hn := integerMinor_det_mod_five
  rw [h, map_zero] at hn
  exact zero_ne_one hn

theorem direction_eq_scaled (j : Fin 12) :
    direction j = (1 / 13 : ℂ) • map (Int.castRingHom ℂ) (integerDirection j) := by
  simp only [direction, WeightedFiberSmoothness.weightedG, pderiv_C_mul,
    pderiv_map, integerDirection, map_mul, smul_eq_C_mul]
  ring

def selectedCoefficients : Poly →ₗ[ℂ] (Fin 12 → ℂ) :=
  LinearMap.pi fun i => lcoeff ℂ (exponent i)

theorem mapped_integerDirection_independent :
    LinearIndependent ℂ (fun j => map (Int.castRingHom ℂ) (integerDirection j)) := by
  have hdet : (integerMinor.map (Int.castRingHom ℂ)).det ≠ 0 := by
    change ((Int.castRingHom ℂ).mapMatrix integerMinor).det ≠ 0
    rw [← RingHom.map_det]
    change (integerMinor.det : ℂ) ≠ 0
    exact_mod_cast integerMinor_det_ne_zero
  apply LinearIndependent.of_comp selectedCoefficients
  have heq : selectedCoefficients ∘
      (fun j => map (Int.castRingHom ℂ) (integerDirection j)) =
      (integerMinor.map (Int.castRingHom ℂ)).col := by
    funext j i
    simp [selectedCoefficients, integerMinor, Matrix.col, coeff_map]
  rw [heq]
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

/-- No nontrivial complex linear combination of the twelve actual directions is zero. -/
theorem direction_independent : LinearIndependent ℂ direction := by
  have h := mapped_integerDirection_independent.units_smul
    (fun _ => Units.mk0 (1 / 13 : ℂ) (by norm_num))
  convert h using 1
  funext j
  exact direction_eq_scaled j

theorem direction_span_finrank :
    Module.finrank ℂ (Submodule.span ℂ (Set.range direction)) = 12 := by
  simpa using finrank_span_eq_card direction_independent

#print axioms integerDirection_mod_five
#print axioms integerMinor_det_ne_zero
#print axioms direction_independent
#print axioms direction_span_finrank

end SymmetricNegativeJacobian
