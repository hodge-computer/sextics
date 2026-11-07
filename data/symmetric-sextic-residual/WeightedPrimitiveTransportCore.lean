import Proposal.SymmetricReflections
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Basic

/-!
# A relative primitive gives the actual reflection-chart residue current

The chart coordinates are `(lambda,b,c,d,v)`; the weighted coordinates use
`u` in the last position. The equation is `H=f(lambda,b,c,d,v^2)` and the
actual transformed source is `A_H=4*v*P(lambda,b,c,d,v^2)`, where
`P=b*d*(1-u)*(c^2-lambda^2*u)`.

Given the three coefficients of a relative two-form whose differential is
the displayed residue three-form, the current is explicitly
`w=(0,-H_v*beta_0,-H_v*beta_1,-H_v*beta_2)`. The zero lambda component is the
coefficient version of wedging with `d lambda`; no derivative in lambda is
integrated or assumed to vanish. The weighted-divergence equation is proved
by the product rule, and the repository's canonical tangent and finite-trace
clearing theorem then supplies legal polynomial data on this chart.

Existence of the relative primitive is an explicit remaining hypothesis.
No assertion of a current or certificate for the protected equation is
assumed. The final projective/coordinate transport is separate.
-/

noncomputable section

namespace WeightedPrimitiveTransport

open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial (Fin 5) ℂ

/-- The last coordinate is squared; all other coordinates are retained. -/
def squareLift : Poly →+* Poly :=
  eval₂Hom C (fun i => if i = 4 then X i ^ 2 else X i)

@[simp] theorem squareLift_C (r : ℂ) : squareLift (C r) = C r := by
  exact eval₂Hom_C _ _ _

@[simp] theorem squareLift_X (i : Fin 5) :
    squareLift (X i) = if i = 4 then X i ^ 2 else X i := by
  exact eval₂Hom_X' _ _ _

/-- Exact chain rule for the normal coordinate of the reflection cover. -/
theorem normal_squareLift (p : Poly) :
    pderiv 4 (squareLift p) = C 2 * X 4 * squareLift (pderiv 4 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
    by_cases hj : j = 4
    · subst j
      simp only [map_mul, squareLift_X, if_pos rfl, pderiv_mul,
        pderiv_pow, pderiv_X_self, hp, map_add, map_mul, map_one,
        ite_true]
      norm_num [map_ofNat, pderiv_pow, pderiv_X_self]
      ring
    · simp only [map_mul, squareLift_X, if_neg hj, pderiv_mul,
        pderiv_X_of_ne hj, hp, map_add, map_mul, map_zero,
        mul_zero, add_zero]
      ring

theorem second_normal_squareLift (p : Poly) :
    pderiv 4 (pderiv 4 (squareLift p)) =
      C 2 * squareLift (pderiv 4 p) +
        C 4 * X 4 ^ 2 * squareLift (pderiv 4 (pderiv 4 p)) := by
  rw [normal_squareLift]
  simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, pderiv_X_self,
    mul_one, normal_squareLift]
  norm_num [map_ofNat]
  ring

def reflectedSource (p : Poly) : Poly := C 4 * X 4 * squareLift p

theorem normal_reflectedSource (p : Poly) :
    pderiv 4 (reflectedSource p) =
      C 4 * squareLift p + C 8 * X 4 ^ 2 * squareLift (pderiv 4 p) := by
  simp only [reflectedSource, pderiv_mul, pderiv_C, zero_mul, zero_add,
    pderiv_X_self, mul_one, normal_squareLift]
  norm_num [map_ofNat]
  ring

/-! ## The actual protected equation and numerator on this chart -/

def leftQuadric : Poly := 1 + C 2 * X 1 - X 4
def rightQuadric : Poly := X 2 ^ 2 + C 2 * X 2 * X 3 - X 0 ^ 2 * X 4

def rawWeighted : Poly :=
  C 2 + X 1 ^ 6 + C 2 * X 2 ^ 6 + X 3 ^ 6 +
    C 30 * X 4 + C 30 * X 4 ^ 2 + C 2 * X 4 ^ 3 +
    C 30 * X 0 ^ 2 * X 2 ^ 4 * X 4 +
    C 30 * X 0 ^ 4 * X 2 ^ 2 * X 4 ^ 2 + C 2 * X 0 ^ 6 * X 4 ^ 3 +
    C (5/7 : ℂ) * leftQuadric ^ 2 * rightQuadric +
    C (10/7 : ℂ) * leftQuadric * rightQuadric ^ 2

def rawSource : Poly := X 1 * X 3 * (1-X 4) * (X 2 ^ 2-X 0 ^ 2*X 4)
def chartEquation : Poly := squareLift rawWeighted
def chartSource : Poly := reflectedSource rawSource

theorem exact_chart_equation (lam b c d v : ℂ) :
    eval ![lam,b,c,d,v] chartEquation =
      eval ![1+v,1-v,b,c+lam*v,c-lam*v,d] HodgeSubmission.F := by
  change _ = SymmetricReflections.transformedF 1 b c d v (lam*v)
  rw [SymmetricReflections.transformedF_formula]
  simp [chartEquation, rawWeighted, leftQuadric, rightQuadric,
    squareLift, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  ring

theorem exact_chart_source (lam b c d v : ℂ) :
    eval ![lam,b,c,d,v] chartSource =
      4*v*eval ![1+v,1-v,b,c+lam*v,c-lam*v,d] HodgeSubmission.A := by
  change _ = 4*v*SymmetricReflections.transformedA 1 b c d v (lam*v)
  rw [SymmetricReflections.transformedA_formula]
  simp [chartSource, reflectedSource, rawSource, squareLift, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring
  all_goals simp

/-! ## The exact residue coefficient and its normalization -/

section FieldIdentities

variable {K : Type*} [Field K] [CharZero K]

/-- Cancellation uses both the monic equation factor and the source factor.
Omitting `ell^-2` from the source would give a different expression. -/
theorem monic_residue_coefficient (ell fu fuu p pu : K)
    (hell : ell ≠ 0) (hfu : fu ≠ 0) :
    ((fu/ell)*(2*pu/ell^2)-(fuu/ell)*(2*p/ell^2))/(fu/ell)^3 =
      2*(fu*pu-fuu*p)/fu^3 := by
  field_simp
  <;> ring

def residueCoefficient (σ : Poly →+* K) (f p : Poly) : K :=
  2 * (σ (squareLift (pderiv 4 f)) * σ (squareLift (pderiv 4 p)) -
    σ (squareLift (pderiv 4 (pderiv 4 f))) * σ (squareLift p)) /
    (σ (squareLift (pderiv 4 f)))^3

theorem normal_nonzero_factors (σ : Poly →+* K) (f : Poly)
    (hg : σ (pderiv 4 (squareLift f)) ≠ 0) :
    σ (X 4) ≠ 0 ∧ σ (squareLift (pderiv 4 f)) ≠ 0 := by
  rw [normal_squareLift, map_mul, map_mul, map_ofNat] at hg
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hg).1).2,
    (mul_ne_zero_iff.mp hg).2⟩

/-- This binds the double-pole source to the canonical normal-residue scalar.
It is an identity for the actual polynomial derivatives, not an assumed
match between unnamed differential forms. -/
theorem exact_reflected_residue_scalar (σ : Poly →+* K) (f p : Poly)
    (hg : σ (pderiv 4 (squareLift f)) ≠ 0) :
    (σ (pderiv 4 (reflectedSource p)) * σ (pderiv 4 (squareLift f)) -
      σ (reflectedSource p) * σ (pderiv 4 (pderiv 4 (squareLift f)))) /
        (σ (pderiv 4 (squareLift f)))^2 =
      σ (pderiv 4 (squareLift f)) * residueCoefficient σ f p := by
  obtain ⟨hv,hu⟩ := normal_nonzero_factors σ f hg
  rw [normal_reflectedSource, second_normal_squareLift]
  simp only [normal_squareLift, reflectedSource, residueCoefficient,
    map_add, map_mul, map_pow, map_ofNat]
  field_simp
  <;> ring

/-- Coefficients of `-d lambda wedge beta`, expressed with the residue density.
There is no lambda component, even when the other coefficients depend on it. -/
def relativeCurrent (g : K) (beta : Fin 3 → K) : Fin 4 → K :=
  Fin.cases 0 (fun i => -g*beta i)

theorem weighted_derivative (E : Derivation ℤ K K) (g b : K) (hg : g ≠ 0) :
    E (-g*b) - (-g*b)*E g/g = -g*E b := by
  simp only [Derivation.leibniz, map_neg, smul_eq_mul]
  field_simp
  <;> ring

/-- The three relative primitive coefficients construct an exact four-coordinate
weighted-divergence solution. No derivative of beta in lambda occurs. -/
theorem relativeCurrent_equation (E : Fin 4 → Derivation ℤ K K)
    (g rho : K) (beta : Fin 3 → K) (hg : g ≠ 0)
    (hprimitive : ∑ i : Fin 3, E i.succ (beta i) = rho) :
    g*rho + ∑ i : Fin 4,
      (E i (relativeCurrent g beta i) -
        relativeCurrent g beta i * E i g/g) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [relativeCurrent, Fin.cases_zero, Fin.cases_succ, map_zero,
    zero_mul, zero_div, sub_self, zero_add]
  simp_rw [weighted_derivative _ _ _ hg]
  rw [← Finset.mul_sum, hprimitive]
  ring

end FieldIdentities

#print axioms normal_squareLift
#print axioms exact_chart_equation
#print axioms exact_chart_source
#print axioms monic_residue_coefficient
#print axioms exact_reflected_residue_scalar
#print axioms relativeCurrent_equation

end WeightedPrimitiveTransport
