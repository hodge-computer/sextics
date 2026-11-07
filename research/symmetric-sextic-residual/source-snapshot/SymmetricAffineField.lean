import SymmetricAffinePrime
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The function field of the actual reflection chart

Primality is supplied by `SymmetricAffinePrime`, not an application input.
The normal derivative is nonzero in the quotient: at the explicit complex
point `(lambda,b,c,d,v)=(0,0,0,0,I)`, the equation is zero and its v-derivative
is `-48*I`.  Consequently the canonical normal denominator is legal on a
nonempty open of this specific hypersurface.
-/

noncomputable section

namespace SymmetricAffineField

open MvPolynomial
open WeightedPrimitiveTransport

set_option maxHeartbeats 2000000

def equationIdeal : Ideal Poly := Ideal.span {chartEquation}
abbrev CoordinateRing := Poly ⧸ equationIdeal

instance equationIdeal_prime : equationIdeal.IsPrime :=
  (Ideal.span_singleton_prime SymmetricAffinePrime.chart_irreducible.ne_zero).mpr
    SymmetricAffinePrime.chart_prime

instance coordinateRing_isDomain : IsDomain CoordinateRing :=
  Ideal.Quotient.isDomain _

/-- A type wrapper makes the field and scalar instances coherent. -/
def FunctionField := FractionRing CoordinateRing

instance functionField_field : Field FunctionField :=
  inferInstanceAs (Field (FractionRing CoordinateRing))

instance functionField_algebra : Algebra CoordinateRing FunctionField :=
  inferInstanceAs (Algebra CoordinateRing (FractionRing CoordinateRing))

instance functionField_isFractionRing : IsFractionRing CoordinateRing FunctionField :=
  inferInstanceAs (IsFractionRing CoordinateRing (FractionRing CoordinateRing))

def quotient : Poly →+* CoordinateRing := Ideal.Quotient.mk equationIdeal

def residueMap : Poly →+* FunctionField :=
  (algebraMap CoordinateRing FunctionField).comp quotient

instance functionField_charZero : CharZero FunctionField :=
  charZero_of_injective_ringHom (residueMap.comp (C : ℂ →+* Poly)).injective

theorem quotient_surjective : Function.Surjective quotient :=
  Ideal.Quotient.mk_surjective

theorem quotient_kernel (p : Poly) : quotient p = 0 ↔ chartEquation ∣ p := by
  rw [quotient, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton

theorem residueMap_kernel (p : Poly) : residueMap p = 0 ↔ chartEquation ∣ p := by
  rw [residueMap, RingHom.comp_apply, map_eq_zero_iff _
    (IsFractionRing.injective CoordinateRing FunctionField)]
  exact quotient_kernel p

def normalPoint : Fin 5 → ℂ := ![0,0,0,0,Complex.I]

theorem normalPoint_equation : eval normalPoint chartEquation = 0 := by
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2)^3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  norm_num [normalPoint, chartEquation, rawWeighted, leftQuadric, rightQuadric,
    Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Complex.I_sq, hi6]

theorem normalPoint_derivative : eval normalPoint (pderiv 4 chartEquation) =
    -48 * Complex.I := by
  rw [chartEquation, normal_squareLift]
  norm_num [normalPoint, rawWeighted, leftQuadric, rightQuadric,
    pderiv_pow, pderiv_mul, Pi.single_apply, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Complex.I_sq, map_ofNat]
  ring

theorem equation_not_dvd_normal : ¬ chartEquation ∣ pderiv 4 chartEquation := by
  intro hd
  have h := map_dvd (eval normalPoint) hd
  rw [normalPoint_equation, normalPoint_derivative, zero_dvd_iff] at h
  exact (mul_ne_zero (by norm_num : (-48 : ℂ) ≠ 0) Complex.I_ne_zero) h

theorem normal_nonzero : residueMap (pderiv 4 chartEquation) ≠ 0 := by
  rw [ne_eq, residueMap_kernel]
  exact equation_not_dvd_normal

theorem cover_coordinate_nonzero : residueMap (X 4) ≠ 0 :=
  (normal_nonzero_factors residueMap rawWeighted normal_nonzero).1

theorem weighted_normal_nonzero :
    residueMap (squareLift (pderiv 4 rawWeighted)) ≠ 0 :=
  (normal_nonzero_factors residueMap rawWeighted normal_nonzero).2

#print axioms coordinateRing_isDomain
#print axioms normal_nonzero
#print axioms weighted_normal_nonzero

end SymmetricAffineField
