import Proposal.PFrozen
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime

/-!
# Irreducibility of the exact frozen sextic

View F as a polynomial in X0 with leading coefficient 14. The specialization
X1=Y0=Y1=Y2=0, X2=1 is 14 X^6+31, irreducible by Eisenstein at 31 and Gauss's lemma.
The unit leading coefficient prevents specialization from lowering factor degrees.
-/

set_option autoImplicit false
noncomputable section

namespace HodgeTestbed.Descent

open Polynomial

/-- Unit leading coefficient suffices for irreducibility to ascend from a specialization. -/
theorem irreducible_of_unit_leadingCoeff_map {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]) (hf : IsUnit f.leadingCoeff)
    (hmap : Irreducible (f.map φ)) : Irreducible f := by
  refine ⟨hmap.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b hab => ?_⟩
  have habunit : IsUnit (a.leadingCoeff * b.leadingCoeff) := by
    rw [← leadingCoeff_mul, ← hab]
    exact hf
  have hm := hmap.isUnit_or_isUnit
    ((congrArg (Polynomial.map φ) hab).trans (Polynomial.map_mul φ))
  exact hm.imp
    (isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ (isUnit_of_mul_isUnit_left habunit))
    (isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ (isUnit_of_mul_isUnit_right habunit))

namespace FrozenSpecialization

def integerFiber : ℤ[X] := C 14 * X ^ 6 + C 31

theorem integerFiber_degree : integerFiber.degree = 6 := by
  unfold integerFiber
  compute_degree <;> norm_num

theorem integerFiber_leadingCoeff : integerFiber.leadingCoeff = 14 := by
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some integerFiber_degree]
  norm_num [integerFiber]

theorem integerFiber_primitive : integerFiber.IsPrimitive := by
  intro r hr
  have h14 : r ∣ 14 := by
    simpa [integerFiber] using ((C_dvd_iff_dvd_coeff r integerFiber).mp hr) 6
  have h31 : r ∣ 31 := by
    simpa [integerFiber] using ((C_dvd_iff_dvd_coeff r integerFiber).mp hr) 0
  apply isUnit_of_dvd_one
  have hh := dvd_sub (dvd_mul_of_dvd_left h14 20) (dvd_mul_of_dvd_left h31 9)
  norm_num at hh
  exact hh

theorem integerFiber_irreducible : Irreducible integerFiber := by
  apply irreducible_of_eisenstein_criterion (P := Ideal.span ({31} : Set ℤ))
  · apply (Ideal.span_singleton_prime (by norm_num : (31 : ℤ) ≠ 0)).mpr
    norm_num
  · rw [integerFiber_leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro n hn
    rw [integerFiber_degree] at hn
    have hn6 : n ≠ 6 := by exact ne_of_lt (WithBot.coe_lt_coe.mp hn)
    simp only [integerFiber, coeff_add, coeff_C_mul, coeff_X_pow, ite_eq_right hn6, mul_zero,
      zero_add, coeff_C, Ideal.mem_span_singleton]
    split_ifs <;> simp
  · rw [integerFiber_degree]
    decide
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [integerFiber]
  · exact integerFiber_primitive

theorem rationalFiber_irreducible : Irreducible (C (14 : ℚ) * X ^ 6 + C 31) := by
  simpa [integerFiber, map_ofNat] using
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast integerFiber_primitive).mp integerFiber_irreducible

abbrev CoeffRing := MvPolynomial (Fin 5) ℚ

/-- Separate X0 from the other five variables. -/
def asPolynomial : CoeffRing[X] := MvPolynomial.finSuccEquiv ℚ 5 Frozen.F

/-- The coefficient specialization leaves only X2=1. -/
def coefficientPoint (i : Fin 5) : ℚ := if i = 1 then 1 else 0

private theorem variable1_image :
    MvPolynomial.finSuccEquiv ℚ 5 (MvPolynomial.X (1 : Fin 6)) =
      C (MvPolynomial.X (0 : Fin 5)) := by
  exact MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 5) (j := (0 : Fin 5))

private theorem variable2_image :
    MvPolynomial.finSuccEquiv ℚ 5 (MvPolynomial.X (2 : Fin 6)) =
      C (MvPolynomial.X (1 : Fin 5)) := by
  exact MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 5) (j := (1 : Fin 5))

private theorem variable3_image :
    MvPolynomial.finSuccEquiv ℚ 5 (MvPolynomial.X (3 : Fin 6)) =
      C (MvPolynomial.X (2 : Fin 5)) := by
  exact MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 5) (j := (2 : Fin 5))

private theorem variable4_image :
    MvPolynomial.finSuccEquiv ℚ 5 (MvPolynomial.X (4 : Fin 6)) =
      C (MvPolynomial.X (3 : Fin 5)) := by
  exact MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 5) (j := (3 : Fin 5))

private theorem variable5_image :
    MvPolynomial.finSuccEquiv ℚ 5 (MvPolynomial.X (5 : Fin 6)) =
      C (MvPolynomial.X (4 : Fin 5)) := by
  exact MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 5) (j := (4 : Fin 5))

theorem asPolynomial_degree : asPolynomial.natDegree = 6 := by
  simp only [asPolynomial, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, map_add, map_mul, map_pow, map_ofNat, MvPolynomial.finSuccEquiv_X_zero,
    variable1_image, variable2_image, variable3_image, variable4_image, variable5_image]
  compute_degree <;> norm_num

theorem asPolynomial_leadingCoeff : asPolynomial.leadingCoeff = 14 := by
  rw [leadingCoeff, asPolynomial_degree]
  simp only [asPolynomial, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, map_add, map_mul, map_pow, map_ofNat, MvPolynomial.finSuccEquiv_X_zero,
    variable1_image, variable2_image, variable3_image, variable4_image, variable5_image]
  compute_degree <;> norm_num

theorem specialization_eq : asPolynomial.map (MvPolynomial.eval coefficientPoint) =
    C (14 : ℚ) * X ^ 6 + C 31 := by
  simp only [asPolynomial, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, map_add, map_mul, map_pow, map_ofNat,
    MvPolynomial.finSuccEquiv_X_zero, variable1_image, variable2_image,
    variable3_image, variable4_image, variable5_image]
  norm_num [coefficientPoint, Fin.ext_iff, map_ofNat]

theorem asPolynomial_irreducible : Irreducible asPolynomial := by
  apply irreducible_of_unit_leadingCoeff_map (MvPolynomial.eval coefficientPoint)
  · rw [asPolynomial_leadingCoeff]
    simpa only [map_ofNat] using
      (show IsUnit (14 : ℚ) from isUnit_iff_ne_zero.mpr (by norm_num)).map MvPolynomial.C
  · rw [specialization_eq]
    exact rationalFiber_irreducible

end FrozenSpecialization

/-- The exact frozen twenty-term sextic is irreducible over QQ. -/
theorem frozen_irreducible : Irreducible Frozen.F := by
  exact (MulEquiv.irreducible_iff (f := (MvPolynomial.finSuccEquiv ℚ 5).toRingEquiv.toMulEquiv)).mp
    FrozenSpecialization.asPolynomial_irreducible

/-- For the frozen F, denominator legality reduces to nondivisibility by F. -/
theorem frozen_denominator_legal_iff (D : SexticPoly) :
    DenominatorLegal Frozen.F D ↔ ¬ Frozen.F ∣ D := by
  exact frozen_irreducible.isRelPrime_iff_not_dvd

/-- Nonzero reduction modulo F is exactly denominator legality for the frozen instance. -/
theorem frozen_denominator_legal_iff_quotient_ne_zero (D : SexticPoly) :
    DenominatorLegal Frozen.F D ↔
      Ideal.Quotient.mk (Ideal.span ({Frozen.F} : Set SexticPoly)) D ≠ 0 := by
  rw [frozen_denominator_legal_iff, ne_eq, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

end HodgeTestbed.Descent
