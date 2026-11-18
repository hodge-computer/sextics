import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
namespace CyclicTriple
open Polynomial

variable {R : Type*} [CommRing R]

/-- Monic presentation, in order Y0,Y1,X0,X1,Y2,Z (or X2). -/
def polynomial (k : R) (n m : ℕ) : (MvPolynomial (Fin 5) R)[X] :=
  X^6 + (C (MvPolynomial.C k * (MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 0 +
    MvPolynomial.X 1^2*MvPolynomial.X 0*MvPolynomial.X 3^2 +
    MvPolynomial.X 2*MvPolynomial.X 4^m*MvPolynomial.X 0))*X +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
      MvPolynomial.X 3^6 + MvPolynomial.X 4^n + MvPolynomial.C k *
      (MvPolynomial.X 1^3*MvPolynomial.X 4^m +
       MvPolynomial.X 1*MvPolynomial.X 2*MvPolynomial.X 0^3*MvPolynomial.X 3 +
       MvPolynomial.X 1*MvPolynomial.X 4^m*MvPolynomial.X 0*MvPolynomial.X 3)))

theorem polynomial_monic (k : R) (n m : ℕ) : (polynomial k n m).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

def specialization (eta : R) : MvPolynomial (Fin 5) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X+1, 0, C eta]

theorem polynomial_specialization (k eta : R) (n m : ℕ) (heta : eta^n = -1) :
    (polynomial k n m).map (specialization eta) =
      (X : (R[X])[X])^6 + C ((X+1)^6 - 1) := by
  simp [polynomial, specialization, ← map_pow, heta, sub_eq_add_neg]

theorem polynomial_irreducible [IsDomain R] [CharZero R]
    (k eta : R) (n m : ℕ) (heta : eta^n = -1) :
    Irreducible (polynomial k n m) := by
  apply (polynomial_monic k n m).irreducible_of_irreducible_map (specialization eta)
  rw [polynomial_specialization k eta n m heta]
  exact HoldoutConstruction.irreducible_power_add_constant ((X+1)^6 - 1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

/-- Coordinate order is Y0,Y1,X0,X1,Y2,Z (or X2). -/
def hypersurface (k : R) (n m : ℕ) : MvPolynomial (Fin 6) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
  MvPolynomial.X 3^6 + MvPolynomial.X 4^6 + MvPolynomial.X 5^n +
  MvPolynomial.C k *
    (MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 0*MvPolynomial.X 1 +
     MvPolynomial.X 2^3*MvPolynomial.X 5^m +
     MvPolynomial.X 2^2*MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 4^2 +
     MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 1^3*MvPolynomial.X 4 +
     MvPolynomial.X 2*MvPolynomial.X 5^m*MvPolynomial.X 1*MvPolynomial.X 4 +
     MvPolynomial.X 3*MvPolynomial.X 5^m*MvPolynomial.X 0*MvPolynomial.X 1)

theorem hypersurface_univariate (k : R) (n m : ℕ) :
    MvPolynomial.finSuccEquiv R 5 (hypersurface k n m) = polynomial k n m := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 5) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [hypersurface, polynomial, MvPolynomial.finSuccEquiv_apply, he, Polynomial.C_ofNat]
  ring

theorem hypersurface_irreducible [IsDomain R] [CharZero R]
    (k eta : R) (n m : ℕ) (heta : eta^n = -1) :
    Irreducible (hypersurface k n m) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 5)).mp
  rw [hypersurface_univariate]
  exact polynomial_irreducible k eta n m heta

theorem weighted_quotient_irreducible (k : ℂ) :
    Irreducible (hypersurface k 2 1) :=
  hypersurface_irreducible k Complex.I 2 1 Complex.I_sq

theorem physical_irreducible (k : ℂ) : Irreducible (hypersurface k 6 3) := by
  apply hypersurface_irreducible k Complex.I 6 3
  rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
  norm_num


theorem polynomial_map {S : Type*} [CommRing S] (phi : R →+* S)
    (k : R) (n m : ℕ) :
    (polynomial k n m).map (MvPolynomial.map phi) = polynomial (phi k) n m := by
  simp [polynomial]

theorem weighted_polynomial_adjoinRoot_isDomain (k : ℂ) :
    IsDomain (AdjoinRoot (polynomial k 2 1)) :=
  AdjoinRoot.isDomain_of_prime
    (polynomial_irreducible k Complex.I 2 1 Complex.I_sq).prime

abbrev QuotientRing (k : ℂ) :=
  MvPolynomial (Fin 6) ℂ ⧸ Ideal.span {hypersurface k 2 1}

def quotientMap (k : ℂ) : MvPolynomial (Fin 6) ℂ →+* QuotientRing k :=
  Ideal.Quotient.mk _

theorem quotientMap_surjective (k : ℂ) : Function.Surjective (quotientMap k) :=
  Ideal.Quotient.mk_surjective

theorem quotientMap_kernel (k : ℂ) (p : MvPolynomial (Fin 6) ℂ) :
    quotientMap k p = 0 ↔ hypersurface k 2 1 ∣ p := by
  exact Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

theorem quotientRing_isDomain (k : ℂ) :
    IsDomain (QuotientRing k) := by
  let hdomain : IsDomain ((MvPolynomial (Fin 5) ℂ)[X] ⧸
      Ideal.span {polynomial k 2 1}) := weighted_polynomial_adjoinRoot_isDomain k
  let e := Ideal.quotientEquiv (Ideal.span {hypersurface k 2 1})
    (Ideal.span {polynomial k 2 1})
    (MvPolynomial.finSuccEquiv ℂ 5).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {polynomial k 2 1} =
        Ideal.span {MvPolynomial.finSuccEquiv ℂ 5 (hypersurface k 2 1)}
      rw [hypersurface_univariate])
  exact e.injective.isDomain e.toRingHom

def axis : MvPolynomial (Fin 6) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![X, 0, 0, 0, 0, 0]

theorem axis_equation (k : R) (n m : ℕ) (hn : 0 < n) :
    axis (hypersurface k n m) = X^6 := by
  simp [axis, hypersurface, Nat.ne_of_gt hn]

theorem axis_gradient (k : R) (n m : ℕ) :
    axis (MvPolynomial.pderiv 0 (hypersurface k n m)) = 6*X^5 := by
  norm_num [Derivation.map_natCast, axis, hypersurface, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Polynomial.C_ofNat, Pi.single_apply,
    show (1 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 0 by decide,
    show (3 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 0 by decide,
    show (5 : Fin 6) ≠ 0 by decide]

theorem hypersurface_not_dvd_pderiv_zero [CharZero R]
    (k : R) (n m : ℕ) (hn : 0 < n) :
    ¬ hypersurface k n m ∣ MvPolynomial.pderiv 0 (hypersurface k n m) := by
  intro hd
  have hm := map_dvd (axis (R := R)) hd
  rw [axis_equation k n m hn, axis_gradient] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc


end CyclicTriple

#print axioms CyclicTriple.weighted_quotient_irreducible
#print axioms CyclicTriple.physical_irreducible
