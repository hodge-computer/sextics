import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
namespace ReflectionCoupledFano
open Polynomial

variable {R : Type*} [CommRing R]

/-- `n=6,m=2` is the physical sextic; `n=3,m=1` is its weighted quotient.
The outer variable is X0 and the coefficient order is X1,X2,Y0,Y1,z. -/
def polynomial (k : R) (n m : ℕ) : (MvPolynomial (Fin 5) R)[X] :=
  X^6 +
    (C (MvPolynomial.C k * MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3) * X^3 +
    C (MvPolynomial.C k *
      (MvPolynomial.X 0 * MvPolynomial.X 2^3 * MvPolynomial.X 3 +
       MvPolynomial.X 0 * MvPolynomial.X 2^2 * MvPolynomial.X 4^m +
       2 * MvPolynomial.X 0 * MvPolynomial.X 3^2 * MvPolynomial.X 4^m +
       3 * MvPolynomial.X 1^3 * MvPolynomial.X 2 * MvPolynomial.X 3)) * X +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
       MvPolynomial.X 3^6 + MvPolynomial.X 4^n +
       MvPolynomial.C k *
         (2 * MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3^3)))

theorem polynomial_monic (k : R) (n m : ℕ) : (polynomial k n m).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
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

/-- Coordinate order is X0,X1,X2,Y0,Y1,z. -/
def hypersurface (k : R) (n m : ℕ) : MvPolynomial (Fin 6) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
  MvPolynomial.X 3^6 + MvPolynomial.X 4^6 + MvPolynomial.X 5^n +
  MvPolynomial.C k *
    (MvPolynomial.X 0^3*MvPolynomial.X 1*MvPolynomial.X 3*MvPolynomial.X 4 +
     MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 3^3*MvPolynomial.X 4 +
     MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 3^2*MvPolynomial.X 5^m +
     2*MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 4^2*MvPolynomial.X 5^m +
     3*MvPolynomial.X 0*MvPolynomial.X 2^3*MvPolynomial.X 3*MvPolynomial.X 4 +
     2*MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4 +
     MvPolynomial.X 1*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4^3)

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

theorem weighted_quotient_irreducible [IsDomain R] [CharZero R] (k : R) :
    Irreducible (hypersurface k 3 1) :=
  hypersurface_irreducible k (-1) 3 1 (by norm_num)

theorem physical_irreducible (k : ℂ) : Irreducible (hypersurface k 6 2) := by
  apply hypersurface_irreducible k Complex.I 6 2
  rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
  norm_num


theorem polynomial_map {S : Type*} [CommRing S] (phi : R →+* S)
    (k : R) (n m : ℕ) :
    (polynomial k n m).map (MvPolynomial.map phi) = polynomial (phi k) n m := by
  simp [polynomial]

theorem weighted_polynomial_adjoinRoot_isDomain [IsDomain R] [CharZero R]
    (k : R) : IsDomain (AdjoinRoot (polynomial k 3 1)) := by
  let phi : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hphi : Function.Injective phi := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((polynomial k 3 1).map (MvPolynomial.map phi))) := by
    rw [polynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (polynomial_irreducible (phi k) (-1) 3 1 (by norm_num)).prime
  let := hmap
  exact HoldoutConstruction.adjoinRoot_isDomain_of_monic_map (MvPolynomial.map phi)
    (MvPolynomial.map_injective phi hphi) _ (polynomial_monic k 3 1)

abbrev QuotientRing (k : R) :=
  MvPolynomial (Fin 6) R ⧸ Ideal.span {hypersurface k 3 1}

def quotientMap (k : R) : MvPolynomial (Fin 6) R →+* QuotientRing k :=
  Ideal.Quotient.mk _

theorem quotientMap_surjective (k : R) : Function.Surjective (quotientMap k) :=
  Ideal.Quotient.mk_surjective

theorem quotientMap_kernel (k : R) (p : MvPolynomial (Fin 6) R) :
    quotientMap k p = 0 ↔ hypersurface k 3 1 ∣ p := by
  exact Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

theorem quotientRing_isDomain [IsDomain R] [CharZero R] (k : R) :
    IsDomain (QuotientRing k) := by
  let hdomain : IsDomain ((MvPolynomial (Fin 5) R)[X] ⧸
      Ideal.span {polynomial k 3 1}) := weighted_polynomial_adjoinRoot_isDomain k
  let e := Ideal.quotientEquiv (Ideal.span {hypersurface k 3 1})
    (Ideal.span {polynomial k 3 1})
    (MvPolynomial.finSuccEquiv R 5).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {polynomial k 3 1} =
        Ideal.span {MvPolynomial.finSuccEquiv R 5 (hypersurface k 3 1)}
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


theorem physical_isHomogeneous (k : R) : (hypersurface k 6 2).IsHomogeneous 6 := by
  have hx (i : Fin 6) := MvPolynomial.isHomogeneous_X R i
  have hp (i : Fin 6) (a : ℕ) := MvPolynomial.isHomogeneous_X_pow (R := R) i a
  have h2 : (2 : MvPolynomial (Fin 6) R).IsHomogeneous 0 := by
    simpa only [map_ofNat] using MvPolynomial.isHomogeneous_C (Fin 6) (2 : R)
  have h3 : (3 : MvPolynomial (Fin 6) R).IsHomogeneous 0 := by
    simpa only [map_ofNat] using MvPolynomial.isHomogeneous_C (Fin 6) (3 : R)
  have hA := (((hp 0 3).mul (hx 1)).mul (hx 3)).mul (hx 4)
  have hB := (((hx 0).mul (hx 1)).mul (hp 3 3)).mul (hx 4)
  have hC := (((hx 0).mul (hx 1)).mul (hp 3 2)).mul (hp 5 2)
  have hD := ((((h2.mul (hx 0)).mul (hx 1)).mul (hp 4 2)).mul (hp 5 2))
  have hE := ((((h3.mul (hx 0)).mul (hp 2 3)).mul (hx 3)).mul (hx 4))
  have hF := ((((h2.mul (hp 1 3)).mul (hx 2)).mul (hx 3)).mul (hx 4))
  have hG := (((hx 1).mul (hx 2)).mul (hx 3)).mul (hp 4 3)
  exact ((((((hp 0 6).add (hp 1 6)).add (hp 2 6)).add (hp 3 6)).add
    (hp 4 6)).add (hp 5 6)).add
      (((((((hA.add hB).add hC).add hD).add hE).add hF).add hG).C_mul k)

def physicalSource : MvPolynomial (Fin 6) R := MvPolynomial.X 0^3*MvPolynomial.X 5^3

def quotientSource : MvPolynomial (Fin 6) R := MvPolynomial.X 0^3*MvPolynomial.X 5

theorem physicalSource_isHomogeneous : (physicalSource (R := R)).IsHomogeneous 6 :=
  (MvPolynomial.isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (MvPolynomial.isHomogeneous_X_pow (5 : Fin 6) 3)

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.weighted_quotient_irreducible
#print axioms ReflectionCoupledFano.physical_irreducible
