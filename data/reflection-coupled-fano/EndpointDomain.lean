import Proposal.QuarticIncidence
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing

/-!
The transverse endpoint section X1=0 of the reflection quotient cone.
Only the initial point of a curve lies on this section. The polynomial
curve itself is allowed to move in X1 and dominates the five-dimensional
affine cone after adjoining its independent curve parameter.

The four independent endpoint coordinates are X2,Y0,Y1,u. X0 is the
adjoined monic root. Irreducibility is elementary Eisenstein after the
specialization (X2,Y0,Y1,u)=(0,0,1,T-1).
-/

noncomputable section

namespace ReflectionCoupledFano.Endpoint

open Polynomial HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S]

def polynomial (c : R) : (MvPolynomial (Fin 4) R)[X] :=
  X^6 + C (3 * MvPolynomial.C c * MvPolynomial.X 0^3 *
    MvPolynomial.X 1 * MvPolynomial.X 2) * X +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
      MvPolynomial.X 2^6 + MvPolynomial.X 3^3)

theorem polynomial_monic (c : R) : (polynomial c).Monic := by
  unfold polynomial
  rw [add_assoc]
  change (X^6 + (C _ * X + C _)).Monic
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

theorem polynomial_specialization (c : R) :
    (polynomial c).map (MvPolynomial.eval₂Hom C ![0,0,1,X-1]) =
      (X : (R[X])[X])^6 + C (X^3-3*X^2+3*X) := by
  simp [polynomial, Polynomial.C_ofNat]
  norm_num
  ring

theorem polynomial_irreducible [IsDomain R] [CharZero R] (c : R) :
    Irreducible (polynomial c) := by
  apply (polynomial_monic c).irreducible_of_irreducible_map
    (MvPolynomial.eval₂Hom C ![0,0,1,X-1])
  rw [polynomial_specialization]
  exact irreducible_power_add_constant (X^3-3*X^2+3*X : R[X])
    (by simp) (by norm_num) 6 (by decide)

theorem polynomial_map (f : R →+* S) (c : R) :
    (polynomial c).map (MvPolynomial.map f) = polynomial (f c) := by
  simp [polynomial]

abbrev Ring (c : R) := AdjoinRoot (polynomial c)
abbrev Field (c : R) := FractionRing (Ring c)

instance ring_commRing (c : R) : CommRing (Ring c) := inferInstance

instance ring_isDomain [IsDomain R] [CharZero R] (c : R) : IsDomain (Ring c) := by
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot ((polynomial c).map (MvPolynomial.map f))) := by
    rw [polynomial_map]
    exact AdjoinRoot.isDomain_of_prime (polynomial_irreducible (f c)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map f)
    (MvPolynomial.map_injective f hf) _ (polynomial_monic c)

theorem of_injective [IsDomain R] (c : R) :
    Function.Injective (AdjoinRoot.of (polynomial c)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  intro h
  have hc := Polynomial.coeff_eq_zero_of_degree_lt
    (p := polynomial c) (n := 6) (by rw [h]; norm_num)
  have hc6 : (polynomial c).coeff 6 = 1 := by
    simp only [polynomial, Polynomial.coeff_add, Polynomial.coeff_mul_X,
      Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  rw [hc6] at hc
  exact one_ne_zero hc

instance ring_charZero [IsDomain R] [CharZero R] (c : R) : CharZero (Ring c) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (polynomial c)).comp (MvPolynomial.C : R →+* MvPolynomial (Fin 4) R))
    ((of_injective c).comp (MvPolynomial.C_injective (Fin 4) R))

noncomputable instance field_field [IsDomain R] [CharZero R] (c : R) :
    _root_.Field (Field c) := inferInstance

def root (c : R) : Ring c := AdjoinRoot.root (polynomial c)
def parameter (c : R) (i : Fin 4) : Ring c := AdjoinRoot.of (polynomial c) (MvPolynomial.X i)

def point (c : R) : Fin 6 → Ring c :=
  ![root c, 0, parameter c 0, parameter c 1, parameter c 2, parameter c 3]

theorem relation (c : R) :
    H (algebraMap R (Ring c) c) (point c) = 0 := by
  have h := AdjoinRoot.eval₂_root (polynomial c)
  change (X^6 + C (3 * MvPolynomial.C c * MvPolynomial.X 0^3 *
    MvPolynomial.X 1 * MvPolynomial.X 2) * X +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
      MvPolynomial.X 2^6 + MvPolynomial.X 3^3) : (MvPolynomial (Fin 4) R)[X]).eval₂
        (AdjoinRoot.of (polynomial c)) (root c) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, map_add, map_mul, map_pow, map_ofNat] at h
  change (root c)^6 +
    (3 * algebraMap R (Ring c) c * (parameter c 0)^3 * parameter c 1 * parameter c 2) *
      root c + ((parameter c 0)^6 + (parameter c 1)^6 + (parameter c 2)^6 +
        (parameter c 3)^3) = 0 at h
  simp [H, point]
  linear_combination h

def map (f : R →+* S) (c : R) : Ring c →+* Ring (f c) :=
  AdjoinRoot.map (MvPolynomial.map f) (polynomial c) (polynomial (f c))
    (by rw [polynomial_map])

theorem map_injective (f : R →+* S) (hf : Function.Injective f) (c : R) :
    Function.Injective (map f c) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hp : polynomial (f c) ∣ p.map (MvPolynomial.map f) := by
      change p.eval₂ ((AdjoinRoot.of (polynomial (f c))).comp (MvPolynomial.map f))
        (AdjoinRoot.root (polynomial (f c))) = 0 at hz
      rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq] at hz
      exact AdjoinRoot.mk_eq_zero.mp hz
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (Polynomial.map_dvd_map (MvPolynomial.map f)
      (MvPolynomial.map_injective f hf) (polynomial_monic c)).mp
    rwa [polynomial_map]

@[simp] theorem map_root (f : R →+* S) (c : R) : map f c (root c) = root (f c) := by
  simp [map, root]

@[simp] theorem map_parameter (f : R →+* S) (c : R) (i : Fin 4) :
    map f c (parameter c i) = parameter (f c) i := by
  simp [map, parameter]

@[simp] theorem map_coefficient (f : R →+* S) (c r : R) :
    map f c (algebraMap R (Ring c) r) = algebraMap S (Ring (f c)) (f r) := by
  change map f c (AdjoinRoot.of _ (MvPolynomial.C r)) =
    AdjoinRoot.of _ (MvPolynomial.C (f r))
  simp [map]

def equation (c : R) : MvPolynomial (Fin 5) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 3^6 + MvPolynomial.X 4^3 +
    3 * MvPolynomial.C c * MvPolynomial.X 0 * MvPolynomial.X 1^3 *
      MvPolynomial.X 2 * MvPolynomial.X 3

theorem equation_univariate (c : R) :
    MvPolynomial.finSuccEquiv R 4 (equation c) = polynomial c := by
  have he : (Fin.cases (X : Polynomial (MvPolynomial (Fin 4) R))
      (fun j => C (MvPolynomial.X j))) =
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),
        C (MvPolynomial.X 3)] := by
    funext i
    fin_cases i <;> rfl
  simp [equation, polynomial, MvPolynomial.finSuccEquiv_apply, he, Polynomial.C_ofNat]
  ring

def projection (c : R) : MvPolynomial (Fin 5) R →+* Ring c :=
  (AdjoinRoot.mk (polynomial c)).comp (MvPolynomial.finSuccEquiv R 4).toRingHom

theorem projection_surjective (c : R) : Function.Surjective (projection c) :=
  (AdjoinRoot.mk_surjective (g := polynomial c)).comp (MvPolynomial.finSuccEquiv R 4).surjective

theorem projection_kernel (c : R) (p : MvPolynomial (Fin 5) R) :
    projection c p = 0 ↔ equation c ∣ p := by
  change AdjoinRoot.mk (polynomial c) (MvPolynomial.finSuccEquiv R 4 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← equation_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv R 4)

@[simp] theorem projection_X_zero (c : R) :
    projection c (MvPolynomial.X (R := R) (0 : Fin 5)) = root c := by
  simp [projection, root, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem projection_X_succ (c : R) (i : Fin 4) :
    projection c (MvPolynomial.X (R := R) i.succ) = parameter c i := by
  change AdjoinRoot.mk (polynomial c)
    (MvPolynomial.finSuccEquiv R 4 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

def residueMap (c : R) : MvPolynomial (Fin 5) R →+* Field c :=
  (algebraMap (Ring c) (Field c)).comp (projection c)

@[simp] theorem residueMap_C (c r : R) :
    residueMap c (MvPolynomial.C r) = algebraMap R (Field c) r := by
  change algebraMap (Ring c) (Field c) (AdjoinRoot.mk (polynomial c)
    (MvPolynomial.finSuccEquiv R 4 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv R 4 (MvPolynomial.C r) =
    C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv R 4).commutes r]
  rfl

@[simp] theorem residueMap_X_zero (c : R) :
    residueMap c (MvPolynomial.X (R := R) (0 : Fin 5)) =
      algebraMap (Ring c) (Field c) (root c) := by
  simp [residueMap]

@[simp] theorem residueMap_X_succ (c : R) (i : Fin 4) :
    residueMap c (MvPolynomial.X (R := R) i.succ) =
      algebraMap (Ring c) (Field c) (parameter c i) := by
  simp [residueMap]

section FieldCalculus

variable [IsDomain R] [CharZero R]

local instance (c : R) : Algebra ℤ (Field c) := _root_.Ring.toIntAlgebra _

theorem residueMap_kernel (c : R) (p : MvPolynomial (Fin 5) R) :
    residueMap c p = 0 ↔ equation c ∣ p :=
  residue_fractionMap_kernel (projection c) (equation c) (projection_kernel c) p

def axis : MvPolynomial (Fin 5) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![X,0,0,0,0]

theorem equation_not_dvd_normal (c : R) :
    ¬ equation c ∣ integerPartial 0 (equation c) := by
  intro hd
  have hm := map_dvd (axis (R := R)) hd
  have he : axis (equation c) = X^6 := by simp [axis, equation]
  have hg : axis (integerPartial 0 (equation c)) = 6*X^5 := by
    norm_num [axis, equation, integerPartial, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul, Pi.single_apply,
      show (2 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 0 by decide,
      show (4 : Fin 5) ≠ 0 by decide]
  rw [he,hg] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

theorem normal_ne_zero (c : R) : residueMap c (integerPartial 0 (equation c)) ≠ 0 := by
  intro h
  exact equation_not_dvd_normal c ((residueMap_kernel c _).mp h)

def tangent (c : R) (i : Fin 4) : Derivation ℤ (Field c) (Field c) :=
  residueTangent (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c)

theorem tangent_apply (c : R) (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    tangent c i (residueMap c p) = residueMap c (integerPartial i.succ p) -
      residueMap c (integerPartial i.succ (equation c)) /
        residueMap c (integerPartial 0 (equation c)) * residueMap c (integerPartial 0 p) :=
  residueTangent_apply (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c) p

theorem tangents_commute (c : R) (i j : Fin 4) :
    Function.Commute (tangent c i) (tangent c j) :=
  residueTangent_commute (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c) (integerPartial_commute i.succ 0)
    (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)

@[simp] theorem tangent_algebraMap (c : R) (i : Fin 4) (r : R) :
    tangent c i (algebraMap R (Field c) r) = 0 := by
  rw [← residueMap_C c r, tangent_apply]
  simp

theorem tangent_parameter (c : R) (i j : Fin 4) :
    tangent c i (algebraMap (Ring c) (Field c) (parameter c j)) =
      if j = i then 1 else 0 := by
  rw [← residueMap_X_succ, tangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hij : j = i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs, hij]

end FieldCalculus

theorem field_trdeg {K : Type*} [_root_.Field K] [CharZero K]
    (c : K) : Algebra.trdeg K (Field c) = 4 := by
  apply monic_hypersurface_field_trdeg (polynomial c) (polynomial_monic c)
  exact ne_of_gt ((polynomial_monic c).degree_pos_of_not_isUnit
    (polynomial_irreducible c).not_isUnit)

theorem normal_eq_gradient [IsDomain R] [CharZero R] (c : R) :
    residueMap c (integerPartial 0 (equation c)) =
      gradient (algebraMap R (Field c) c)
        (fun i => algebraMap (Ring c) (Field c) (point c i)) 0 := by
  have hd3 : MvPolynomial.pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) R) = 0 := by
    exact Derivation.map_natCast _ 3
  have hp : integerPartial 0 (equation c) =
      6 * MvPolynomial.X 0^5 +
      3 * MvPolynomial.C c * MvPolynomial.X 1^3 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
    norm_num [equation, integerPartial, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul, Pi.single_apply, hd3,
      show (2 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 0 by decide,
      show (4 : Fin 5) ≠ 0 by decide]
    ring
  rw [hp]
  simp only [map_add, map_mul, map_pow, map_ofNat, residueMap_C,
    show (1 : Fin 5) = (0 : Fin 4).succ from rfl,
    show (2 : Fin 5) = (1 : Fin 4).succ from rfl,
    show (3 : Fin 5) = (2 : Fin 4).succ from rfl,
    residueMap_X_zero, residueMap_X_succ]
  norm_num [gradient, point, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change 3 * algebraMap R (Field c) c *
      (algebraMap (Ring c) (Field c) (parameter c 0))^3 *
      algebraMap (Ring c) (Field c) (parameter c 1) *
      algebraMap (Ring c) (Field c) (parameter c 2) =
      algebraMap R (Field c) c *
        (3 * (algebraMap (Ring c) (Field c) (parameter c 0))^3 *
          algebraMap (Ring c) (Field c) (parameter c 1) *
          algebraMap (Ring c) (Field c) (parameter c 2))
  ring

end ReflectionCoupledFano.Endpoint

#print axioms ReflectionCoupledFano.Endpoint.polynomial_irreducible
#print axioms ReflectionCoupledFano.Endpoint.tangents_commute
