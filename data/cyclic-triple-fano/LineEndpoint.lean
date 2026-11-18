import Proposal.LineIncidence
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing

/-! The endpoint section Y1=0; adapted from fqlx's reflection-coupled-fano proof. -/

noncomputable section

namespace CyclicTriple.Endpoint

open Polynomial HoldoutConstruction



def polynomial (c : ℂ) : (MvPolynomial (Fin 4) ℂ)[X] :=
  X^6 + C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 3^2 + MvPolynomial.C c*MvPolynomial.X 0^3*MvPolynomial.X 3)

theorem polynomial_monic (c : ℂ) : (polynomial c).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem polynomial_specialization (c : ℂ) :
    (polynomial c).map (MvPolynomial.eval₂Hom C ![0,X+1,0,C Complex.I]) =
      (X : (ℂ[X])[X])^6 + C ((X+1)^6-1) := by
  simp [polynomial, ← map_pow, Complex.I_sq, sub_eq_add_neg]

theorem polynomial_irreducible (c : ℂ) : Irreducible (polynomial c) := by
  apply (polynomial_monic c).irreducible_of_irreducible_map
    (MvPolynomial.eval₂Hom C ![0,X+1,0,C Complex.I])
  rw [polynomial_specialization]
  exact irreducible_power_add_constant ((X+1)^6-1 : ℂ[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one]) 6 (by decide)

abbrev Ring (c : ℂ) := AdjoinRoot (polynomial c)
abbrev Field (c : ℂ) := FractionRing (Ring c)
instance ring_commRing (c : ℂ) : CommRing (Ring c) := inferInstance
instance ring_isDomain (c : ℂ) : IsDomain (Ring c) :=
  AdjoinRoot.isDomain_of_prime (polynomial_irreducible c).prime

theorem of_injective (c : ℂ) :
    Function.Injective (AdjoinRoot.of (polynomial c)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  intro h
  have hc := Polynomial.coeff_eq_zero_of_degree_lt
    (p := polynomial c) (n := 6) (by rw [h]; norm_num)
  have hc6 : (polynomial c).coeff 6 = 1 := by
    simp only [polynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  rw [hc6] at hc
  exact one_ne_zero hc

instance ring_charZero (c : ℂ) : CharZero (Ring c) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (polynomial c)).comp (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 4) ℂ))
    ((of_injective c).comp (MvPolynomial.C_injective (Fin 4) ℂ))

noncomputable instance field_field (c : ℂ) :
    _root_.Field (Field c) := inferInstance

def root (c : ℂ) : Ring c := AdjoinRoot.root (polynomial c)
def parameter (c : ℂ) (i : Fin 4) : Ring c := AdjoinRoot.of (polynomial c) (MvPolynomial.X i)

def point (c : ℂ) : Fin 6 → Ring c :=
  ![root c, 0, parameter c 0, parameter c 1, parameter c 2, parameter c 3]

theorem relation (c : ℂ) : H (algebraMap ℂ (Ring c) c) (point c) = 0 := by
  have h := AdjoinRoot.eval₂_root (polynomial c)
  change (X^6 + C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 3^2 + MvPolynomial.C c*MvPolynomial.X 0^3*MvPolynomial.X 3) :
    (MvPolynomial (Fin 4) ℂ)[X]).eval₂ (AdjoinRoot.of (polynomial c)) (root c) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, map_add, map_mul, map_pow, map_ofNat] at h
  change root c ^ 6 + (parameter c 0 ^ 6 + parameter c 1 ^ 6 + parameter c 2 ^ 6 +
    parameter c 3 ^ 2 + algebraMap ℂ (Ring c) c * parameter c 0 ^ 3 * parameter c 3) = 0 at h
  simp [H, point]
  linear_combination h

def equation (c : ℂ) : MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 3^6 + MvPolynomial.X 4^2 +
    MvPolynomial.C c * MvPolynomial.X 1^3 * MvPolynomial.X 4

theorem equation_univariate (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ 4 (equation c) = polynomial c := by
  have he : (Fin.cases (X : Polynomial (MvPolynomial (Fin 4) ℂ))
      (fun j => C (MvPolynomial.X j))) =
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),
        C (MvPolynomial.X 3)] := by
    funext i
    fin_cases i <;> rfl
  simp [equation, polynomial, MvPolynomial.finSuccEquiv_apply, he, Polynomial.C_ofNat]
  ring

def projection (c : ℂ) : MvPolynomial (Fin 5) ℂ →+* Ring c :=
  (AdjoinRoot.mk (polynomial c)).comp (MvPolynomial.finSuccEquiv ℂ 4).toRingHom

theorem projection_surjective (c : ℂ) : Function.Surjective (projection c) :=
  (AdjoinRoot.mk_surjective (g := polynomial c)).comp (MvPolynomial.finSuccEquiv ℂ 4).surjective

theorem projection_kernel (c : ℂ) (p : MvPolynomial (Fin 5) ℂ) :
    projection c p = 0 ↔ equation c ∣ p := by
  change AdjoinRoot.mk (polynomial c) (MvPolynomial.finSuccEquiv ℂ 4 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← equation_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 4)

@[simp] theorem projection_X_zero (c : ℂ) :
    projection c (MvPolynomial.X (R := ℂ) (0 : Fin 5)) = root c := by
  simp [projection, root, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem projection_X_succ (c : ℂ) (i : Fin 4) :
    projection c (MvPolynomial.X (R := ℂ) i.succ) = parameter c i := by
  change AdjoinRoot.mk (polynomial c)
    (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

def residueMap (c : ℂ) : MvPolynomial (Fin 5) ℂ →+* Field c :=
  (algebraMap (Ring c) (Field c)).comp (projection c)

@[simp] theorem residueMap_C (c r : ℂ) :
    residueMap c (MvPolynomial.C r) = algebraMap ℂ (Field c) r := by
  change algebraMap (Ring c) (Field c) (AdjoinRoot.mk (polynomial c)
    (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.C r) =
    C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv ℂ 4).commutes r]
  rfl

@[simp] theorem residueMap_X_zero (c : ℂ) :
    residueMap c (MvPolynomial.X (R := ℂ) (0 : Fin 5)) =
      algebraMap (Ring c) (Field c) (root c) := by
  simp [residueMap]

@[simp] theorem residueMap_X_succ (c : ℂ) (i : Fin 4) :
    residueMap c (MvPolynomial.X (R := ℂ) i.succ) =
      algebraMap (Ring c) (Field c) (parameter c i) := by
  simp [residueMap]

section FieldCalculus



local instance (c : ℂ) : Algebra ℤ (Field c) := _root_.Ring.toIntAlgebra _

theorem residueMap_kernel (c : ℂ) (p : MvPolynomial (Fin 5) ℂ) :
    residueMap c p = 0 ↔ equation c ∣ p :=
  residue_fractionMap_kernel (projection c) (equation c) (projection_kernel c) p

def axis : MvPolynomial (Fin 5) ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom C ![X,0,0,0,0]

theorem equation_not_dvd_normal (c : ℂ) :
    ¬ equation c ∣ integerPartial 0 (equation c) := by
  intro hd
  have hm := map_dvd axis hd
  have he : axis (equation c) = X^6 := by simp [axis, equation]
  have hg : axis (integerPartial 0 (equation c)) = 6*X^5 := by
    norm_num [axis, equation, integerPartial, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul, Pi.single_apply,
      show (2 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 0 by decide,
      show (4 : Fin 5) ≠ 0 by decide]
  rw [he,hg] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

theorem normal_ne_zero (c : ℂ) : residueMap c (integerPartial 0 (equation c)) ≠ 0 := by
  intro h
  exact equation_not_dvd_normal c ((residueMap_kernel c _).mp h)

def tangent (c : ℂ) (i : Fin 4) : Derivation ℤ (Field c) (Field c) :=
  residueTangent (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c)

theorem tangent_apply (c : ℂ) (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    tangent c i (residueMap c p) = residueMap c (integerPartial i.succ p) -
      residueMap c (integerPartial i.succ (equation c)) /
        residueMap c (integerPartial 0 (equation c)) * residueMap c (integerPartial 0 p) :=
  residueTangent_apply (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c) p

theorem tangents_commute (c : ℂ) (i j : Fin 4) :
    Function.Commute (tangent c i) (tangent c j) :=
  residueTangent_commute (K := Field c) (projection c) (projection_surjective c)
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) (equation c)
    (projection_kernel c) (normal_ne_zero c) (integerPartial_commute i.succ 0)
    (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)

@[simp] theorem tangent_algebraMap (c : ℂ) (i : Fin 4) (r : ℂ) :
    tangent c i (algebraMap ℂ (Field c) r) = 0 := by
  rw [← residueMap_C c r, tangent_apply]
  simp

theorem tangent_parameter (c : ℂ) (i j : Fin 4) :
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

theorem field_trdeg (c : ℂ) : Algebra.trdeg ℂ (Field c) = 4 := by
  apply monic_hypersurface_field_trdeg (polynomial c) (polynomial_monic c)
  exact ne_of_gt ((polynomial_monic c).degree_pos_of_not_isUnit
    (polynomial_irreducible c).not_isUnit)

theorem normal_eq_gradient (c : ℂ) :
    residueMap c (integerPartial 0 (equation c)) =
      gradient (algebraMap ℂ (Field c) c)
        (fun i => algebraMap (Ring c) (Field c) (point c i)) 0 := by
  have hp : integerPartial 0 (equation c) = 6 * MvPolynomial.X 0^5 := by
    norm_num [equation, integerPartial, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul, Pi.single_apply,
      show (2 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 0 by decide, show (4 : Fin 5) ≠ 0 by decide]
  rw [hp]
  simp [gradient, point, residueMap_X_zero, map_ofNat]

end CyclicTriple.Endpoint

#print axioms CyclicTriple.Endpoint.polynomial_irreducible
#print axioms CyclicTriple.Endpoint.tangents_commute
