import Proposal.BundleConic
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The actual coefficient, endpoint, and quotient domains.  The coefficient
parameter is a unit, and the complex specialization is performed on its
Laurent coordinate ring before passing to a function field.
-/

noncomputable section

namespace HoldoutBundle

open Polynomial HoldoutConstruction

section Equations

variable {R : Type*} [CommRing R]

def endpointPolynomial (a b : R) : (MvPolynomial (Fin 3) R)[X] :=
  X^6 + C (MvPolynomial.X 0^6 + MvPolynomial.C a*MvPolynomial.X 1^3 +
    MvPolynomial.C b*MvPolynomial.X 2^3)

theorem endpointPolynomial_monic (a b : R) : (endpointPolynomial a b).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem endpointPolynomial_degree [Nontrivial R] (a b : R) :
    (endpointPolynomial a b).degree = 6 :=
  degree_X_pow_add_C (by decide : 0 < 6) _

theorem endpointPolynomial_natDegree [Nontrivial R] (a b : R) :
    (endpointPolynomial a b).natDegree = 6 := natDegree_X_pow_add_C

def quotientPolynomial (a b : R) : (MvPolynomial (Fin 4) R)[X] :=
  X^6 + (C (MvPolynomial.X 0*MvPolynomial.X 2)*X^3 +
    C (MvPolynomial.X 0^6+MvPolynomial.X 1^6+
      MvPolynomial.X 0^3*MvPolynomial.X 1*MvPolynomial.X 3+
      MvPolynomial.C a*MvPolynomial.X 2^3+
      MvPolynomial.C b*MvPolynomial.X 3^3))

theorem quotientPolynomial_monic (a b : R) : (quotientPolynomial a b).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

theorem endpointPolynomial_map {T : Type*} [CommRing T] (f : R →+* T) (a b : R) :
    (endpointPolynomial a b).map (MvPolynomial.map f) =
      endpointPolynomial (f a) (f b) := by
  simp [endpointPolynomial]

theorem quotientPolynomial_map {T : Type*} [CommRing T] (f : R →+* T) (a b : R) :
    (quotientPolynomial a b).map (MvPolynomial.map f) =
      quotientPolynomial (f a) (f b) := by
  simp [quotientPolynomial]

theorem kPoly_univariate (a b : R) :
    MvPolynomial.finSuccEquiv R 4 (kPoly a b) = quotientPolynomial a b := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 4) R)[X])
      (fun j => C (MvPolynomial.X j))) =
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),
        C (MvPolynomial.X 2),C (MvPolynomial.X 3)] := by
    funext j
    fin_cases j <;> rfl
  simp [kPoly, K, quotientPolynomial, MvPolynomial.finSuccEquiv_apply, he]
  ring

end Equations

section Domains

private theorem endpoint_irreducible_algClosed
    {R : Type*} [Field R] [CharZero R] [IsAlgClosed R]
    (a b : R) (hb : b ≠ 0) : Irreducible (endpointPolynomial a b) := by
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (-b⁻¹) (by decide : 0 < 3)
  have he0 : e ≠ 0 := by
    intro h
    simp [h, inv_ne_zero hb] at he
  have hbe : b*e^3 = -1 := by
    rw [he]
    field_simp
  let f : MvPolynomial (Fin 3) R →+* R[X] :=
    MvPolynomial.eval₂Hom C ![1,0,X+C e]
  apply (endpointPolynomial_monic a b).irreducible_of_irreducible_map f
  have hm : (endpointPolynomial a b).map f =
      (X : (R[X])[X])^6+C (1+C b*(X+C e)^3) := by
    simp [endpointPolynomial, f]
  rw [hm]
  apply irreducible_power_add_constant _ _ _ 6 (by decide)
  · simp [coeff_X_add_C_pow, hbe]
  · have hc : ((1+C b*(X+C e)^3 : R[X]).coeff 1) = 3*b*e^2 := by
      norm_num [coeff_X_add_C_pow, coeff_one]
      ring
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 he0)

theorem endpointPolynomial_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a b : R) (hb : b ≠ 0) : Irreducible (endpointPolynomial a b) := by
  let L := AlgebraicClosure (FractionRing R)
  let f : R →+* L :=
    (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R _)
  apply (endpointPolynomial_monic a b).irreducible_of_irreducible_map (MvPolynomial.map f)
  rw [endpointPolynomial_map]
  exact endpoint_irreducible_algClosed (f a) (f b)
    (fun h => hb (hf (h.trans (map_zero f).symm)))

theorem quotientPolynomial_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a b : R) (hb : b ≠ 0) : Irreducible (quotientPolynomial a b) := by
  let f : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 3) R :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      ![0,MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.X 2]
  apply (quotientPolynomial_monic a b).irreducible_of_irreducible_map f
  have hm : (quotientPolynomial a b).map f = endpointPolynomial a b := by
    simp [quotientPolynomial, endpointPolynomial, f]
  rw [hm]
  exact endpointPolynomial_irreducible a b hb

theorem endpoint_adjoinRoot_isDomain
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a b : R) (hb : b ≠ 0) : IsDomain (AdjoinRoot (endpointPolynomial a b)) := by
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R _
  have hm : IsDomain (AdjoinRoot
      ((endpointPolynomial a b).map (MvPolynomial.map f))) := by
    rw [endpointPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (endpointPolynomial_irreducible (f a) (f b)
        (fun h => hb (hf (h.trans (map_zero f).symm)))).prime
  let := hm
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map f)
    (MvPolynomial.map_injective f hf) _ (endpointPolynomial_monic a b)

theorem quotient_adjoinRoot_isDomain
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a b : R) (hb : b ≠ 0) : IsDomain (AdjoinRoot (quotientPolynomial a b)) := by
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R _
  have hm : IsDomain (AdjoinRoot
      ((quotientPolynomial a b).map (MvPolynomial.map f))) := by
    rw [quotientPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (quotientPolynomial_irreducible (f a) (f b)
        (fun h => hb (hf (h.trans (map_zero f).symm)))).prime
  let := hm
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map f)
    (MvPolynomial.map_injective f hf) _ (quotientPolynomial_monic a b)

end Domains

section EndpointCoordinates

variable {R : Type*} [CommRing R]

abbrev EndpointCoordinateRing (a b : R) := AdjoinRoot (endpointPolynomial a b)
abbrev QuotientCoordinateRing (a b : R) := AdjoinRoot (quotientPolynomial a b)

def endpointRoot (a b : R) : EndpointCoordinateRing a b :=
  AdjoinRoot.root (endpointPolynomial a b)

def endpointParameter (a b : R) (j : Fin 3) : EndpointCoordinateRing a b :=
  AdjoinRoot.of (endpointPolynomial a b) (MvPolynomial.X j)

theorem endpointRoot_ne_zero [Nontrivial R] (a b : R) : endpointRoot a b ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (endpointPolynomial_monic a b) X_ne_zero
  rw [Polynomial.natDegree_X, endpointPolynomial_natDegree]
  decide

theorem endpoint_of_injective [IsDomain R] (a b : R) :
    Function.Injective (AdjoinRoot.of (endpointPolynomial a b)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [endpointPolynomial_degree]
  decide

theorem endpoint_charZero [IsDomain R] [CharZero R] (a b : R) :
    CharZero (EndpointCoordinateRing a b) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (endpointPolynomial a b)).comp MvPolynomial.C)
    ((endpoint_of_injective a b).comp (MvPolynomial.C_injective (Fin 3) R))

theorem endpoint_relation (a b : R) :
    (endpointRoot a b)^6+(endpointParameter a b 0)^6+
      algebraMap R (EndpointCoordinateRing a b) a*(endpointParameter a b 1)^3+
      algebraMap R (EndpointCoordinateRing a b) b*(endpointParameter a b 2)^3=0 := by
  have h := AdjoinRoot.eval₂_root (endpointPolynomial a b)
  change (X^6+C (MvPolynomial.X 0^6+MvPolynomial.C a*MvPolynomial.X 1^3+
    MvPolynomial.C b*MvPolynomial.X 2^3 : MvPolynomial (Fin 3) R)).eval₂
      (AdjoinRoot.of (endpointPolynomial a b)) (endpointRoot a b)=0 at h
  rw [Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  simp only [map_add,map_pow,map_mul] at h
  change (endpointRoot a b)^6+((endpointParameter a b 0)^6+
    algebraMap R (EndpointCoordinateRing a b) a*(endpointParameter a b 1)^3+
    algebraMap R (EndpointCoordinateRing a b) b*(endpointParameter a b 2)^3)=0 at h
  linear_combination h

def endpointMap {T : Type*} [CommRing T] (f : R →+* T) (a b : R) :
    EndpointCoordinateRing a b →+* EndpointCoordinateRing (f a) (f b) :=
  AdjoinRoot.map (MvPolynomial.map f) (endpointPolynomial a b)
    (endpointPolynomial (f a) (f b)) (by rw [endpointPolynomial_map])

theorem endpointMap_injective {T : Type*} [CommRing T]
    (f : R →+* T) (hf : Function.Injective f) (a b : R) :
    Function.Injective (endpointMap f a b) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hp : endpointPolynomial (f a) (f b) ∣ p.map (MvPolynomial.map f) := by
      change p.eval₂ ((AdjoinRoot.of (endpointPolynomial (f a) (f b))).comp
        (MvPolynomial.map f)) (AdjoinRoot.root (endpointPolynomial (f a) (f b)))=0 at hz
      rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq] at hz
      exact AdjoinRoot.mk_eq_zero.mp hz
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (Polynomial.map_dvd_map (MvPolynomial.map f)
      (MvPolynomial.map_injective f hf) (endpointPolynomial_monic a b)).mp
    rwa [endpointPolynomial_map]

@[simp] theorem endpointMap_root {T : Type*} [CommRing T]
    (f : R →+* T) (a b : R) :
    endpointMap f a b (endpointRoot a b)=endpointRoot (f a) (f b) := by
  simp [endpointMap, endpointRoot]

@[simp] theorem endpointMap_parameter {T : Type*} [CommRing T]
    (f : R →+* T) (a b : R) (j : Fin 3) :
    endpointMap f a b (endpointParameter a b j)=endpointParameter (f a) (f b) j := by
  simp [endpointMap, endpointParameter]

end EndpointCoordinates

end HoldoutBundle
