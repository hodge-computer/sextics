import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain

/- Source component: EndpointDomain -/
section
/-!
The endpoint domain for the polynomial conic family. The three independent
endpoint parameters are X2, S and P; X0 is the simple algebraic root.
This is an intermediate construction, not a certificate.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

variable {R : Type*} [CommRing R]

def endpointPolynomial : (MvPolynomial (Fin 3) R)[X] :=
  X^6 + C (MvPolynomial.X 0^6 + MvPolynomial.X 1^3 -
    3*MvPolynomial.X 1*MvPolynomial.X 2^2)

theorem endpointPolynomial_monic : (endpointPolynomial (R := R)).Monic :=
  monic_X_pow_add_C _ (by decide)

theorem endpointPolynomial_irreducible [IsDomain R] [CharZero R] :
    Irreducible (endpointPolynomial (R := R)) := by
  apply (endpointPolynomial_monic (R := R)).irreducible_of_irreducible_map
    (MvPolynomial.eval₂Hom C ![0, X, 1])
  have he : (endpointPolynomial (R := R)).map
      (MvPolynomial.eval₂Hom C ![0, X, 1]) = (X : (R[X])[X])^6 + C (X^3-3*X) := by
    simp [endpointPolynomial]
  rw [he]
  exact irreducible_power_add_constant (X^3-3*X : R[X])
    (by simp) (by norm_num) 6 (by decide)

theorem endpointPolynomial_map {T : Type*} [CommRing T] (φ : R →+* T) :
    (endpointPolynomial (R := R)).map (MvPolynomial.map φ) =
      endpointPolynomial (R := T) := by
  simp [endpointPolynomial]

theorem endpoint_adjoinRoot_isDomain [IsDomain R] [CharZero R] :
    IsDomain (AdjoinRoot (endpointPolynomial (R := R))) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hmap : IsDomain (AdjoinRoot
      ((endpointPolynomial (R := R)).map (MvPolynomial.map φ))) := by
    rw [endpointPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (endpointPolynomial_irreducible (R := FractionRing R)).prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map φ)
    (MvPolynomial.map_injective φ hφ) _ endpointPolynomial_monic

abbrev EndpointRing (R : Type*) [CommRing R] := AdjoinRoot (endpointPolynomial (R := R))

def endpointRoot : EndpointRing R := AdjoinRoot.root (endpointPolynomial (R := R))

def endpointParameter (i : Fin 3) : EndpointRing R :=
  AdjoinRoot.of (endpointPolynomial (R := R)) (MvPolynomial.X i)

theorem endpoint_relation :
    (endpointRoot (R := R))^6 + (endpointParameter (R := R) 0)^6 +
      (endpointParameter (R := R) 1)^3 -
      3*endpointParameter (R := R) 1*(endpointParameter (R := R) 2)^2 = 0 := by
  have h := AdjoinRoot.eval₂_root (endpointPolynomial (R := R))
  change (X^6+C (MvPolynomial.X 0^6+MvPolynomial.X 1^3-
    3*MvPolynomial.X 1*MvPolynomial.X 2^2 : MvPolynomial (Fin 3) R)).eval₂
    (AdjoinRoot.of (endpointPolynomial (R := R))) (endpointRoot (R := R)) = 0 at h
  rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  simp only [map_add, map_sub, map_pow, map_mul, map_ofNat] at h
  change (endpointRoot (R := R))^6 + ((endpointParameter (R := R) 0)^6 +
    (endpointParameter (R := R) 1)^3 -
    3*endpointParameter (R := R) 1*(endpointParameter (R := R) 2)^2) = 0 at h
  linear_combination h

/-- The universal endpoint specializes to (X0,X2,S,P)=(1,0,-1,0). -/
def endpointSeedEval : EndpointRing R →+* R :=
  AdjoinRoot.lift (f := endpointPolynomial (R := R))
    (MvPolynomial.eval₂Hom (RingHom.id R) ![0,-1,0]) 1 (by
      simp only [endpointPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      norm_num [Matrix.cons_val]
      change (3 : R)*0^2 = 0
      ring)

@[simp] theorem endpointSeedEval_root : endpointSeedEval (endpointRoot (R := R)) = 1 := by
  simp [endpointSeedEval, endpointRoot]

@[simp] theorem endpointSeedEval_parameter (i : Fin 3) :
    endpointSeedEval (endpointParameter (R := R) i) = ![0,-1,0] i := by
  simp [endpointSeedEval, endpointParameter]

theorem endpointRoot_ne_zero [Nontrivial R] : endpointRoot (R := R) ≠ 0 := by
  intro h
  have hh := congrArg (endpointSeedEval (R := R)) h
  simp at hh

theorem endpoint_of_injective [IsDomain R] :
    Function.Injective (AdjoinRoot.of (endpointPolynomial (R := R))) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  change (X^6+C (MvPolynomial.X 0^6+MvPolynomial.X 1^3-
    3*MvPolynomial.X 1*MvPolynomial.X 2^2 : MvPolynomial (Fin 3) R)).degree ≠ 0
  rw [degree_X_pow_add_C (by decide)]
  norm_num

theorem endpoint_charZero [IsDomain R] [CharZero R] : CharZero (EndpointRing R) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (endpointPolynomial (R := R))).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin 3) R))
    ((endpoint_of_injective (R := R)).comp (MvPolynomial.C_injective (Fin 3) R))

end HoldoutConstruction

#print axioms HoldoutConstruction.endpoint_adjoinRoot_isDomain
#print axioms HoldoutConstruction.endpointRoot_ne_zero
#print axioms HoldoutConstruction.endpoint_of_injective
end
end

/- Source component: EndpointBaseChange -/
section
/-!
Injective base change of the endpoint coordinate domain. In the holdout
application the source coefficient ring is the Fermat-curve coordinate
ring, while the destination is its fraction field. A seed is evaluated
only on the former; generic construction takes place over the latter.
-/

noncomputable section


namespace HoldoutConstruction

variable {R T : Type*} [CommRing R] [CommRing T]

def endpointMap (φ : R →+* T) : EndpointRing R →+* EndpointRing T :=
  AdjoinRoot.map (MvPolynomial.map φ) (endpointPolynomial (R := R))
    (endpointPolynomial (R := T)) (by rw [endpointPolynomial_map])

theorem endpointMap_injective (φ : R →+* T) (hφ : Function.Injective φ) :
    Function.Injective (endpointMap φ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hp : endpointPolynomial (R := T) ∣ p.map (MvPolynomial.map φ) := by
      change p.eval₂ ((AdjoinRoot.of (endpointPolynomial (R := T))).comp
        (MvPolynomial.map φ)) (AdjoinRoot.root (endpointPolynomial (R := T))) = 0 at hz
      rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
        ← Polynomial.aeval_def, AdjoinRoot.aeval_eq] at hz
      exact AdjoinRoot.mk_eq_zero.mp hz
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (Polynomial.map_dvd_map (MvPolynomial.map φ)
      (MvPolynomial.map_injective φ hφ) endpointPolynomial_monic).mp
    rwa [endpointPolynomial_map]

@[simp] theorem endpointMap_root (φ : R →+* T) :
    endpointMap φ (endpointRoot (R := R)) = endpointRoot (R := T) := by
  simp [endpointMap, endpointRoot]

@[simp] theorem endpointMap_parameter (φ : R →+* T) (i : Fin 3) :
    endpointMap φ (endpointParameter (R := R) i) = endpointParameter (R := T) i := by
  simp [endpointMap, endpointParameter]

@[simp] theorem endpointMap_coefficient (φ : R →+* T) (r : R) :
    endpointMap φ (algebraMap R (EndpointRing R) r) =
      algebraMap T (EndpointRing T) (φ r) := by
  change endpointMap φ (AdjoinRoot.of _ (MvPolynomial.C r)) =
    AdjoinRoot.of _ (MvPolynomial.C (φ r))
  simp [endpointMap]

def endpointFieldMap (φ : R →+* T) :
    EndpointRing R →+* FractionRing (EndpointRing T) :=
  (algebraMap (EndpointRing T) (FractionRing (EndpointRing T))).comp (endpointMap φ)

theorem endpointFieldMap_injective [IsDomain T] [CharZero T]
    (φ : R →+* T) (hφ : Function.Injective φ) :
    Function.Injective (endpointFieldMap φ) := by
  let : IsDomain (EndpointRing T) := endpoint_adjoinRoot_isDomain
  intro a b h
  apply endpointMap_injective φ hφ
  apply IsFractionRing.injective (EndpointRing T) (FractionRing (EndpointRing T))
  exact h

end HoldoutConstruction

#print axioms HoldoutConstruction.endpointMap_injective
#print axioms HoldoutConstruction.endpointFieldMap_injective
end
end
