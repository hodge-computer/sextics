import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain

/- Source component: HypersurfaceCoordinates -/
section
/-!
Multivariate coordinate versions of the integral-domain lemmas. The original
holdout sextic is kept fixed throughout. These are intermediate construction
lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section WeightedQuotient

variable {R : Type*} [CommRing R]

/-- Coordinate order: `X0, X1, X2, S, P`. -/
def weightedHypersurface (alpha beta : R) : MvPolynomial (Fin 5) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
    MvPolynomial.X 4 * (MvPolynomial.C alpha * MvPolynomial.X 0^3 * MvPolynomial.X 1 +
      MvPolynomial.C beta * MvPolynomial.X 1^3 * MvPolynomial.X 2) +
    MvPolynomial.X 3^3 - 3*MvPolynomial.X 3*MvPolynomial.X 4^2

theorem weightedHypersurface_univariate (alpha beta : R) :
    MvPolynomial.finSuccEquiv R 4 (weightedHypersurface alpha beta) =
      quotientPolynomial alpha beta := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 4) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3)] := by
    funext i
    fin_cases i <;> rfl
  simp [weightedHypersurface, quotientPolynomial, MvPolynomial.finSuccEquiv_apply, he,
    Polynomial.C_ofNat]
  ring

theorem weightedHypersurface_irreducible [IsDomain R] [CharZero R]
    (alpha beta : R) : Irreducible (weightedHypersurface alpha beta) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 4)).mp
  rw [weightedHypersurface_univariate]
  exact quotientPolynomial_irreducible alpha beta

theorem weightedHypersurface_quotient_isDomain [IsDomain R] [CharZero R]
    (alpha beta : R) :
    IsDomain (MvPolynomial (Fin 5) R ⧸ Ideal.span {weightedHypersurface alpha beta}) := by
  let hdomain : IsDomain ((MvPolynomial (Fin 4) R)[X] ⧸
      Ideal.span {quotientPolynomial alpha beta}) := by
    change IsDomain (AdjoinRoot (quotientPolynomial alpha beta))
    exact quotient_adjoinRoot_isDomain alpha beta
  let e := Ideal.quotientEquiv (Ideal.span {weightedHypersurface alpha beta})
    (Ideal.span {quotientPolynomial alpha beta})
    (MvPolynomial.finSuccEquiv R 4).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {quotientPolynomial alpha beta} =
        Ideal.span {MvPolynomial.finSuccEquiv R 4 (weightedHypersurface alpha beta)}
      rw [weightedHypersurface_univariate])
  exact e.injective.isDomain e.toRingHom

end WeightedQuotient

section OriginalHoldout

variable {R : Type*} [CommRing R]

/-- The exact one-reflection sextic, monic in `X0`. The coefficient variables are
`X1, X2, Y0, Y1, Y2`, in this order. -/
def holdoutPolynomial : (MvPolynomial (Fin 5) R)[X] :=
  X^6 + (C (MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3) * X^3 +
    C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^6 +
      MvPolynomial.X 3^6 + MvPolynomial.X 4^6 +
      MvPolynomial.X 0^3 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3))

theorem holdoutPolynomial_monic : (holdoutPolynomial (R := R)).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

/-- `eta` may be any sixth root of `-1`; over the complex numbers one can
take `eta = I`. -/
def holdoutSpecialization (eta : R) : MvPolynomial (Fin 5) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X+1, 0, C eta]

theorem holdoutPolynomial_specialization (eta : R) (heta : eta^6 = -1) :
    (holdoutPolynomial (R := R)).map (holdoutSpecialization eta) =
      (X : (R[X])[X])^6 + C ((X+1)^6 - 1) := by
  simp [holdoutPolynomial, holdoutSpecialization, ← map_pow, heta, sub_eq_add_neg]

theorem holdoutPolynomial_irreducible [IsDomain R] [CharZero R]
    (eta : R) (heta : eta^6 = -1) :
    Irreducible (holdoutPolynomial (R := R)) := by
  apply (holdoutPolynomial_monic (R := R)).irreducible_of_irreducible_map
    (holdoutSpecialization eta)
  rw [holdoutPolynomial_specialization eta heta]
  exact irreducible_power_add_constant ((X+1)^6 - 1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

/-- Coordinate order: `X0, X1, X2, Y0, Y1, Y2`. -/
def holdoutSextic : MvPolynomial (Fin 6) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 0^3*MvPolynomial.X 1*MvPolynomial.X 3*MvPolynomial.X 4 +
    MvPolynomial.X 1^6 + MvPolynomial.X 1^3*MvPolynomial.X 2*MvPolynomial.X 3*MvPolynomial.X 4 +
    MvPolynomial.X 2^6 + MvPolynomial.X 3^6 + MvPolynomial.X 4^6 + MvPolynomial.X 5^6

theorem holdoutSextic_univariate :
    MvPolynomial.finSuccEquiv R 5 (holdoutSextic (R := R)) =
      holdoutPolynomial (R := R) := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 5) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X, C (MvPolynomial.X 0), C (MvPolynomial.X 1),
        C (MvPolynomial.X 2), C (MvPolynomial.X 3), C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [holdoutSextic, holdoutPolynomial, MvPolynomial.finSuccEquiv_apply, he]
  ring

theorem holdoutSextic_irreducible [IsDomain R] [CharZero R]
    (eta : R) (heta : eta^6 = -1) : Irreducible (holdoutSextic (R := R)) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 5)).mp
  rw [holdoutSextic_univariate]
  exact holdoutPolynomial_irreducible eta heta

/-- Restriction to the `X0` axis. -/
def holdoutAxis : MvPolynomial (Fin 6) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![X, 0, 0, 0, 0, 0]

theorem holdoutAxis_equation :
    holdoutAxis (holdoutSextic (R := R)) = X^6 := by
  simp [holdoutAxis, holdoutSextic]

theorem holdoutAxis_gradient :
    holdoutAxis (MvPolynomial.pderiv 0 (holdoutSextic (R := R))) = 6*X^5 := by
  norm_num [holdoutAxis, holdoutSextic, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Polynomial.C_ofNat, Pi.single_apply,
    show (2 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 0 by decide,
    show (4 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 0 by decide]

/-- The distinguished normal derivative stays nonzero on the hypersurface.
No smoothness theorem is required: divisibility would survive restriction to
the `X0` axis, where `X0^6` cannot divide `6 X0^5`. -/
theorem holdoutSextic_not_dvd_pderiv_zero [CharZero R] :
    ¬ holdoutSextic (R := R) ∣ MvPolynomial.pderiv 0 (holdoutSextic (R := R)) := by
  intro hd
  have hm := map_dvd (holdoutAxis (R := R)) hd
  rw [holdoutAxis_equation, holdoutAxis_gradient] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

end OriginalHoldout

section HoldoutQuotient

variable {R : Type*} [Field R] [CharZero R]

theorem holdoutSextic_quotient_isDomain
    (eta : R) (heta : eta^6 = -1) :
    IsDomain (MvPolynomial (Fin 6) R ⧸ Ideal.span {holdoutSextic (R := R)}) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime
      (holdoutSextic_irreducible eta heta).ne_zero).mpr
        (holdoutSextic_irreducible eta heta).prime)

end HoldoutQuotient

end HoldoutConstruction

#print axioms HoldoutConstruction.weightedHypersurface_quotient_isDomain
#print axioms HoldoutConstruction.holdoutSextic_irreducible
#print axioms HoldoutConstruction.holdoutSextic_quotient_isDomain
end
end
