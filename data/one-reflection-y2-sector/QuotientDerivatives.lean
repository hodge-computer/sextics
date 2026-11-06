import HodgeComputer.Constructions.HoldoutCover.CurveFamily
import Proposal.HypersurfaceCoordinates
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/- Source component: QuotientDerivations -/
section
/-!
The four canonical tangent derivations of the weighted quotient function
field. The coordinate order is X0, X1, X2, S, P, with X0 eliminated by the
actual monic sextic. Constants in the coefficient field are killed.
-/

noncomputable section

namespace HoldoutConstruction

section Coordinates

variable {R : Type*} [CommRing R]

abbrev QuotientRing (alpha beta : R) := AdjoinRoot (quotientPolynomial alpha beta)

abbrev QuotientField (alpha beta : R) := FractionRing (QuotientRing alpha beta)

def quotientRoot (alpha beta : R) : QuotientRing alpha beta :=
  AdjoinRoot.root (quotientPolynomial alpha beta)

def quotientParameter (alpha beta : R) (i : Fin 4) : QuotientRing alpha beta :=
  AdjoinRoot.of (quotientPolynomial alpha beta) (MvPolynomial.X i)

def quotientProjection (alpha beta : R) :
    MvPolynomial (Fin 5) R →+* QuotientRing alpha beta :=
  (AdjoinRoot.mk (quotientPolynomial alpha beta)).comp
    (MvPolynomial.finSuccEquiv R 4).toRingHom

theorem quotientProjection_surjective (alpha beta : R) :
    Function.Surjective (quotientProjection alpha beta) :=
  (AdjoinRoot.mk_surjective (g := quotientPolynomial alpha beta)).comp
    (MvPolynomial.finSuccEquiv R 4).surjective

theorem quotientProjection_kernel (alpha beta : R) (p : MvPolynomial (Fin 5) R) :
    quotientProjection alpha beta p = 0 ↔ weightedHypersurface alpha beta ∣ p := by
  change AdjoinRoot.mk (quotientPolynomial alpha beta)
    (MvPolynomial.finSuccEquiv R 4 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← weightedHypersurface_univariate alpha beta]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv R 4)

@[simp] theorem quotientProjection_X_zero (alpha beta : R) :
    quotientProjection alpha beta (MvPolynomial.X 0) = quotientRoot alpha beta := by
  change AdjoinRoot.mk (quotientPolynomial alpha beta)
    (MvPolynomial.finSuccEquiv R 4 (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rfl

@[simp] theorem quotientProjection_X_succ (alpha beta : R) (i : Fin 4) :
    quotientProjection alpha beta (MvPolynomial.X i.succ) = quotientParameter alpha beta i := by
  change AdjoinRoot.mk (quotientPolynomial alpha beta)
    (MvPolynomial.finSuccEquiv R 4 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

def quotientAxis : MvPolynomial (Fin 5) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0,0,0]

theorem quotientAxis_equation (alpha beta : R) :
    quotientAxis (weightedHypersurface alpha beta) = Polynomial.X^6 := by
  simp [quotientAxis, weightedHypersurface]

theorem quotientAxis_gradient (alpha beta : R) :
    quotientAxis (integerPartial 0 (weightedHypersurface alpha beta)) =
      6*Polynomial.X^5 := by
  norm_num [quotientAxis, integerPartial, weightedHypersurface,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, Polynomial.C_ofNat,
    Pi.single_apply, show (1 : Fin 5) ≠ 0 by decide,
    show (2 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 0 by decide,
    show (4 : Fin 5) ≠ 0 by decide]
  simp [Matrix.cons_val]

/-- Restriction to the X0 axis proves that the normal derivative does not
vanish in the hypersurface's coordinate ring. -/
theorem weightedHypersurface_not_dvd_partial_zero [CharZero R] (alpha beta : R) :
    ¬ weightedHypersurface alpha beta ∣ integerPartial 0 (weightedHypersurface alpha beta) := by
  intro hd
  have hm := map_dvd (quotientAxis (R := R)) hd
  rw [quotientAxis_equation, quotientAxis_gradient] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

end Coordinates

section Field

variable {R : Type*} [Field R] [CharZero R]

attribute [local instance] quotient_adjoinRoot_isDomain

theorem quotient_charZero (alpha beta : R) : CharZero (QuotientRing alpha beta) := by
  let φ : R →+* QuotientRing alpha beta :=
    (AdjoinRoot.of (quotientPolynomial alpha beta)).comp MvPolynomial.C
  exact charZero_of_injective_ringHom (f := φ) φ.injective

attribute [local instance] quotient_charZero

local instance (alpha beta : R) : Algebra ℤ (QuotientField alpha beta) := Ring.toIntAlgebra _

def quotientResidueMap (alpha beta : R) :
    MvPolynomial (Fin 5) R →+* QuotientField alpha beta :=
  (algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)).comp
    (quotientProjection alpha beta)

omit [CharZero R] in
@[simp] theorem quotientResidueMap_C (alpha beta r : R) :
    quotientResidueMap alpha beta (MvPolynomial.C r) =
      algebraMap R (QuotientField alpha beta) r := by
  change algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)
    (AdjoinRoot.mk (quotientPolynomial alpha beta)
      (MvPolynomial.finSuccEquiv R 4 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv R 4 (MvPolynomial.C r) =
    Polynomial.C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv R 4).commutes r]
  rfl

theorem quotientResidueMap_kernel (alpha beta : R) (p : MvPolynomial (Fin 5) R) :
    quotientResidueMap alpha beta p = 0 ↔ weightedHypersurface alpha beta ∣ p :=
  residue_fractionMap_kernel (quotientProjection alpha beta)
    (weightedHypersurface alpha beta) (quotientProjection_kernel alpha beta) p

omit [CharZero R] in
@[simp] theorem quotientResidueMap_X_zero (alpha beta : R) :
    quotientResidueMap alpha beta (MvPolynomial.X 0) =
      algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)
        (quotientRoot alpha beta) := by
  simp [quotientResidueMap]

omit [CharZero R] in
@[simp] theorem quotientResidueMap_X_succ (alpha beta : R) (i : Fin 4) :
    quotientResidueMap alpha beta (MvPolynomial.X i.succ) =
      algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)
        (quotientParameter alpha beta i) := by
  simp [quotientResidueMap]

theorem quotient_normal_ne_zero (alpha beta : R) :
    quotientResidueMap alpha beta (integerPartial 0 (weightedHypersurface alpha beta)) ≠ 0 := by
  intro h
  exact weightedHypersurface_not_dvd_partial_zero alpha beta
    ((quotientResidueMap_kernel alpha beta _).mp h)

/-- The genuine tangent derivations, obtained by quotient descent followed
by fraction-field extension. -/
def quotientTangent (alpha beta : R) (i : Fin 4) :
    Derivation ℤ (QuotientField alpha beta) (QuotientField alpha beta) :=
  residueTangent (K := QuotientField alpha beta) (quotientProjection alpha beta)
    (quotientProjection_surjective alpha beta) (integerPartial 0) (integerPartial i.succ)
    (weightedHypersurface alpha beta) (quotientProjection_kernel alpha beta)
    (quotient_normal_ne_zero alpha beta)

theorem quotientTangent_apply (alpha beta : R) (i : Fin 4)
    (p : MvPolynomial (Fin 5) R) :
    quotientTangent alpha beta i (quotientResidueMap alpha beta p) =
      quotientResidueMap alpha beta (integerPartial i.succ p) -
        quotientResidueMap alpha beta (integerPartial i.succ (weightedHypersurface alpha beta)) /
          quotientResidueMap alpha beta (integerPartial 0 (weightedHypersurface alpha beta)) *
            quotientResidueMap alpha beta (integerPartial 0 p) :=
  residueTangent_apply (K := QuotientField alpha beta) (quotientProjection alpha beta)
    (quotientProjection_surjective alpha beta) (integerPartial 0) (integerPartial i.succ)
    (weightedHypersurface alpha beta) (quotientProjection_kernel alpha beta)
    (quotient_normal_ne_zero alpha beta) p

theorem quotientTangents_commute (alpha beta : R) (i j : Fin 4) :
    Function.Commute (quotientTangent alpha beta i) (quotientTangent alpha beta j) :=
  residueTangent_commute (K := QuotientField alpha beta) (quotientProjection alpha beta)
    (quotientProjection_surjective alpha beta) (integerPartial 0) (integerPartial i.succ)
    (integerPartial j.succ) (weightedHypersurface alpha beta)
    (quotientProjection_kernel alpha beta) (quotient_normal_ne_zero alpha beta)
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0)
    (integerPartial_commute i.succ j.succ)

@[simp] theorem quotientTangent_constant (alpha beta : R) (i : Fin 4) (r : R) :
    quotientTangent alpha beta i (quotientResidueMap alpha beta (MvPolynomial.C r)) = 0 := by
  rw [quotientTangent_apply]
  simp

@[simp] theorem quotientTangent_algebraMap (alpha beta : R) (i : Fin 4) (r : R) :
    quotientTangent alpha beta i (algebraMap R (QuotientField alpha beta) r) = 0 := by
  rw [← quotientResidueMap_C, quotientTangent_constant]

theorem quotientTangent_parameter (alpha beta : R) (i j : Fin 4) :
    quotientTangent alpha beta i
      (algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)
        (quotientParameter alpha beta j)) = if j = i then 1 else 0 := by
  rw [← quotientResidueMap_X_succ, quotientTangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hij : j = i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs, hij]

theorem quotientTangent_root (alpha beta : R) (i : Fin 4) :
    quotientTangent alpha beta i
      (algebraMap (QuotientRing alpha beta) (QuotientField alpha beta)
        (quotientRoot alpha beta)) =
      -quotientResidueMap alpha beta (integerPartial i.succ (weightedHypersurface alpha beta)) /
        quotientResidueMap alpha beta (integerPartial 0 (weightedHypersurface alpha beta)) := by
  rw [← quotientResidueMap_X_zero, quotientTangent_apply,
    integerPartial_X_of_ne i.succ 0 (Ne.symm (Fin.succ_ne_zero i)),
    integerPartial_X_self]
  simp only [map_zero, map_one, mul_one, zero_sub, neg_div]

end Field

end HoldoutConstruction

#print axioms HoldoutConstruction.quotient_normal_ne_zero
#print axioms HoldoutConstruction.quotientTangents_commute
#print axioms HoldoutConstruction.quotientTangent_parameter
end
end

/- Source component: QuotientCoordinates -/
section
/-! Evaluation bridges between the actual quotient polynomial, its
canonical partial derivatives, and the polynomial conic's H/gradient. -/

noncomputable section

namespace HoldoutConstruction

open HoldoutConicIncidence

variable {R T : Type*} [CommRing R] [CommRing T]

theorem weightedHypersurface_eq_H (alpha beta : R) :
    weightedHypersurface alpha beta =
      H (MvPolynomial.C alpha) (MvPolynomial.C beta) MvPolynomial.X := rfl

theorem weightedHypersurface_eval₂ (f : R →+* T) (x : Fin 5 → T) (alpha beta : R) :
    MvPolynomial.eval₂Hom f x (weightedHypersurface alpha beta) =
      H (f alpha) (f beta) x := by
  simp [weightedHypersurface, H]

theorem weightedHypersurface_integerPartial (alpha beta : R) (i : Fin 5) :
    integerPartial i (weightedHypersurface alpha beta) =
      gradient (MvPolynomial.C alpha) (MvPolynomial.C beta) MvPolynomial.X i := by
  have hthree : MvPolynomial.pderiv i (3 : MvPolynomial (Fin 5) R) = 0 :=
    Derivation.map_natCast _ 3
  simp only [integerPartial_apply, weightedHypersurface, map_add, map_sub,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X, hthree]
  fin_cases i <;> norm_num [gradient, Pi.single_apply, Fin.ext_iff] <;> ring

theorem quotientGradient_eval₂ (f : R →+* T) (x : Fin 5 → T)
    (alpha beta : R) (i : Fin 5) :
    MvPolynomial.eval₂Hom f x
      (gradient (MvPolynomial.C alpha) (MvPolynomial.C beta) MvPolynomial.X i) =
      gradient (f alpha) (f beta) x i := by
  fin_cases i <;> simp [gradient]

theorem weightedHypersurface_integerPartial_eval₂ (f : R →+* T) (x : Fin 5 → T)
    (alpha beta : R) (i : Fin 5) :
    MvPolynomial.eval₂Hom f x (integerPartial i (weightedHypersurface alpha beta)) =
      gradient (f alpha) (f beta) x i := by
  rw [weightedHypersurface_integerPartial, quotientGradient_eval₂]

end HoldoutConstruction

#print axioms HoldoutConstruction.weightedHypersurface_integerPartial
#print axioms HoldoutConstruction.weightedHypersurface_integerPartial_eval₂
end
end
