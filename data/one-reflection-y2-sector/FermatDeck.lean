import Proposal.CommonCoverBaseChange
import HodgeComputer.Constructions.HoldoutCover.FermatFields

/- Source component: FermatDeck -/
section
/-!
An explicit deck automorphism on the integral common cover over the
generic Fermat base. Both Fermat coordinates scale inversely to T, so the
physical coordinates and the exact holdout equation are fixed. Prepared
with OpenAI ChatGPT assistance for a contribution through GitHub account
fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero

/-- Scaling of the Fermat coordinate ring extended to its fraction field. -/
def genericBaseScaleEquiv (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    FermatCoefficientField K ≃+* FermatCoefficientField K :=
  IsFractionRing.ringEquivOfRingEquiv (fermatBaseScaleEquiv z hz hz0)

omit [CharZero K] in
@[simp] theorem genericBaseScaleEquiv_coefficient
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) (c : K) :
    genericBaseScaleEquiv z hz hz0
      (algebraMap K (FermatCoefficientField K) c) =
      algebraMap K (FermatCoefficientField K) c := by
  rw [IsScalarTower.algebraMap_apply K (FermatBaseRing K) (FermatCoefficientField K)]
  dsimp [genericBaseScaleEquiv]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (FermatBaseRing K) (FermatCoefficientField K)
    (fermatBaseScale z hz (algebraMap K (FermatBaseRing K) c)) = _
  rw [fermatBaseScale_coefficient]

omit [CharZero K] in
@[simp] theorem genericBaseScaleEquiv_alpha
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    genericBaseScaleEquiv z hz hz0 (genericBaseAlpha K) =
      algebraMap K (FermatCoefficientField K) z * genericBaseAlpha K := by
  dsimp [genericBaseScaleEquiv, genericBaseAlpha]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (FermatBaseRing K) (FermatCoefficientField K)
    (fermatBaseScale z hz baseAlpha) = _
  rw [fermatBaseScale_alpha, map_mul,
    ← IsScalarTower.algebraMap_apply K (FermatBaseRing K) (FermatCoefficientField K)]

omit [CharZero K] in
@[simp] theorem genericBaseScaleEquiv_beta
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    genericBaseScaleEquiv z hz hz0 (genericBaseBeta K) =
      algebraMap K (FermatCoefficientField K) z * genericBaseBeta K := by
  dsimp [genericBaseScaleEquiv, genericBaseBeta]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap (FermatBaseRing K) (FermatCoefficientField K)
    (fermatBaseScale z hz baseBeta) = _
  rw [fermatBaseScale_beta, map_mul,
    ← IsScalarTower.algebraMap_apply K (FermatBaseRing K) (FermatCoefficientField K)]

/-- Inverse base scaling followed by forward T scaling. -/
def commonDeckCoefficientEquiv (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    MvPolynomial (Fin 4) (FermatCoefficientField K) ≃+*
      MvPolynomial (Fin 4) (FermatCoefficientField K) :=
  (MvPolynomial.mapEquiv (Fin 4)
    (genericBaseScaleEquiv z⁻¹ (by rw [inv_pow, hz, inv_one]) (inv_ne_zero hz0))).trans
      (scaleLastVariableEquiv (algebraMap K (FermatCoefficientField K) z)
        ((map_ne_zero (algebraMap K (FermatCoefficientField K))).2 hz0))

@[simp] theorem commonDeckCoefficientEquiv_C
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) (c : FermatCoefficientField K) :
    commonDeckCoefficientEquiv z hz hz0 (MvPolynomial.C c) =
      MvPolynomial.C
        (genericBaseScaleEquiv z⁻¹ (by rw [inv_pow, hz, inv_one]) (inv_ne_zero hz0) c) := by
  simp [commonDeckCoefficientEquiv, RingEquiv.trans_apply,
    MvPolynomial.mapEquiv_apply]

@[simp] theorem commonDeckCoefficientEquiv_X
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) (i : Fin 4) :
    commonDeckCoefficientEquiv z hz hz0 (MvPolynomial.X i) =
      ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
        MvPolynomial.C (algebraMap K (FermatCoefficientField K) z)*MvPolynomial.X 3] i := by
  simp [commonDeckCoefficientEquiv, RingEquiv.trans_apply,
    MvPolynomial.mapEquiv_apply]

/-- The complete common-cover polynomial is invariant. -/
theorem commonDeck_polynomial (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K)).map
      (commonDeckCoefficientEquiv z hz hz0) =
      commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K) := by
  let c := algebraMap K (FermatCoefficientField K) z
  let e := genericBaseScaleEquiv z⁻¹
    (show (z⁻¹)^6=1 by rw [inv_pow, hz, inv_one]) (inv_ne_zero hz0)
  have hc : c^6 = 1 := by dsimp [c]; rw [← map_pow, hz, map_one]
  have ha : c * e (genericBaseAlpha K) = genericBaseAlpha K := by
    dsimp [c, e]
    rw [genericBaseScaleEquiv_alpha, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hz0, map_one, one_mul]
  have hb : c * e (genericBaseBeta K) = genericBaseBeta K := by
    dsimp [c, e]
    rw [genericBaseScaleEquiv_beta, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hz0, map_one, one_mul]
  let C2 : FermatCoefficientField K →+*
      Polynomial (MvPolynomial (Fin 4) (FermatCoefficientField K)) :=
    Polynomial.C.comp MvPolynomial.C
  have hca := congrArg C2 ha
  have hcb := congrArg C2 hb
  have hcc := congrArg C2 hc
  simp only [map_mul, map_pow, map_one] at hca hcb hcc
  dsimp only [C2, c, e] at hca hcb hcc
  simp only [RingHom.comp_apply] at hca hcb hcc
  simp only [commonCoverPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    map_add, map_mul, map_pow, RingEquiv.coe_toRingHom, commonDeckCoefficientEquiv_C,
    commonDeckCoefficientEquiv_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  change _ = _
  linear_combination
    (C (MvPolynomial.X 0)*C (MvPolynomial.X 2)*C (MvPolynomial.X 3)*X^3)*hca +
    (C (MvPolynomial.X 0)^3*C (MvPolynomial.X 1)*C (MvPolynomial.X 2)*
      C (MvPolynomial.X 3))*hca + C (MvPolynomial.X 3)^6*hcc

/-- A genuine ring automorphism of the integral common cover. -/
def commonDeckRingEquiv (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    GenericCommonCoverRing K ≃+* GenericCommonCoverRing K :=
  AdjoinRoot.mapRingEquiv (commonDeckCoefficientEquiv z hz hz0)
    (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K))
    (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K))
    (by rw [commonDeck_polynomial])

@[simp] theorem commonDeckRingEquiv_root
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    commonDeckRingEquiv z hz hz0
      (AdjoinRoot.root (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K))) =
      AdjoinRoot.root (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K)) := by
  simp [commonDeckRingEquiv]

@[simp] theorem commonDeckRingEquiv_of
    (z : K) (hz : z^6=1) (hz0 : z ≠ 0)
    (p : MvPolynomial (Fin 4) (FermatCoefficientField K)) :
    commonDeckRingEquiv z hz hz0 (AdjoinRoot.of _ p) =
      AdjoinRoot.of _ (commonDeckCoefficientEquiv z hz hz0 p) := by
  simp [commonDeckRingEquiv]

end HoldoutConstruction

#print axioms HoldoutConstruction.commonDeck_polynomial
#print axioms HoldoutConstruction.commonDeckRingEquiv
end
end
