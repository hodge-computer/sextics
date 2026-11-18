import Proposal.BundleBase
import Proposal.BundleCalculus
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/-! The actual quotient coordinate domain, fraction field, and four canonical
relative tangent derivations. The parameter direction is restored by the
full physical Jacobian. -/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

instance quotientRing_charZero : CharZero QuotientRing :=
  charZero_of_injective_ringHom (f := algebraMap BaseField QuotientRing)
    (algebraMap BaseField QuotientRing).injective

local instance : Algebra ℤ QuotientField := Ring.toIntAlgebra _

def quotientRoot : QuotientRing := AdjoinRoot.root (quotientPolynomial genericA genericB)
def quotientParameter (j : Fin 4) : QuotientRing :=
  AdjoinRoot.of (quotientPolynomial genericA genericB) (MvPolynomial.X j)

def quotientProjection : MvPolynomial (Fin 5) BaseField →+* QuotientRing :=
  (AdjoinRoot.mk (quotientPolynomial genericA genericB)).comp
    (MvPolynomial.finSuccEquiv BaseField 4).toRingHom

theorem quotientProjection_surjective : Function.Surjective quotientProjection :=
  (AdjoinRoot.mk_surjective (g := quotientPolynomial genericA genericB)).comp
    (MvPolynomial.finSuccEquiv BaseField 4).surjective

theorem quotientProjection_kernel (p : MvPolynomial (Fin 5) BaseField) :
    quotientProjection p=0 ↔ kPoly genericA genericB ∣ p := by
  change AdjoinRoot.mk (quotientPolynomial genericA genericB)
    (MvPolynomial.finSuccEquiv BaseField 4 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← kPoly_univariate genericA genericB]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv BaseField 4)

@[simp] theorem quotientProjection_X_zero :
    quotientProjection (MvPolynomial.X 0)=quotientRoot := by
  change AdjoinRoot.mk (quotientPolynomial genericA genericB)
    (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.X 0))=_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rfl

@[simp] theorem quotientProjection_X_succ (j : Fin 4) :
    quotientProjection (MvPolynomial.X j.succ)=quotientParameter j := by
  change AdjoinRoot.mk (quotientPolynomial genericA genericB)
    (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.X j.succ))=_
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

def quotientAxis : MvPolynomial (Fin 5) BaseField →+* Polynomial BaseField :=
  MvPolynomial.eval₂Hom C ![X,0,0,0,0]

theorem quotientAxis_equation : quotientAxis (kPoly genericA genericB)=X^6 := by
  simp [quotientAxis,kPoly,K]

theorem quotientAxis_gradient :
    quotientAxis (integerPartial 0 (kPoly genericA genericB))=6*X^5 := by
  rw [integerPartial_apply,kPoly_pderiv]
  simp [quotientAxis,gradient]

theorem quotient_equation_not_dvd_partial_zero :
    ¬ kPoly genericA genericB ∣ integerPartial 0 (kPoly genericA genericB) := by
  intro hd
  have hm := map_dvd quotientAxis hd
  rw [quotientAxis_equation,quotientAxis_gradient] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

def quotientResidueMap : MvPolynomial (Fin 5) BaseField →+* QuotientField :=
  (algebraMap QuotientRing QuotientField).comp quotientProjection

@[simp] theorem quotientResidueMap_C (r : BaseField) :
    quotientResidueMap (MvPolynomial.C r)=algebraMap BaseField QuotientField r := by
  change algebraMap QuotientRing QuotientField
    (AdjoinRoot.mk (quotientPolynomial genericA genericB)
      (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.C r)))=_
  rw [show MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.C r)=
    C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv BaseField 4).commutes r]
  rfl

theorem quotientResidueMap_kernel (p : MvPolynomial (Fin 5) BaseField) :
    quotientResidueMap p=0 ↔ kPoly genericA genericB ∣ p :=
  residue_fractionMap_kernel quotientProjection (kPoly genericA genericB)
    quotientProjection_kernel p

@[simp] theorem quotientResidueMap_X_zero :
    quotientResidueMap (MvPolynomial.X 0)=
      algebraMap QuotientRing QuotientField quotientRoot := by
  simp [quotientResidueMap]

@[simp] theorem quotientResidueMap_X_succ (j : Fin 4) :
    quotientResidueMap (MvPolynomial.X j.succ)=
      algebraMap QuotientRing QuotientField (quotientParameter j) := by
  simp [quotientResidueMap]

theorem quotient_normal_ne_zero :
    quotientResidueMap (integerPartial 0 (kPoly genericA genericB)) ≠ 0 := by
  intro h
  exact quotient_equation_not_dvd_partial_zero ((quotientResidueMap_kernel _).mp h)

def quotientTangent (j : Fin 4) : Derivation ℤ QuotientField QuotientField :=
  residueTangent (K := QuotientField) quotientProjection quotientProjection_surjective
    (integerPartial 0) (integerPartial j.succ) (kPoly genericA genericB)
    quotientProjection_kernel quotient_normal_ne_zero

theorem quotientTangent_apply (j : Fin 4) (p : MvPolynomial (Fin 5) BaseField) :
    quotientTangent j (quotientResidueMap p)=
      quotientResidueMap (integerPartial j.succ p)-
        quotientResidueMap (integerPartial j.succ (kPoly genericA genericB))/
          quotientResidueMap (integerPartial 0 (kPoly genericA genericB))*
            quotientResidueMap (integerPartial 0 p) :=
  residueTangent_apply (K := QuotientField) quotientProjection quotientProjection_surjective
    (integerPartial 0) (integerPartial j.succ) (kPoly genericA genericB)
    quotientProjection_kernel quotient_normal_ne_zero p

theorem quotientTangents_commute (i j : Fin 4) :
    Function.Commute (quotientTangent i) (quotientTangent j) :=
  residueTangent_commute (K := QuotientField) quotientProjection quotientProjection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ)
    (kPoly genericA genericB) quotientProjection_kernel quotient_normal_ne_zero
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0)
    (integerPartial_commute i.succ j.succ)

@[simp] theorem quotientTangent_constant (j : Fin 4) (r : BaseField) :
    quotientTangent j (quotientResidueMap (MvPolynomial.C r))=0 := by
  rw [quotientTangent_apply]
  simp

@[simp] theorem quotientTangent_algebraMap (j : Fin 4) (r : BaseField) :
    quotientTangent j (algebraMap BaseField QuotientField r)=0 := by
  rw [← quotientResidueMap_C,quotientTangent_constant]

theorem quotientTangent_parameter (i j : Fin 4) :
    quotientTangent i (algebraMap QuotientRing QuotientField (quotientParameter j))=
      if j=i then 1 else 0 := by
  rw [← quotientResidueMap_X_succ,quotientTangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero,mul_zero,sub_zero]
  by_cases hij : j=i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs,hij]

theorem quotientTangent_root (i : Fin 4) :
    quotientTangent i (algebraMap QuotientRing QuotientField quotientRoot)=
      -quotientResidueMap (integerPartial i.succ (kPoly genericA genericB))/
        quotientResidueMap (integerPartial 0 (kPoly genericA genericB)) := by
  rw [← quotientResidueMap_X_zero,quotientTangent_apply,
    integerPartial_X_of_ne i.succ 0 (Ne.symm (Fin.succ_ne_zero i)),integerPartial_X_self]
  simp only [map_zero,map_one,mul_one,zero_sub,neg_div]

end HoldoutBundle

#print axioms HoldoutBundle.quotient_normal_ne_zero
#print axioms HoldoutBundle.quotientTangents_commute
