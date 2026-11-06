import Proposal.CoverFields
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/- Source component: PhysicalDerivations -/
section
/-!
The exact physical holdout residue chart. The distinguished coordinate is
X0; the five independent coordinates are X1, X2, Y0, Y1, Y2. The derivations
are actual quotient/fraction-field derivations, not formal differential
symbols or additional hypotheses.
-/

noncomputable section

namespace HoldoutConstruction

attribute [local instance] holdoutCoordinateRing_isDomain

local instance physicalDerivations_intHoldoutFunctionFieldAlgebra : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _

def physicalRoot : HoldoutCoordinateRing :=
  AdjoinRoot.root (holdoutPolynomial (R := ℂ))

def physicalParameter (i : Fin 5) : HoldoutCoordinateRing :=
  AdjoinRoot.of (holdoutPolynomial (R := ℂ)) (MvPolynomial.X i)

def physicalProjection : MvPolynomial (Fin 6) ℂ →+* HoldoutCoordinateRing :=
  (AdjoinRoot.mk (holdoutPolynomial (R := ℂ))).comp
    (MvPolynomial.finSuccEquiv ℂ 5).toRingHom

theorem physicalProjection_surjective : Function.Surjective physicalProjection :=
  (AdjoinRoot.mk_surjective (g := holdoutPolynomial (R := ℂ))).comp
    (MvPolynomial.finSuccEquiv ℂ 5).surjective

theorem physicalProjection_kernel (p : MvPolynomial (Fin 6) ℂ) :
    physicalProjection p = 0 ↔ holdoutSextic ∣ p := by
  change AdjoinRoot.mk (holdoutPolynomial (R := ℂ))
    (MvPolynomial.finSuccEquiv ℂ 5 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← holdoutSextic_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)

@[simp] theorem physicalProjection_X_zero :
    physicalProjection (MvPolynomial.X 0) = physicalRoot := by
  change AdjoinRoot.mk (holdoutPolynomial (R := ℂ))
    (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rfl

@[simp] theorem physicalProjection_X_succ (i : Fin 5) :
    physicalProjection (MvPolynomial.X i.succ) = physicalParameter i := by
  change AdjoinRoot.mk (holdoutPolynomial (R := ℂ))
    (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

def physicalResidueMap : MvPolynomial (Fin 6) ℂ →+* HoldoutFunctionField :=
  (algebraMap HoldoutCoordinateRing HoldoutFunctionField).comp physicalProjection

theorem physicalResidueMap_kernel (p : MvPolynomial (Fin 6) ℂ) :
    physicalResidueMap p = 0 ↔ holdoutSextic ∣ p :=
  residue_fractionMap_kernel physicalProjection holdoutSextic physicalProjection_kernel p

@[simp] theorem physicalResidueMap_C (c : ℂ) :
    physicalResidueMap (MvPolynomial.C c) = algebraMap ℂ HoldoutFunctionField c := by
  change algebraMap HoldoutCoordinateRing HoldoutFunctionField
    (AdjoinRoot.mk (holdoutPolynomial (R := ℂ))
      (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c))) = _
  rw [show MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C c) =
    Polynomial.C (MvPolynomial.C c) from (MvPolynomial.finSuccEquiv ℂ 5).commutes c]
  rfl

@[simp] theorem physicalResidueMap_X_zero :
    physicalResidueMap (MvPolynomial.X 0) =
      algebraMap HoldoutCoordinateRing HoldoutFunctionField physicalRoot := by
  simp [physicalResidueMap]

@[simp] theorem physicalResidueMap_X_succ (i : Fin 5) :
    physicalResidueMap (MvPolynomial.X i.succ) =
      algebraMap HoldoutCoordinateRing HoldoutFunctionField (physicalParameter i) := by
  simp [physicalResidueMap]

theorem physical_normal_ne_zero :
    physicalResidueMap (integerPartial 0 holdoutSextic) ≠ 0 := by
  intro h
  exact holdoutSextic_not_dvd_pderiv_zero
    ((physicalResidueMap_kernel _).mp h)

/-- Five commuting tangent derivations of the exact holdout function field. -/
def physicalTangent (i : Fin 5) : Derivation ℤ HoldoutFunctionField HoldoutFunctionField :=
  residueTangent (K := HoldoutFunctionField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) holdoutSextic
    physicalProjection_kernel physical_normal_ne_zero

theorem physicalTangent_apply (i : Fin 5) (p : MvPolynomial (Fin 6) ℂ) :
    physicalTangent i (physicalResidueMap p) =
      physicalResidueMap (integerPartial i.succ p) -
        physicalResidueMap (integerPartial i.succ holdoutSextic) /
          physicalResidueMap (integerPartial 0 holdoutSextic) *
            physicalResidueMap (integerPartial 0 p) :=
  residueTangent_apply (K := HoldoutFunctionField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) holdoutSextic
    physicalProjection_kernel physical_normal_ne_zero p

theorem physicalTangents_commute (i j : Fin 5) :
    Function.Commute (physicalTangent i) (physicalTangent j) :=
  residueTangent_commute (K := HoldoutFunctionField) physicalProjection physicalProjection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) holdoutSextic
    physicalProjection_kernel physical_normal_ne_zero
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0)
    (integerPartial_commute i.succ j.succ)

@[simp] theorem physicalTangent_constant (i : Fin 5) (c : ℂ) :
    physicalTangent i (physicalResidueMap (MvPolynomial.C c)) = 0 := by
  rw [physicalTangent_apply]
  simp

@[simp] theorem physicalTangent_algebraMap (i : Fin 5) (c : ℂ) :
    physicalTangent i (algebraMap ℂ HoldoutFunctionField c) = 0 := by
  rw [← physicalResidueMap_C, physicalTangent_constant]

theorem physicalTangent_parameter (i j : Fin 5) :
    physicalTangent i
      (algebraMap HoldoutCoordinateRing HoldoutFunctionField (physicalParameter j)) =
        if j = i then 1 else 0 := by
  rw [← physicalResidueMap_X_succ, physicalTangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hij : j = i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs, hij]

theorem physicalTangent_root (i : Fin 5) :
    physicalTangent i (algebraMap HoldoutCoordinateRing HoldoutFunctionField physicalRoot) =
      -physicalResidueMap (integerPartial i.succ holdoutSextic) /
        physicalResidueMap (integerPartial 0 holdoutSextic) := by
  rw [← physicalResidueMap_X_zero, physicalTangent_apply,
    integerPartial_X_of_ne i.succ 0 (Ne.symm (Fin.succ_ne_zero i)),
    integerPartial_X_self]
  simp only [map_zero, map_one, mul_one, zero_sub, neg_div]

end HoldoutConstruction

#print axioms HoldoutConstruction.physical_normal_ne_zero
#print axioms HoldoutConstruction.physicalTangents_commute
#print axioms HoldoutConstruction.physicalTangent_parameter
end
end
