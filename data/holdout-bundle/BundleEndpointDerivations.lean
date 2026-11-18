import Proposal.BundleBase
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives

/-!
Three commuting derivations on the actual generic endpoint field. They
differentiate the independent endpoint parameters c2,p0,q0, while the
simple endpoint root c0 is differentiated by its defining equation.
This is the explicit application of fqlx's shared quotient-derivation API.
-/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

section Coordinates
variable {R : Type*} [CommRing R]

def endpointEquation (a b : R) : MvPolynomial (Fin 4) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
    MvPolynomial.C a * MvPolynomial.X 2^3 + MvPolynomial.C b * MvPolynomial.X 3^3

theorem endpointEquation_univariate (a b : R) :
    MvPolynomial.finSuccEquiv R 3 (endpointEquation a b) = endpointPolynomial a b := by
  have he : Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 3) R))
      (fun j => Polynomial.C (MvPolynomial.X j)) =
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0),
        Polynomial.C (MvPolynomial.X 1), Polynomial.C (MvPolynomial.X 2)] := by
    funext i
    fin_cases i <;> rfl
  simp [endpointEquation, endpointPolynomial, MvPolynomial.finSuccEquiv_apply, he]
  ring

def endpointQuotient (a b : R) : MvPolynomial (Fin 4) R →+* EndpointCoordinateRing a b :=
  (AdjoinRoot.mk (endpointPolynomial a b)).comp (MvPolynomial.finSuccEquiv R 3).toRingHom

theorem endpointQuotient_surjective (a b : R) : Function.Surjective (endpointQuotient a b) :=
  (AdjoinRoot.mk_surjective (g := endpointPolynomial a b)).comp
    (MvPolynomial.finSuccEquiv R 3).surjective

theorem endpointQuotient_kernel (a b : R) (p : MvPolynomial (Fin 4) R) :
    endpointQuotient a b p = 0 ↔ endpointEquation a b ∣ p := by
  change AdjoinRoot.mk (endpointPolynomial a b) (MvPolynomial.finSuccEquiv R 3 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← endpointEquation_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv R 3)

@[simp] theorem endpointQuotient_X_zero (a b : R) :
    endpointQuotient a b (MvPolynomial.X (0 : Fin 4)) = endpointRoot a b := by
  simp [endpointQuotient, endpointRoot, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem endpointQuotient_X_succ (a b : R) (i : Fin 3) :
    endpointQuotient a b (MvPolynomial.X i.succ) = endpointParameter a b i := by
  change AdjoinRoot.mk (endpointPolynomial a b)
    (MvPolynomial.finSuccEquiv R 3 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

theorem endpointEquation_partial_zero (a b : R) :
    integerPartial 0 (endpointEquation a b) = 6 * MvPolynomial.X 0^5 := by
  simp [integerPartial_apply, endpointEquation, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, smul_eq_mul] <;> ring

end Coordinates

local instance : Algebra ℤ EndpointField := Ring.toIntAlgebra _

def endpointResidueMap : MvPolynomial (Fin 4) BaseField →+* EndpointField :=
  (algebraMap GenericEndpoint EndpointField).comp (endpointQuotient genericA genericB)

@[simp] theorem endpointResidueMap_C (r : BaseField) :
    endpointResidueMap (MvPolynomial.C r) = algebraMap BaseField EndpointField r := by
  change algebraMap GenericEndpoint EndpointField
    (AdjoinRoot.mk (endpointPolynomial genericA genericB)
      (MvPolynomial.finSuccEquiv BaseField 3 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv BaseField 3 (MvPolynomial.C r) =
    Polynomial.C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv BaseField 3).commutes r]
  rfl

theorem endpointResidueMap_kernel (p : MvPolynomial (Fin 4) BaseField) :
    endpointResidueMap p = 0 ↔ endpointEquation genericA genericB ∣ p :=
  residue_fractionMap_kernel (endpointQuotient genericA genericB)
    (endpointEquation genericA genericB) (endpointQuotient_kernel genericA genericB) p

@[simp] theorem endpointResidueMap_X_zero :
    endpointResidueMap (MvPolynomial.X (0 : Fin 4)) =
      algebraMap GenericEndpoint EndpointField (endpointRoot genericA genericB) := by
  simp [endpointResidueMap]

@[simp] theorem endpointResidueMap_X_succ (i : Fin 3) :
    endpointResidueMap (MvPolynomial.X i.succ) =
      algebraMap GenericEndpoint EndpointField (endpointParameter genericA genericB i) := by
  simp [endpointResidueMap]

theorem endpointResidue_root_ne_zero :
    algebraMap GenericEndpoint EndpointField (endpointRoot genericA genericB) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective GenericEndpoint EndpointField).ne
      (endpointRoot_ne_zero genericA genericB)

theorem endpoint_normal_ne_zero :
    endpointResidueMap (integerPartial 0 (endpointEquation genericA genericB)) ≠ 0 := by
  rw [endpointEquation_partial_zero, map_mul, map_ofNat, map_pow, endpointResidueMap_X_zero]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 5 endpointResidue_root_ne_zero)

def endpointTangent (i : Fin 3) : Derivation ℤ EndpointField EndpointField :=
  residueTangent (K := EndpointField) (endpointQuotient genericA genericB)
    (endpointQuotient_surjective genericA genericB) (integerPartial 0) (integerPartial i.succ)
    (endpointEquation genericA genericB) (endpointQuotient_kernel genericA genericB)
    endpoint_normal_ne_zero

theorem endpointTangent_apply (i : Fin 3) (p : MvPolynomial (Fin 4) BaseField) :
    endpointTangent i (endpointResidueMap p) =
      endpointResidueMap (integerPartial i.succ p) -
        endpointResidueMap (integerPartial i.succ (endpointEquation genericA genericB)) /
          endpointResidueMap (integerPartial 0 (endpointEquation genericA genericB)) *
            endpointResidueMap (integerPartial 0 p) :=
  residueTangent_apply (K := EndpointField) (endpointQuotient genericA genericB)
    (endpointQuotient_surjective genericA genericB) (integerPartial 0) (integerPartial i.succ)
    (endpointEquation genericA genericB) (endpointQuotient_kernel genericA genericB)
    endpoint_normal_ne_zero p

theorem endpointTangents_commute (i j : Fin 3) :
    Function.Commute (endpointTangent i) (endpointTangent j) :=
  residueTangent_commute (K := EndpointField) (endpointQuotient genericA genericB)
    (endpointQuotient_surjective genericA genericB) (integerPartial 0)
    (integerPartial i.succ) (integerPartial j.succ) (endpointEquation genericA genericB)
    (endpointQuotient_kernel genericA genericB) endpoint_normal_ne_zero
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0)
    (integerPartial_commute i.succ j.succ)

@[simp] theorem endpointTangent_constant (i : Fin 3) (r : BaseField) :
    endpointTangent i (endpointResidueMap (MvPolynomial.C r)) = 0 := by
  rw [endpointTangent_apply]
  simp

@[simp] theorem endpointTangent_algebraMap (i : Fin 3) (r : BaseField) :
    endpointTangent i (algebraMap BaseField EndpointField r) = 0 := by
  rw [← endpointResidueMap_C, endpointTangent_constant]

theorem endpointTangent_parameter (i j : Fin 3) :
    endpointTangent i
      (algebraMap GenericEndpoint EndpointField (endpointParameter genericA genericB j)) =
        if j = i then 1 else 0 := by
  rw [← endpointResidueMap_X_succ, endpointTangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hij : j = i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs, hij]

end HoldoutBundle

#print axioms HoldoutBundle.endpoint_normal_ne_zero
#print axioms HoldoutBundle.endpointTangents_commute
#print axioms HoldoutBundle.endpointTangent_parameter
