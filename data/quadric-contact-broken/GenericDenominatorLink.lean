import Proposal.NumericDenominatorLink
import Proposal.GenericLineSpecialization
import Proposal.CubicDenominatorEvaluation

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
namespace QuadricContactGenericDenominator
open Polynomial QuadricContactRatioInverse QuadricContactRatioDenominator
open QuadricContactNumericDenominator

/-- The actual generic coefficient specialization alpha=1,beta=2, into C. -/
def coefficientToComplex : ParameterSpecialization.Coefficients →+* ℂ :=
  (Rat.castHom ℂ).comp ParameterSpecialization.specialize

theorem generic_polynomial_cast :
    ParameterEliminant.P.map coefficientToComplex = linePolynomial := by
  rw [coefficientToComplex, ← Polynomial.map_map,
    ParameterEliminant.P_specialize, QuadricContactRatioDataLink.polynomial_cast]

/-- The concrete generic-to-auxiliary algebra map. -/
def genericToComplex : ParameterEliminant.E →+* Auxiliary :=
  AdjoinRoot.map coefficientToComplex ParameterEliminant.P linePolynomial
    (generic_polynomial_cast ▸ dvd_refl linePolynomial)

theorem genericToComplex_eq :
    genericToComplex = numericToComplex.comp ParameterEliminant.toSpecial := by
  symm
  exact AdjoinRoot.map_comp_map _ _ _ _ _ _ _

theorem generic_sum_specializes :
    genericToComplex (GenericCubicLines.x + GenericCubicLines.y) = sumElement := by
  rw [genericToComplex_eq, RingHom.comp_apply, map_add,
    GenericCubicLines.toSpecial_x, GenericCubicLines.toSpecial_y, ← map_add,
    numericToComplex_mk, QuadricContactRatioDataLink.sum_cast]
  exact (AdjoinRoot.aeval_eq lineSum).symm

/-- The source matrix is exactly multiplication by the two generic line
coordinates in their monic power basis. -/
def genericSumMatrix : Matrix (Fin 27) (Fin 27) ParameterSpecialization.Coefficients :=
  Algebra.leftMulMatrix
    (AdjoinRootSpecialization.basis ParameterEliminant.P
      ParameterEliminant.P_monic ParameterEliminant.P_natDegree)
    (GenericCubicLines.x + GenericCubicLines.y)

theorem generic_matrix_specializes :
    genericSumMatrix.map coefficientToComplex = sumMatrix := by
  have h := map_leftMulMatrix_target coefficientToComplex ParameterEliminant.P linePolynomial
    ParameterEliminant.P_monic polynomial_monic ParameterEliminant.P_natDegree
    polynomial_degree generic_polynomial_cast (GenericCubicLines.x + GenericCubicLines.y)
  change genericSumMatrix.map coefficientToComplex =
    Algebra.leftMulMatrix basis (genericToComplex (GenericCubicLines.x + GenericCubicLines.y)) at h
  rw [generic_sum_specializes] at h
  exact h

def genericNormFiber : Polynomial ℂ :=
  ((2 * Polynomial.X ^ 2 : Polynomial ℂ) •
    (1 : Matrix (Fin 27) (Fin 27) (Polynomial ℂ)) -
    (genericSumMatrix.map coefficientToComplex).map Polynomial.C).det

theorem genericNormFiber_eq : genericNormFiber =
    ((2 * Polynomial.X ^ 2 : Polynomial ℂ) •
      (1 : Matrix (Fin 27) (Fin 27) (Polynomial ℂ)) - sumPolynomialMatrix).det := by
  rw [genericNormFiber, generic_matrix_specializes]
  rfl

/-- The actual generic determinant used by the cubic certificate. This definition
is definitionally equal to GenericCubicCertificate.D. -/
def activeDenominator : MvPolynomial (Fin 4) ParameterSpecialization.Coefficients :=
  QuadricContact.CubicMatrixCertificate.denominator
    (Algebra.leftMulMatrix
      (AdjoinRootSpecialization.basis ParameterEliminant.P
        ParameterEliminant.P_monic ParameterEliminant.P_natDegree))
    GenericCubicLines.x GenericCubicLines.y

theorem activeDenominator_fiber :
    MvPolynomial.eval₂Hom (Polynomial.C.comp coefficientToComplex)
      ![(2 : Polynomial ℂ) * Polynomial.X ^ 2, 0, 1, 1] activeDenominator =
      genericNormFiber := by
  exact QuadricContact.CubicMatrixCertificate.denominator_norm_fiber _ _ _ _

/-- Homogeneous coefficient clearing need only establish its scalar factor on
the fiber. The generic line algebra and the complete finite inverse witness
are concrete and kernel verified in the preceding links. -/
theorem denominator_legal (D : HodgeComputer.Poly) (κ : ℂ) (hκ : κ ≠ 0)
    (hD : (QuadricContactDenominator.toUni D).map QuadricContactDenominator.specialize =
      Polynomial.C κ * genericNormFiber) :
    IsRelPrime QuadricContactDenominator.targetF D := by
  apply QuadricContactRatioDenominator.denominator_legal D κ hκ
  simpa only [genericNormFiber_eq] using hD

/-- A directly usable version for simultaneous homogeneous clearing of the
actual generic determinant and its numerator coefficients. -/
theorem denominator_legal_of_active_fiber (D : HodgeComputer.Poly) (κ : ℂ) (hκ : κ ≠ 0)
    (hD : (QuadricContactDenominator.toUni D).map QuadricContactDenominator.specialize =
      Polynomial.C κ * MvPolynomial.eval₂Hom (Polynomial.C.comp coefficientToComplex)
        ![(2 : Polynomial ℂ) * Polynomial.X ^ 2, 0, 1, 1] activeDenominator) :
    IsRelPrime QuadricContactDenominator.targetF D := by
  apply denominator_legal D κ hκ
  simpa only [activeDenominator_fiber] using hD

end QuadricContactGenericDenominator

#print axioms QuadricContactGenericDenominator.generic_matrix_specializes
#print axioms QuadricContactGenericDenominator.denominator_legal
