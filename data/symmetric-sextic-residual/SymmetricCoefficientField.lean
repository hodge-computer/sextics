import Proposal.SymmetricCoefficientReduction
import Proposal.SymmetricCertificateTransport
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Degree.Units

/-!
# The actual coefficient field and its residual primitive equation

The three coefficient derivatives determine a rational vector field by a
three-by-three adjugate. Its denominator is proved nonzero on the actual
reflection hypersurface. No expanded inverse matrix is needed.

The final equivalence reduces the existing relative-primitive obligation
to the specific source `2*div(W)/f_u`, where every coefficient of `W` is
defined here. It does not assert that this last source has a primitive.
-/

noncomputable section

namespace SymmetricCoefficientField

open MvPolynomial HoldoutConstruction WeightedPrimitiveTransport
open SymmetricAffineField SymmetricPrimitiveEndpoint
open SymmetricCoefficientReduction ResidueCoefficientReduction
open scoped BigOperators Matrix

set_option maxHeartbeats 2000000

@[local simp] theorem partial_two (i : Fin 5) :
    (pderiv i : Derivation ℂ Poly Poly) (2 : Poly) = 0 :=
  (pderiv i).map_natCast 2

@[local simp] theorem partial_thirty (i : Fin 5) :
    (pderiv i : Derivation ℂ Poly Poly) (30 : Poly) = 0 :=
  (pderiv i).map_natCast 30

def leftBase : Poly := 1+2*X 1
def rightBase : Poly := X 2^2+2*X 2*X 3
def leadingCoefficient : Poly := 2+2*X 0^6-C (5/7:ℂ)*X 0^2-C (10/7:ℂ)*X 0^4

def equationCoefficient : Fin 3 → Poly := ![
  2+X 1^6+2*X 2^6+X 3^6+C (5/7:ℂ)*leftBase^2*rightBase+
    C (10/7:ℂ)*leftBase*rightBase^2,
  30+30*X 0^2*X 2^4+C (5/7:ℂ)*(-X 0^2*leftBase^2-2*leftBase*rightBase)+
    C (10/7:ℂ)*(-2*X 0^2*leftBase*rightBase-rightBase^2),
  30+30*X 0^4*X 2^2+C (5/7:ℂ)*(rightBase+2*X 0^2*leftBase)+
    C (10/7:ℂ)*(X 0^4*leftBase+2*X 0^2*rightBase)]

def sourceCoefficient : Fin 3 → Poly := ![
  X 1*X 3*X 2^2,
  -X 1*X 3*(X 2^2+X 0^2),
  X 1*X 3*X 0^2]

def coefficientMatrix : Matrix (Fin 3) (Fin 3) Poly :=
  fun i j => basePartial j (equationCoefficient i)

def coefficientDenominator : Poly := coefficientMatrix.det

def coefficientNumerator : Fin 3 → Poly :=
  coefficientMatrix.adjugate.mulVec sourceCoefficient

theorem equation_coefficients : rawWeighted =
    leadingCoefficient*X 4^3 + equationCoefficient 2*X 4^2+
      equationCoefficient 1*X 4+equationCoefficient 0 := by
  simp [rawWeighted, leftQuadric, rightQuadric, leadingCoefficient,
    equationCoefficient, leftBase, rightBase, map_ofNat]
  ring

theorem source_coefficients : rawSource =
    sourceCoefficient 2*X 4^2+sourceCoefficient 1*X 4+sourceCoefficient 0 := by
  simp [rawSource, sourceCoefficient]
  ring

theorem normal_equationCoefficient (i : Fin 3) :
    normalPartial (equationCoefficient i) = 0 := by
  fin_cases i <;>
    simp [normalPartial, equationCoefficient, leftBase, rightBase,
      pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply]

theorem normal_sourceCoefficient (i : Fin 3) :
    normalPartial (sourceCoefficient i) = 0 := by
  fin_cases i <;>
    simp [normalPartial, sourceCoefficient, pderiv_mul, pderiv_pow,
      pderiv_X, Pi.single_apply]

theorem squareLift_equationCoefficient (i : Fin 3) :
    squareLift (equationCoefficient i) = equationCoefficient i := by
  fin_cases i <;> simp [equationCoefficient, leftBase, rightBase, map_ofNat]

theorem normal_coefficientMatrix (i j : Fin 3) :
    normalPartial (coefficientMatrix i j) = 0 := by
  rw [coefficientMatrix, normal_base_commute, normal_equationCoefficient, map_zero]

theorem squareLift_coefficientMatrix (i j : Fin 3) :
    squareLift (coefficientMatrix i j) = coefficientMatrix i j := by
  change squareLift (pderiv j.succ.castSucc (equationCoefficient i)) = _
  rw [← tangent_squareLift j.succ, squareLift_equationCoefficient]
  rfl

theorem normal_denominator : normalPartial coefficientDenominator = 0 := by
  rw [coefficientDenominator, Matrix.det_fin_three]
  simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul,
    normal_coefficientMatrix, zero_mul, mul_zero, add_zero, sub_self]

theorem squareLift_denominator : squareLift coefficientDenominator = coefficientDenominator := by
  rw [coefficientDenominator, RingHom.map_det]
  congr 1
  funext i j
  exact squareLift_coefficientMatrix i j

theorem normal_adjugate (i j : Fin 3) :
    normalPartial (coefficientMatrix.adjugate i j) = 0 := by
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [Derivation.leibniz, smul_eq_mul, normal_coefficientMatrix]

theorem normal_numerator (i : Fin 3) :
    normalPartial (coefficientNumerator i) = 0 := by
  simp only [coefficientNumerator, Matrix.mulVec, dotProduct, map_sum,
    Derivation.leibniz, smul_eq_mul, normal_adjugate,
    normal_sourceCoefficient, mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero]

theorem coefficient_matching (k : Fin 3) :
    (∑ i, coefficientNumerator i*coefficientMatrix k i) =
      coefficientDenominator*sourceCoefficient k := by
  have h := Matrix.mulVec_mulVec sourceCoefficient coefficientMatrix coefficientMatrix.adjugate
  rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have hk := congrFun h k
  simpa only [coefficientNumerator, coefficientDenominator, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using hk

theorem base_leadingCoefficient (i : Fin 3) : basePartial i leadingCoefficient = 0 := by
  fin_cases i <;>
    simp [basePartial, leadingCoefficient, pderiv_mul, pderiv_pow, pderiv_X,
      Pi.single_apply]

theorem base_normalCoordinate (i : Fin 3) : basePartial i (X 4) = 0 := by
  fin_cases i <;> simp [basePartial]

theorem base_equation (i : Fin 3) : basePartial i rawWeighted =
    coefficientMatrix 2 i*X 4^2+coefficientMatrix 1 i*X 4+coefficientMatrix 0 i := by
  rw [equation_coefficients]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    base_normalCoordinate, base_leadingCoefficient, zero_mul, mul_zero,
    add_zero, zero_add, coefficientMatrix]
  ring

/-- The adjugate supplies the exact polynomial coefficient identity. -/
theorem equation_matching :
    (∑ i, coefficientNumerator i*basePartial i rawWeighted) =
      coefficientDenominator*rawSource := by
  simp_rw [base_equation]
  calc
    _ = (∑ i, coefficientNumerator i*coefficientMatrix 2 i)*X 4^2+
        (∑ i, coefficientNumerator i*coefficientMatrix 1 i)*X 4+
        (∑ i, coefficientNumerator i*coefficientMatrix 0 i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ = coefficientDenominator*rawSource := by
      rw [coefficient_matching, coefficient_matching, coefficient_matching, source_coefficients]
      ring

/-! ## A nonzero denominator in the actual quotient field -/

def specialize : Poly →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C ![0,1,1,2,Polynomial.X]

theorem specialize_matrix : specialize.mapMatrix coefficientMatrix =
    !![Polynomial.C (842/7:ℂ), Polynomial.C (2154/7:ℂ), Polynomial.C (2034/7:ℂ);
       Polynomial.C (-100/7:ℂ), Polynomial.C (-780/7:ℂ), Polynomial.C (-260/7:ℂ);
       0, Polynomial.C (30/7:ℂ), Polynomial.C (10/7:ℂ)] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [RingHom.mapMatrix_apply, Matrix.map_apply, coefficientMatrix, basePartial, equationCoefficient,
      leftBase, rightBase, specialize, pderiv_mul, pderiv_pow, pderiv_X,
      Pi.single_apply, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
  all_goals
    apply Polynomial.funext
    intro x
    norm_num

theorem specialize_denominator :
    specialize coefficientDenominator = Polynomial.C (-564000/49:ℂ) := by
  rw [coefficientDenominator, RingHom.map_det, specialize_matrix, Matrix.det_fin_three]
  apply Polynomial.funext
  intro x
  norm_num [Fin.ext_iff, Matrix.cons_val_two]

theorem specialize_equation : specialize chartEquation =
    2*Polynomial.X^6+Polynomial.C (235/7:ℂ)*Polynomial.X^4-
      Polynomial.C (190/7:ℂ)*Polynomial.X^2+Polynomial.C (1458/7:ℂ) := by
  simp [chartEquation, rawWeighted, leftQuadric, rightQuadric, specialize,
    Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_ofNat]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_zero]
  ring

theorem denominator_nonzero : weightedMap coefficientDenominator ≠ 0 := by
  change residueMap (squareLift coefficientDenominator) ≠ 0
  rw [squareLift_denominator, ne_eq, residueMap_kernel]
  intro hdiv
  have hs := map_dvd specialize hdiv
  rw [specialize_denominator] at hs
  have hc : IsUnit (Polynomial.C (-564000/49:ℂ)) :=
    (isUnit_iff_ne_zero.mpr (by norm_num : (-564000/49:ℂ) ≠ 0)).map Polynomial.C
  have hu : IsUnit (specialize chartEquation) := isUnit_of_dvd_unit hs hc
  have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
  have hz : (specialize chartEquation).coeff 6 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; decide)
  rw [specialize_equation] at hz
  norm_num at hz

/-! ## The exact remaining source -/

def coefficientField (i : Fin 3) : FunctionField :=
  weightedMap (coefficientNumerator i)/weightedMap coefficientDenominator

def coefficientFieldDivergence : FunctionField :=
  coefficientDivergence weightedMap basePartial coefficientDenominator coefficientNumerator

theorem coefficientFieldDivergence_eq :
    coefficientFieldDivergence = divergence relativeTangent coefficientField :=
  coefficientDivergence_eq weightedMap normalPartial basePartial relativeTangent
    rawWeighted coefficientDenominator coefficientNumerator canonical_tangents
    normal_numerator normal_denominator

def residualDensity : FunctionField :=
  2*coefficientFieldDivergence/weightedMap (normalPartial rawWeighted)

theorem primitive_iff_residual :
    Nonempty RelativePrimitive ↔ HasPrimitive relativeTangent residualDensity := by
  have hm : (∑ i, coefficientNumerator i*basePartial i rawWeighted) =
      coefficientDenominator*(rawSource+0*rawWeighted) := by
    simpa only [zero_mul, add_zero] using equation_matching
  simpa only [map_zero, sub_zero, residualDensity, coefficientFieldDivergence] using
    relativePrimitive_iff_residual 0 coefficientDenominator coefficientNumerator
      denominator_nonzero normal_numerator normal_denominator hm

def primitiveOfResidual (gamma : Fin 3 → FunctionField)
    (hgamma : divergence relativeTangent gamma = residualDensity) : RelativePrimitive :=
  relativePrimitiveOfResidual 0 coefficientDenominator coefficientNumerator
    denominator_nonzero normal_numerator normal_denominator
    (by simpa only [zero_mul, add_zero] using equation_matching)
    gamma (by simpa only [map_zero, sub_zero, residualDensity,
      coefficientFieldDivergence] using hgamma)

/-- A solution of the concrete reduced equation feeds the existing exact
polynomial certificate construction without any additional hypothesis. -/
theorem certificate_of_residual (gamma : Fin 3 → FunctionField)
    (hgamma : divergence relativeTangent gamma = residualDensity) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A :=
  SymmetricCertificateTransport.certificate_of_relative_primitive
    (primitiveOfResidual gamma hgamma)

#print axioms equation_matching
#print axioms denominator_nonzero
#print axioms primitive_iff_residual
#print axioms primitiveOfResidual
#print axioms certificate_of_residual

end SymmetricCoefficientField
