import Proposal.JacobianLifting
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal

/-!
A generic polynomial conic and a polynomial normal on the mixed-polar
Jacobian. Arithmetic lifting is provided by the shared library. The
full-coefficient linear algebra is the method used in the accepted
ternary-deformation construction, with all target-specific data bound here.
Adapted from the accepted constructions of fqlx and hodgepodgeconjecture.
Prepared for benediamond with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace MixedPolarJacobianFamily
open HoldoutConstruction MixedPolarJacobianIncidence MixedPolarJacobianLifting Polynomial
open scoped BigOperators

abbrev GenericIncidence := SquareGenericAlgebra ComplexParameterField genericEquations
noncomputable instance (priority := 2000) genericIncidence_module : Module ComplexParameterField GenericIncidence :=
  Algebra.toModule
noncomputable instance (priority := 2000) genericIncidence_smul : SMul ComplexParameterField GenericIncidence :=
  genericIncidence_module.toSMul
def coefficientFactor : Ideal GenericIncidence :=
  Classical.choose complex_generic_factor_exists
instance coefficientFactor_maximal : coefficientFactor.IsMaximal :=
  (Classical.choose_spec complex_generic_factor_exists).1
abbrev CoefficientField := GenericIncidence ⧸ coefficientFactor
noncomputable instance coefficientField_field : Field CoefficientField :=
  Ideal.Quotient.field _
noncomputable instance (priority := 2000) coefficientField_module : Module ComplexParameterField CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_smul : SMul ComplexParameterField CoefficientField :=
  coefficientField_module.toSMul
instance coefficientField_finite : Module.Finite ComplexParameterField CoefficientField :=
  (Classical.choose_spec complex_generic_factor_exists).2
instance coefficientField_charZero : CharZero CoefficientField :=
  charZero_of_injective_ringHom (f := algebraMap ComplexParameterField CoefficientField)
    (algebraMap ComplexParameterField CoefficientField).injective
noncomputable instance coefficientField_parameterAlgebra : Algebra ParameterRing CoefficientField :=
  ((algebraMap ComplexParameterField CoefficientField).comp
    (algebraMap ParameterRing ComplexParameterField)).toAlgebra
noncomputable instance (priority := 2000) coefficientField_parameterModule : Module ParameterRing CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_parameterSMul : SMul ParameterRing CoefficientField :=
  coefficientField_parameterModule.toSMul
instance coefficientField_parameterTower : IsScalarTower ParameterRing ComplexParameterField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (R := ParameterRing) (S := ComplexParameterField)
    (A := CoefficientField) (fun _ => rfl)

def coefficients : Fin 13 → CoefficientField :=
  squareGenericCoordinates genericEquations coefficientFactor
def scalarParameter (i : Fin 4) : CoefficientField :=
  algebraMap ParameterRing CoefficientField (parameter i)
def conicCurve : Fin 3 → Polynomial CoefficientField :=
  curveEval endpoints (algebraMap ParameterRing CoefficientField) coefficients
def conicGradient : Fin 3 → Polynomial CoefficientField :=
  gradient (C (scalarParameter 0)) (C (scalarParameter 1)) X conicCurve

theorem conic_equation :
    H (C (scalarParameter 0)) (C (scalarParameter 1)) X conicCurve=0 := by
  have he : (H (cp (parameter 0)) (cp (parameter 1)) X (curve endpoints)).map
      (MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients) =
      H (C (scalarParameter 0)) (C (scalarParameter 1)) X conicCurve := by
    change (Polynomial.mapRingHom
      (MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients))
      (H (cp (parameter 0)) (cp (parameter 1)) X (curve endpoints)) = _
    convert
      (MixedPolarJacobianIncidence.H_map
        (Polynomial.mapRingHom
          (MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients))
        (cp (parameter 0)) (cp (parameter 1)) X (curve endpoints)) using 1
    simp only [Polynomial.coe_mapRingHom,cp,Polynomial.map_C,Polynomial.map_X,
      MvPolynomial.eval₂Hom_C,scalarParameter,conicCurve]
    rfl
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n<13
  · have h := squareGeneric_solution genericEquations coefficientFactor (⟨n,hn⟩ : Fin 13)
    change MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients
      (equations (parameter 0) (parameter 1) endpoints ⟨n,hn⟩)=0 at h
    rw [equations_eval] at h
    exact h
  · have hb : (H (C (scalarParameter 0)) (C (scalarParameter 1)) X conicCurve).natDegree ≤ 12 := by
      rw [← he]
      exact Polynomial.natDegree_map_le.trans (H_natDegree_le _ _ _)
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega))

def conicJacobian : Matrix (Fin 13) (Fin 13) CoefficientField :=
  fun i j => (conicGradient (slotCoordinate j)*X^slotDegree j).coeff i.val
lemma conic_jacobian_unit : IsUnit conicJacobian.det := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval coefficients
      (MvPolynomial.pderiv i (genericEquations j)))=conicJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (algebraMap ParameterRing CoefficientField) coefficients
      (MvPolynomial.pderiv i (equations (parameter 0) (parameter 1) endpoints j)) = _
    rw [equations_pderiv_eval]
    rfl
  have h := squareGeneric_jacobian genericEquations coefficientFactor
  change IsUnit (Matrix.det (fun i j => MvPolynomial.aeval coefficients
    (MvPolynomial.pderiv i (genericEquations j)))) at h
  rw [hm,Matrix.det_transpose] at h
  exact h

/-- Full-coefficient version of the shared polynomial-normal linear algebra. -/
theorem full_polynomial_combination_one {R : Type*} [CommRing R] {n : ℕ} (hn : 0<n)
    (Q : Fin n → Polynomial R) (bound : ∀ j, (Q j).natDegree < n)
    (hunit : IsUnit (Matrix.det (fun i j : Fin n => (Q j).coeff i.val))) :
    ∃ u : Fin n → R, ∑ j, C (u j)*Q j=1 := by
  let J : Matrix (Fin n) (Fin n) R := fun i j => (Q j).coeff i.val
  let e : Fin n → R := Pi.single ⟨0,hn⟩ 1
  let u := J⁻¹.mulVec e
  have hu : J.mulVec u=e := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv J hunit,Matrix.one_mulVec]
  refine ⟨u,?_⟩
  apply Polynomial.ext
  intro k
  by_cases hk : k<n
  · have h := congrFun hu ⟨k,hk⟩
    simp only [Matrix.mulVec,dotProduct,J,e,Pi.single_apply] at h
    rw [show (∑ j, (Q j).coeff k*u j) = ∑ j, u j*(Q j).coeff k by
      apply Finset.sum_congr rfl
      intro j _
      ring] at h
    simpa [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_one,
      Fin.ext_iff] using h
  · have hQ (j : Fin n) : (Q j).coeff k=0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (bound j) (Nat.le_of_not_gt hk))
    have hk0 : k ≠ 0 := by omega
    simp [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,hQ,Polynomial.coeff_one,hk0]

lemma conicGradient_column_bound (j : Fin 13) :
    (conicGradient (slotCoordinate j)*X^slotDegree j).natDegree < 13 := by
  unfold conicGradient conicCurve
  rw [curveEval_eq_valueCurve]
  fin_cases j <;> dsimp [slotCoordinate,slotDegree,gradient,a8r,b256r,
    MixedPolarJacobian.a8,MixedPolarJacobian.a432,valueCurve]
  all_goals compute_degree <;> norm_num

theorem conicNormal_exists : ∃ N : Fin 3 → Polynomial CoefficientField,
    polynomialPairing conicGradient N=1 ∧ ∀ i, i ≠ 2 → (N i).coeff 0=0 := by
  obtain ⟨u,hu⟩ := full_polynomial_combination_one (by decide : 0<13)
    (fun j => conicGradient (slotCoordinate j)*X^slotDegree j)
    conicGradient_column_bound conic_jacobian_unit
  let v : Fin 13 → Fin 3 → Polynomial CoefficientField :=
    fun j => Pi.single (slotCoordinate j) (X^slotDegree j)
  have hp (j : Fin 13) : polynomialPairing conicGradient (v j)=
      conicGradient (slotCoordinate j)*X^slotDegree j := by
    simp [v,polynomialPairing,Pi.single_apply]
  refine ⟨fun i => 0+∑ j, C (u j)*v j i,?_,?_⟩
  · rw [polynomialPairing_affine]
    have hz : polynomialPairing conicGradient (fun _ : Fin 3 => 0)=0 := by
      simp [polynomialPairing]
    rw [hz,zero_add]
    simpa only [hp] using hu
  · intro i hi
    have hz (j : Fin 13) : (C (u j)*v j i).coeff 0=0 := by
      fin_cases j <;> fin_cases i <;> simp_all [v,slotCoordinate,slotDegree,Pi.single_apply,
        Polynomial.coeff_C_mul,Polynomial.coeff_X_pow]
    simp [Polynomial.finsetSum_coeff,hz]

def conicNormal : Fin 3 → Polynomial CoefficientField := Classical.choose conicNormal_exists
lemma conicNormal_pairing : polynomialPairing conicGradient conicNormal=1 :=
  (Classical.choose_spec conicNormal_exists).1
lemma conicNormal_constant_zero (i : Fin 3) (hi : i ≠ 2) :
    (conicNormal i).coeff 0=0 := (Classical.choose_spec conicNormal_exists).2 i hi
lemma conicNormal_constant_nonzero : (conicNormal 2).coeff 0 ≠ 0 := by
  have hp := congrArg (Polynomial.constantCoeff : Polynomial CoefficientField →+* CoefficientField)
    conicNormal_pairing
  unfold polynomialPairing at hp
  rw [map_sum,map_one] at hp
  simp only [map_mul,Polynomial.constantCoeff_apply,Fin.sum_univ_three,
    conicNormal_constant_zero 0 (by decide),conicNormal_constant_zero 1 (by decide),
    mul_zero,zero_add] at hp
  intro h
  rw [h,mul_zero] at hp
  exact zero_ne_one hp

#print axioms conic_equation
#print axioms conicNormal_pairing
#print axioms conicNormal_constant_nonzero
end MixedPolarJacobianFamily
