import Proposal.JacobianParameters
import Proposal.JacobianDomain
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix

/-! Independence of the five coefficient coordinates and nonsingularity
of the normal/tangent evaluation matrix for the generic conic family.
The anchored-family and Laplace-expansion arguments reuse the credited shared
construction. Adapted from the accepted cyclic and transitive constructions of hodgepodgeconjecture and fqlx; this mixed-polar specialization was prepared for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
namespace CycleJacobianGeometry
open HoldoutConstruction CycleJacobianIncidence CycleJacobianLifting
  CycleJacobianFamily CycleJacobianParameters Polynomial

/-- Endpoint order c1,c2,R,X agrees with the four independent parameters. -/
def remainingCurveMap : ComplexParameterRing →+* Polynomial CoefficientField :=
  MvPolynomial.eval₂Hom (C.comp constantMap)
    ![C (scalarParameter 0),C (scalarParameter 1),conicCurve 0,conicCurve 1]
lemma remainingCurveMap_constant : constantCoeff.comp remainingCurveMap=parameterMap := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [remainingCurveMap,constantMap]
  · intro i
    simp only [RingHom.comp_apply,remainingCurveMap,MvPolynomial.eval₂Hom_X',
      Polynomial.constantCoeff_apply,parameterMap_X]
    fin_cases i <;> simp [conicCurve_endpoint_r,conicCurve_endpoint_x]

def coefficientMap : CycleJacobianDomain.Coeff →+* Polynomial CoefficientField :=
  (Polynomial.eval₂RingHom remainingCurveMap X).comp (MvPolynomial.finSuccEquiv ℂ 4).toRingHom
lemma coefficientMap_injective : Function.Injective coefficientMap := by
  have hconst : Function.Injective (constantCoeff.comp remainingCurveMap) := by
    rw [remainingCurveMap_constant]
    exact parameterMap_injective
  have h := polynomial_family_injective remainingCurveMap hconst 1 one_ne_zero
  simp only [Polynomial.C_1,one_mul] at h
  exact h.comp (MvPolynomial.finSuccEquiv ℂ 4).injective
@[simp] lemma coefficientMap_C (z : ℂ) : coefficientMap (MvPolynomial.C z)=C (constantMap z) := by
  simp [coefficientMap,MvPolynomial.finSuccEquiv_apply,remainingCurveMap]
@[simp] lemma coefficientMap_X (i : Fin 5) : coefficientMap (MvPolynomial.X i)=fullCurve i.succ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coefficientMap,MvPolynomial.finSuccEquiv_X_zero,fullCurve]
  · change (Polynomial.eval₂RingHom remainingCurveMap X)
      (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X j.succ))=_
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ remainingCurveMap X (C (MvPolynomial.X j))=_
    rw [Polynomial.eval₂_C]
    simp only [remainingCurveMap,MvPolynomial.eval₂Hom_X']
    fin_cases j <;> rfl

/-- Generic-size counterpart of the shared five-coordinate determinant lemma. -/

def evaluationPolynomialMatrix : Matrix (Fin 6) (Fin 6) (Polynomial CoefficientField) :=
  fun i => Fin.cases (fullNormal i) (fun j => polynomialDerivation j (fullCurve i))
lemma evaluation_det_constant : evaluationPolynomialMatrix.det.coeff 0=(conicNormal 2).coeff 0 := by
  calc
    _ = Matrix.det (fun i j => (evaluationPolynomialMatrix i j).coeff 0) :=
      (constantCoeff : Polynomial CoefficientField →+* CoefficientField).map_det _
    _ = _ := by
      apply endpoint_det
      · intro i
        exact fullNormal_constant i
      · change (timePolynomialDerivation (fullCurve 1)).coeff 0=1
        rw [fullCurve_time,timePolynomialDerivation_apply]
        simp
      · intro j
        change (coefficientPolynomialDerivation (coefficientDerivation j) (fullCurve 1)).coeff 0=0
        rw [fullCurve_time,coefficientPolynomialDerivation_coeff]
        simp
      · intro i j
        change (coefficientPolynomialDerivation (coefficientDerivation j)
          (fullCurve i.succ.succ)).coeff 0=if i=j then 1 else 0
        rw [coefficientPolynomialDerivation_coeff,fullCurve_endpoint,coefficientDerivation_parameter]
lemma evaluation_det_ne_zero : evaluationPolynomialMatrix.det ≠ 0 := by
  intro h
  have hc := evaluation_det_constant
  rw [h,Polynomial.coeff_zero] at hc
  exact conicNormal_constant_nonzero hc.symm

#print axioms coefficientMap_injective
#print axioms evaluation_det_ne_zero
end CycleJacobianGeometry
