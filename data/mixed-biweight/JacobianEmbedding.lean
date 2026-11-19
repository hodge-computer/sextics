import Proposal.JacobianGeometry
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields

/-! The generic conic induces an embedding of the Jacobian function field.
The coefficient embedding is anchored; the hypersurface extension uses the
shared monic-root embedding theorem. Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace CycleJacobianEmbedding
open HoldoutConstruction CycleJacobianIncidence CycleJacobianLifting CycleJacobianFamily
  CycleJacobianParameters CycleJacobianGeometry Polynomial
abbrev FunctionField := FractionRing (Polynomial CoefficientField)
abbrev TargetRing := AdjoinRoot CycleJacobianDomain.equation
abbrev TargetField := FractionRing TargetRing
noncomputable instance coefficientField_complexAlgebra : Algebra ℂ CoefficientField := constantMap.toAlgebra
noncomputable instance (priority := 2000) coefficientField_complexModule : Module ℂ CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_complexSMul : SMul ℂ CoefficientField :=
  coefficientField_complexModule.toSMul
instance coefficientField_complexTower : IsScalarTower ℂ ComplexParameterField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := ComplexParameterField) (A := CoefficientField)
    (fun _ => rfl)

lemma conicPolynomial_root :
    CycleJacobianDomain.equation.eval₂ coefficientMap (fullCurve 0)=0 := by
  have he : CycleJacobianDomain.equation.eval₂ coefficientMap (fullCurve 0)=
      conicCurve 2^2-conicCurve 1^3-
      C (constantMap (1/216))*CycleJacobian.a8 (C (scalarParameter 0)) (C (scalarParameter 1))
        1 (conicCurve 0) X*(conicCurve 1)-
      C (constantMap (1/5832))*CycleJacobian.b256 (C (scalarParameter 0)) (C (scalarParameter 1))
        1 (conicCurve 0) X := by
    rw [CycleJacobianDomain.equation,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
      Polynomial.eval₂_X,Polynomial.eval₂_C]
    simp only [CycleJacobianDomain.rhs,CycleJacobian.a8,CycleJacobian.b256,
      map_add,map_mul,map_pow,map_sub,map_neg,map_one,map_ofNat,coefficientMap_C,coefficientMap_X]
    simp only [fullCurve,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
      Matrix.cons_val_one,Matrix.cons_val]
    ring
  have hs := CycleJacobianDomain.integral_scaling (C.comp constantMap)
    (C (scalarParameter 0)) (C (scalarParameter 1)) (conicCurve 0) X (conicCurve 1) (conicCurve 2)
  change 5832*(_)=H (C (scalarParameter 0)) (C (scalarParameter 1)) X conicCurve at hs
  simp only [RingHom.comp_apply] at hs
  rw [← he,conic_equation] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by norm_num)

def fieldCoordinate (i : Fin 6) : FunctionField :=
  algebraMap (Polynomial CoefficientField) FunctionField (fullCurve i)
def fieldCoefficientMap : CycleJacobianDomain.Coeff →+* FunctionField :=
  (algebraMap (Polynomial CoefficientField) FunctionField).comp coefficientMap
lemma fieldCoefficientMap_injective : Function.Injective fieldCoefficientMap :=
  (IsFractionRing.injective (Polynomial CoefficientField) FunctionField).comp coefficientMap_injective
lemma conicField_root :
    CycleJacobianDomain.equation.eval₂ fieldCoefficientMap (fieldCoordinate 0)=0 := by
  have h := congrArg (algebraMap (Polynomial CoefficientField) FunctionField) conicPolynomial_root
  rw [map_zero,Polynomial.hom_eval₂] at h
  exact h

def targetRingMap : TargetRing →+* FunctionField :=
  AdjoinRoot.lift (f := CycleJacobianDomain.equation) fieldCoefficientMap (fieldCoordinate 0) conicField_root
lemma targetRingMap_injective : Function.Injective targetRingMap :=
  monic_root_embedding_injective CycleJacobianDomain.equation
    CycleJacobianDomain.equation_monic CycleJacobianDomain.equation_irreducible
    fieldCoefficientMap fieldCoefficientMap_injective (fieldCoordinate 0) conicField_root
def targetFieldMap : TargetField →+* FunctionField := IsFractionRing.lift targetRingMap_injective
lemma targetFieldMap_injective : Function.Injective targetFieldMap := targetFieldMap.injective
lemma targetFieldMap_ring (r : TargetRing) :
    targetFieldMap (algebraMap TargetRing TargetField r)=targetRingMap r :=
  IsFractionRing.lift_algebraMap targetRingMap_injective r
lemma targetFieldMap_complex (z : ℂ) :
    targetFieldMap (algebraMap ℂ TargetField z)=algebraMap ℂ FunctionField z := by
  change targetFieldMap (algebraMap TargetRing TargetField
    (AdjoinRoot.of CycleJacobianDomain.equation (MvPolynomial.C z)))=_
  rw [targetFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of CycleJacobianDomain.equation (MvPolynomial.C z))=_
  rw [AdjoinRoot.lift_of]
  simp only [fieldCoefficientMap,RingHom.comp_apply,coefficientMap_C]
  rfl
noncomputable instance functionField_targetAlgebra : Algebra TargetField FunctionField := targetFieldMap.toAlgebra
instance functionField_targetTower : IsScalarTower ℂ TargetField FunctionField :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := TargetField) (A := FunctionField)
    (fun z => (targetFieldMap_complex z).symm)
#print axioms targetFieldMap_injective
end CycleJacobianEmbedding
