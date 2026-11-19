import Proposal.ConicEmbedding

/-!
The dominant conic map embeds the function field of the exact deformed
weighted quotient. Injectivity is established before assigning the target
algebra structure. Uses fqlx's shared monic-root embedding theorem.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open HoldoutConstruction Polynomial

abbrev targetPolynomial := DeformedGeometry.quotientPolynomial (14⁻¹ : BaseField) baseFieldAlpha baseFieldBeta
abbrev TargetRing := AdjoinRoot targetPolynomial
abbrev TargetField := FractionRing TargetRing
instance targetRing_domain : IsDomain TargetRing := DeformedGeometry.quotient_domain _ _ _
noncomputable instance targetField_field : Field TargetField := inferInstance
instance targetRing_charZero : CharZero TargetRing :=
  charZero_of_injective_ringHom (f := algebraMap BaseField TargetRing) (algebraMap BaseField TargetRing).injective
instance targetField_charZero : CharZero TargetField := inferInstance

lemma conicPolynomial_root : targetPolynomial.eval₂ targetCoefficientMap (conicCurve 0)=0 := by
  have he : targetPolynomial.eval₂ targetCoefficientMap (conicCurve 0)=
      MvPolynomial.eval₂Hom (C.comp (algebraMap BaseField CoefficientField)) conicCurve
        (DeformedGeometry.weightedEquation (14⁻¹) baseFieldAlpha baseFieldBeta) := by
    simp [targetPolynomial,DeformedGeometry.quotientPolynomial,DeformedGeometry.weightedEquation,
      Polynomial.eval₂_add,Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
      targetCoefficientMap_C,targetCoefficientMap_X,conicAlpha_base,conicBeta_base,map_ofNat]
    ring
  rw [he]
  have h := DeformedGeometry.weightedEquation_eval_fourteen
    (C.comp (algebraMap BaseField CoefficientField)) baseFieldAlpha baseFieldBeta conicCurve
  simp only [RingHom.comp_apply,conicAlpha_base,conicBeta_base,conic_equation] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

def fieldCoordinate (i : Fin 5) : FunctionField :=
  algebraMap (Polynomial CoefficientField) FunctionField (conicCurve i)
def fieldCoefficientMap : MvPolynomial (Fin 4) BaseField →+* FunctionField :=
  (algebraMap (Polynomial CoefficientField) FunctionField).comp targetCoefficientMap
lemma fieldCoefficientMap_injective : Function.Injective fieldCoefficientMap :=
  (IsFractionRing.injective (Polynomial CoefficientField) FunctionField).comp targetCoefficientMap_injective
@[simp] lemma fieldCoefficientMap_C (r : BaseField) :
    fieldCoefficientMap (MvPolynomial.C r)=algebraMap BaseField FunctionField r := by
  rw [fieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_C]
  rfl
@[simp] lemma fieldCoefficientMap_X (i : Fin 4) :
    fieldCoefficientMap (MvPolynomial.X i)=fieldCoordinate i.succ := by
  rw [fieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_X]
  rfl
lemma conicField_root : targetPolynomial.eval₂ fieldCoefficientMap (fieldCoordinate 0)=0 := by
  have h := congrArg (algebraMap (Polynomial CoefficientField) FunctionField) conicPolynomial_root
  rw [map_zero,Polynomial.hom_eval₂] at h
  exact h
def targetRingMap : TargetRing →+* FunctionField :=
  AdjoinRoot.lift (f := targetPolynomial) fieldCoefficientMap (fieldCoordinate 0) conicField_root
lemma targetRingMap_injective : Function.Injective targetRingMap :=
  monic_root_embedding_injective targetPolynomial
    (DeformedGeometry.quotientPolynomial_monic _ _ _)
    (DeformedGeometry.quotientPolynomial_irreducible _ _ _)
    fieldCoefficientMap fieldCoefficientMap_injective (fieldCoordinate 0) conicField_root
def targetFieldMap : TargetField →+* FunctionField := IsFractionRing.lift targetRingMap_injective
@[simp] lemma targetFieldMap_ring (r : TargetRing) :
    targetFieldMap (algebraMap TargetRing TargetField r)=targetRingMap r :=
  IsFractionRing.lift_algebraMap targetRingMap_injective r
@[simp] lemma targetFieldMap_base (r : BaseField) :
    targetFieldMap (algebraMap BaseField TargetField r)=algebraMap BaseField FunctionField r := by
  change targetFieldMap (algebraMap TargetRing TargetField
    (AdjoinRoot.of targetPolynomial (MvPolynomial.C r)))=_
  rw [targetFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of targetPolynomial (MvPolynomial.C r))=_
  rw [AdjoinRoot.lift_of,fieldCoefficientMap_C]
noncomputable instance functionField_targetAlgebra : Algebra TargetField FunctionField := targetFieldMap.toAlgebra
instance functionField_targetTower : IsScalarTower BaseField TargetField FunctionField :=
  IsScalarTower.of_algebraMap_eq (R := BaseField) (S := TargetField) (A := FunctionField)
    (fun r => (targetFieldMap_base r).symm)

end DeformedConic
#print axioms DeformedConic.targetRingMap_injective
#print axioms DeformedConic.targetFieldMap_base
