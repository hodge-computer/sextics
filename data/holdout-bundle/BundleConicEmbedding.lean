import Proposal.BundleCoefficientBase
import Proposal.BundleQuotientModel
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap

/-! Dominance and finiteness of the actual anchored conic evaluation map.
The independent endpoint parameters and the exact coordinate X1=t prove
injectivity before the target-field algebra structure is introduced. -/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

def endpointCoefficientEmbedding : MvPolynomial (Fin 3) BaseField →+* CoefficientField :=
  (algebraMap EndpointField CoefficientField).comp
    ((algebraMap GenericEndpoint EndpointField).comp
      (AdjoinRoot.of (endpointPolynomial genericA genericB)))

theorem endpointCoefficientEmbedding_injective :
    Function.Injective endpointCoefficientEmbedding := by
  intro a b h
  apply endpoint_of_injective genericA genericB
  apply IsFractionRing.injective GenericEndpoint EndpointField
  apply (algebraMap EndpointField CoefficientField).injective
  exact h

def curveRemainingCoefficientMap :
    MvPolynomial (Fin 3) BaseField →+* Polynomial CoefficientField :=
  MvPolynomial.eval₂Hom (C.comp (algebraMap BaseField CoefficientField))
    ![baseFamily.curve 2,baseFamily.curve 3,baseFamily.curve 4]

theorem curveRemainingCoefficientMap_constant :
    Polynomial.constantCoeff.comp curveRemainingCoefficientMap=endpointCoefficientEmbedding := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,curveRemainingCoefficientMap,MvPolynomial.eval₂Hom_C,
      Polynomial.constantCoeff_apply,Polynomial.coeff_C_zero,endpointCoefficientEmbedding]
    rfl
  · intro j
    simp only [RingHom.comp_apply,curveRemainingCoefficientMap,MvPolynomial.eval₂Hom_X',
      Polynomial.constantCoeff_apply,endpointCoefficientEmbedding]
    change (![baseFamily.curve 2,baseFamily.curve 3,baseFamily.curve 4] j).coeff 0=
      algebraMap EndpointField CoefficientField
        (algebraMap GenericEndpoint EndpointField (endpointParameter genericA genericB j))
    have hj : ![baseFamily.curve 2,baseFamily.curve 3,baseFamily.curve 4] j=
        baseFamily.curve j.succ.succ := by fin_cases j <;> simp
    rw [hj,baseFamily.curve_endpoint,conicEndpoint_parameter]

def curveTargetCoefficientMap :
    MvPolynomial (Fin 4) BaseField →+* Polynomial CoefficientField :=
  (Polynomial.eval₂RingHom curveRemainingCoefficientMap (C 1*X)).comp
    (MvPolynomial.finSuccEquiv BaseField 3).toRingHom

theorem curveTargetCoefficientMap_injective :
    Function.Injective curveTargetCoefficientMap := by
  have hconst : Function.Injective
      (Polynomial.constantCoeff.comp curveRemainingCoefficientMap) := by
    rw [curveRemainingCoefficientMap_constant]
    exact endpointCoefficientEmbedding_injective
  exact (polynomial_family_injective curveRemainingCoefficientMap hconst
    1 one_ne_zero).comp (MvPolynomial.finSuccEquiv BaseField 3).injective

@[simp] theorem curveTargetCoefficientMap_C (r : BaseField) :
    curveTargetCoefficientMap (MvPolynomial.C r)=C (algebraMap BaseField CoefficientField r) := by
  simp [curveTargetCoefficientMap,MvPolynomial.finSuccEquiv_apply,curveRemainingCoefficientMap]

theorem curveTargetCoefficientMap_X (j : Fin 4) :
    curveTargetCoefficientMap (MvPolynomial.X j)=baseFamily.curve j.succ := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [curveTargetCoefficientMap,MvPolynomial.finSuccEquiv_X_zero]
  · change (Polynomial.eval₂RingHom curveRemainingCoefficientMap (C 1*X))
      (MvPolynomial.finSuccEquiv BaseField 3 (MvPolynomial.X i.succ))=_
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ curveRemainingCoefficientMap (C 1*X) (C (MvPolynomial.X i))=_
    rw [Polynomial.eval₂_C]
    simp only [curveRemainingCoefficientMap,MvPolynomial.eval₂Hom_X']
    fin_cases i <;> simp

def conicFieldCoordinate (j : Fin 5) : ConicFunctionField :=
  algebraMap (Polynomial CoefficientField) ConicFunctionField (baseFamily.curve j)

def conicFieldEval : MvPolynomial (Fin 5) BaseField →+* ConicFunctionField :=
  MvPolynomial.eval₂Hom (algebraMap BaseField ConicFunctionField) conicFieldCoordinate

def conicFieldCoefficientMap : MvPolynomial (Fin 4) BaseField →+* ConicFunctionField :=
  (algebraMap (Polynomial CoefficientField) ConicFunctionField).comp curveTargetCoefficientMap

theorem conicFieldCoefficientMap_injective : Function.Injective conicFieldCoefficientMap :=
  (IsFractionRing.injective (Polynomial CoefficientField) ConicFunctionField).comp
    curveTargetCoefficientMap_injective

@[simp] theorem conicFieldCoefficientMap_C (r : BaseField) :
    conicFieldCoefficientMap (MvPolynomial.C r)=algebraMap BaseField ConicFunctionField r := by
  rw [conicFieldCoefficientMap,RingHom.comp_apply,curveTargetCoefficientMap_C]
  rfl

@[simp] theorem conicFieldCoefficientMap_X (j : Fin 4) :
    conicFieldCoefficientMap (MvPolynomial.X j)=conicFieldCoordinate j.succ := by
  rw [conicFieldCoefficientMap,RingHom.comp_apply,curveTargetCoefficientMap_X]
  rfl

theorem conicPolynomial_root :
    (quotientPolynomial genericA genericB).eval₂ curveTargetCoefficientMap
      (baseFamily.curve 0)=0 := by
  have h := baseFamily.curve_equation
  simp only [quotientPolynomial,Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,map_add,map_mul,map_pow,
    curveTargetCoefficientMap_C,curveTargetCoefficientMap_X,
    show (0 : Fin 4).succ=(1 : Fin 5) by decide,
    show (1 : Fin 4).succ=(2 : Fin 5) by decide,
    show (2 : Fin 4).succ=(3 : Fin 5) by decide,
    show (3 : Fin 4).succ=(4 : Fin 5) by decide]
  unfold K at h
  linear_combination h

theorem conicField_root :
    (quotientPolynomial genericA genericB).eval₂ conicFieldCoefficientMap
      (conicFieldCoordinate 0)=0 := by
  have h := congrArg (algebraMap (Polynomial CoefficientField) ConicFunctionField)
    conicPolynomial_root
  rw [map_zero,Polynomial.hom_eval₂] at h
  exact h

def conicTargetRingMap : QuotientRing →+* ConicFunctionField :=
  AdjoinRoot.lift (f := quotientPolynomial genericA genericB)
    conicFieldCoefficientMap (conicFieldCoordinate 0) conicField_root

theorem conicTargetRingMap_injective : Function.Injective conicTargetRingMap :=
  monic_root_embedding_injective (quotientPolynomial genericA genericB)
    (quotientPolynomial_monic genericA genericB)
    (quotientPolynomial_irreducible genericA genericB genericB_ne_zero)
    conicFieldCoefficientMap conicFieldCoefficientMap_injective
    (conicFieldCoordinate 0) conicField_root

def conicTargetFieldMap : QuotientField →+* ConicFunctionField :=
  IsFractionRing.lift conicTargetRingMap_injective

@[simp] theorem conicTargetFieldMap_ring (r : QuotientRing) :
    conicTargetFieldMap (algebraMap QuotientRing QuotientField r)=conicTargetRingMap r :=
  IsFractionRing.lift_algebraMap conicTargetRingMap_injective r

@[simp] theorem conicTargetFieldMap_base (r : BaseField) :
    conicTargetFieldMap (algebraMap BaseField QuotientField r)=
      algebraMap BaseField ConicFunctionField r := by
  change conicTargetFieldMap (algebraMap QuotientRing QuotientField
    (AdjoinRoot.of (quotientPolynomial genericA genericB) (MvPolynomial.C r)))=_
  rw [conicTargetFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (MvPolynomial.C r))=_
  rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_C]

instance conicFunctionField_targetAlgebra : Algebra QuotientField ConicFunctionField :=
  conicTargetFieldMap.toAlgebra

instance conicFunctionField_baseTower : IsScalarTower BaseField QuotientField ConicFunctionField :=
  IsScalarTower.of_algebraMap_eq (R := BaseField) (S := QuotientField)
    (A := ConicFunctionField) (fun r => (conicTargetFieldMap_base r).symm)

theorem conicTargetFieldMap_coordinate (j : Fin 5) :
    conicTargetFieldMap (quotientResidueMap (MvPolynomial.X j))=conicFieldCoordinate j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [quotientResidueMap_X_zero,conicTargetFieldMap_ring]
    exact AdjoinRoot.lift_root conicField_root
  · rw [quotientResidueMap_X_succ,conicTargetFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (MvPolynomial.X i))=_
    rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_X]

theorem conicTargetFieldMap_residue (f : MvPolynomial (Fin 5) BaseField) :
    conicTargetFieldMap (quotientResidueMap f)=conicFieldEval f := by
  have h : conicTargetFieldMap.comp quotientResidueMap=conicFieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [conicFieldEval]
    · intro j
      simp only [RingHom.comp_apply,conicTargetFieldMap_coordinate,
        conicFieldEval,MvPolynomial.eval₂Hom_X']
  exact congrArg (fun f : MvPolynomial (Fin 5) BaseField →+* ConicFunctionField => f _) h

instance conicFunctionField_finite : Module.Finite QuotientField ConicFunctionField := by
  apply finite_of_same_finite_trdeg (K := BaseField)
  · rw [quotientField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [quotientField_trdeg,conicFunctionField_trdeg]

end HoldoutBundle

#print axioms HoldoutBundle.conicTargetRingMap_injective
#print axioms HoldoutBundle.conicFunctionField_finite
