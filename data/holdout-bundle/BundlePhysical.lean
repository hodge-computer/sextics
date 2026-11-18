import Proposal.BundlePhysicalDominance
import Proposal.BundleQuotientModel

/-! The injective map from the generic relative quotient field into the
physical sextic field. Its construction first proves injectivity on the
polynomial parameter algebra, then localizes, then adjoins the monic root. -/

noncomputable section

namespace HoldoutBundle
open HoldoutConstruction

attribute [local instance] holdoutCoordinateRing_isDomain
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem localization_map_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (f : S →+* T) (h : Function.Injective (f.comp (algebraMap R S))) :
    Function.Injective f := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq M f).mpr
  intro x y
  constructor
  · exact congrArg f
  · intro he
    exact congrArg (algebraMap R S) (h he)

def parameterPhysicalMap : ParameterRing →+* HoldoutFunctionField :=
  (Polynomial.aeval physicalLambda).toRingHom

theorem parameterPhysicalMap_injective : Function.Injective parameterPhysicalMap :=
  transcendental_iff_injective.mp
    (physicalParameters_independent.transcendental (0 : Fin 5))

def basePhysicalFieldMap : BaseField →+* HoldoutFunctionField :=
  IsFractionRing.lift parameterPhysicalMap_injective

@[simp] theorem basePhysicalFieldMap_ring (p : ParameterRing) :
    basePhysicalFieldMap (algebraMap ParameterRing BaseField p)=parameterPhysicalMap p :=
  IsFractionRing.lift_algebraMap parameterPhysicalMap_injective p

@[simp] theorem basePhysicalFieldMap_complex (c : ℂ) :
    basePhysicalFieldMap (algebraMap ℂ BaseField c)=algebraMap ℂ HoldoutFunctionField c := by
  change basePhysicalFieldMap (algebraMap ParameterRing BaseField (Polynomial.C c))=_
  simp [parameterPhysicalMap]

@[simp] theorem basePhysicalFieldMap_lambda : basePhysicalFieldMap lambda=physicalLambda := by
  simp [lambda,parameterPhysicalMap]

theorem basePhysicalFieldMap_A : basePhysicalFieldMap genericA=coeffA physicalLambda := by
  rw [genericA_value,map_add,map_inv₀,basePhysicalFieldMap_lambda]
  rfl

theorem basePhysicalFieldMap_B : basePhysicalFieldMap genericB=coeffB physicalI physicalLambda := by
  rw [genericB_value,map_mul,map_sub,map_inv₀,basePhysicalFieldMap_lambda,
    basePhysicalFieldMap_complex]
  rfl

def physicalIndependentCoordinates : Fin 4 → HoldoutFunctionField :=
  ![physicalY 1,physicalY 2,physicalP,physicalQ]

def physicalIntegralCoefficientMap : MvPolynomial (Fin 4) ParameterRing →+* HoldoutFunctionField :=
  MvPolynomial.eval₂Hom parameterPhysicalMap physicalIndependentCoordinates

def physicalParameterEquiv : MvPolynomial (Fin 5) ℂ ≃ₐ[ℂ]
    MvPolynomial (Fin 4) ParameterRing :=
  (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 4)).trans
    (MvPolynomial.optionEquivRight ℂ (Fin 4))

theorem physicalIntegralCoefficientMap_parameterEquiv :
    physicalIntegralCoefficientMap.comp physicalParameterEquiv.toRingHom=
      (MvPolynomial.aeval physicalParameters).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [physicalIntegralCoefficientMap,physicalParameterEquiv,parameterPhysicalMap,
      MvPolynomial.optionEquivRight_C]
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [physicalIntegralCoefficientMap,physicalParameterEquiv,parameterPhysicalMap,
        physicalIndependentCoordinates,physicalParameters]
    ·
      simp [physicalIntegralCoefficientMap,physicalParameterEquiv,parameterPhysicalMap,
        physicalIndependentCoordinates,physicalParameters]

theorem physicalIntegralCoefficientMap_injective : Function.Injective physicalIntegralCoefficientMap := by
  intro p q hpq
  obtain ⟨a,rfl⟩ := physicalParameterEquiv.surjective p
  obtain ⟨b,rfl⟩ := physicalParameterEquiv.surjective q
  apply congrArg physicalParameterEquiv
  apply physical_parameter_evaluation_injective
  change (physicalIntegralCoefficientMap.comp physicalParameterEquiv.toRingHom) a=
    (physicalIntegralCoefficientMap.comp physicalParameterEquiv.toRingHom) b at hpq
  rwa [physicalIntegralCoefficientMap_parameterEquiv] at hpq

def physicalCoefficientMap : MvPolynomial (Fin 4) BaseField →+* HoldoutFunctionField :=
  MvPolynomial.eval₂Hom basePhysicalFieldMap physicalIndependentCoordinates

@[simp] theorem physicalCoefficientMap_C (r : BaseField) :
    physicalCoefficientMap (MvPolynomial.C r)=basePhysicalFieldMap r := by
  simp [physicalCoefficientMap]

@[simp] theorem physicalCoefficientMap_X (j : Fin 4) :
    physicalCoefficientMap (MvPolynomial.X j)=physicalIndependentCoordinates j := by
  simp [physicalCoefficientMap]

theorem physicalCoefficientMap_baseChange :
    physicalCoefficientMap.comp
      (algebraMap (MvPolynomial (Fin 4) ParameterRing) (MvPolynomial (Fin 4) BaseField))=
      physicalIntegralCoefficientMap := by
  rw [MvPolynomial.algebraMap_def]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,MvPolynomial.map_C,physicalCoefficientMap_C,
      basePhysicalFieldMap_ring,physicalIntegralCoefficientMap,MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply,MvPolynomial.map_X,physicalCoefficientMap_X,
      physicalIntegralCoefficientMap,MvPolynomial.eval₂Hom_X']

theorem physicalCoefficientMap_injective : Function.Injective physicalCoefficientMap := by
  apply localization_map_injective
    ((nonZeroDivisors ParameterRing).map (MvPolynomial.C (σ := Fin 4))) physicalCoefficientMap
  rw [physicalCoefficientMap_baseChange]
  exact physicalIntegralCoefficientMap_injective

theorem physical_quotient_root :
    (quotientPolynomial genericA genericB).eval₂ physicalCoefficientMap (physicalY 0)=0 := by
  have h := physical_quotient_equation
  simp only [quotientPolynomial,Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,map_add,map_mul,map_pow,
    physicalCoefficientMap_C,physicalCoefficientMap_X,basePhysicalFieldMap_A,
    basePhysicalFieldMap_B,physicalIndependentCoordinates,Matrix.cons_val]
  simp only [K,Matrix.cons_val] at h
  linear_combination h

def quotientPhysicalRingMap : QuotientRing →+* HoldoutFunctionField :=
  AdjoinRoot.lift (f := quotientPolynomial genericA genericB)
    physicalCoefficientMap (physicalY 0) physical_quotient_root

theorem quotientPhysicalRingMap_injective : Function.Injective quotientPhysicalRingMap :=
  monic_root_embedding_injective _ (quotientPolynomial_monic _ _)
    (quotientPolynomial_irreducible _ _ genericB_ne_zero)
    physicalCoefficientMap physicalCoefficientMap_injective (physicalY 0) physical_quotient_root

def quotientPhysicalFieldMap : QuotientField →+* HoldoutFunctionField :=
  IsFractionRing.lift quotientPhysicalRingMap_injective

@[simp] theorem quotientPhysicalFieldMap_ring (p : QuotientRing) :
    quotientPhysicalFieldMap (algebraMap QuotientRing QuotientField p)=quotientPhysicalRingMap p :=
  IsFractionRing.lift_algebraMap quotientPhysicalRingMap_injective p

@[simp] theorem quotientPhysicalFieldMap_base (r : BaseField) :
    quotientPhysicalFieldMap (algebraMap BaseField QuotientField r)=basePhysicalFieldMap r := by
  change quotientPhysicalFieldMap (algebraMap QuotientRing QuotientField
    (AdjoinRoot.of _ (MvPolynomial.C r)))=_
  rw [quotientPhysicalFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (MvPolynomial.C r))=_
  rw [AdjoinRoot.lift_of,physicalCoefficientMap_C]

def physicalModelCoordinates : Fin 5 → HoldoutFunctionField :=
  ![physicalY 0,physicalY 1,physicalY 2,physicalP,physicalQ]

theorem quotientPhysicalFieldMap_coordinate (j : Fin 5) :
    quotientPhysicalFieldMap (quotientResidueMap (MvPolynomial.X j))=physicalModelCoordinates j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [quotientResidueMap_X_zero,quotientPhysicalFieldMap_ring]
    change AdjoinRoot.lift (f := quotientPolynomial genericA genericB)
      physicalCoefficientMap (physicalY 0) physical_quotient_root
      (AdjoinRoot.root (quotientPolynomial genericA genericB))=physicalY 0
    exact AdjoinRoot.lift_root physical_quotient_root
  · rw [quotientResidueMap_X_succ,quotientPhysicalFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (MvPolynomial.X i))=_
    rw [AdjoinRoot.lift_of,physicalCoefficientMap_X]
    simp only [physicalIndependentCoordinates,physicalModelCoordinates,Matrix.cons_val_succ]

theorem quotientPhysicalFieldMap_residue (p : MvPolynomial (Fin 5) BaseField) :
    quotientPhysicalFieldMap (quotientResidueMap p)=
      MvPolynomial.eval₂Hom basePhysicalFieldMap physicalModelCoordinates p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [quotientResidueMap_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [map_mul,hp,quotientPhysicalFieldMap_coordinate,MvPolynomial.eval₂Hom_X']

end HoldoutBundle

#print axioms HoldoutBundle.quotientPhysicalRingMap_injective
#print axioms HoldoutBundle.quotientPhysicalFieldMap_residue
