import Proposal.BundleFields

/-! The Laurent coefficient base and its honest complex specialization. -/

noncomputable section

namespace HoldoutBundle

open Polynomial HoldoutConstruction

abbrev ParameterRing := Polynomial ℂ
abbrev BaseRing := Localization.Away (Polynomial.X : ParameterRing)
abbrev BaseField := FractionRing ParameterRing

instance baseRing_isDomain : IsDomain BaseRing :=
  Localization.Away.isDomain Polynomial.X_ne_zero

instance baseRing_charZero : CharZero BaseRing :=
  charZero_of_injective_ringHom (f := algebraMap ℂ BaseRing)
    (algebraMap ℂ BaseRing).injective

def baseLambda : BaseRing := algebraMap ParameterRing BaseRing Polynomial.X
def baseLambdaInv : BaseRing :=
  IsLocalization.Away.invSelf (S := BaseRing) (Polynomial.X : ParameterRing)
def baseI : BaseRing := algebraMap ℂ BaseRing Complex.I
def baseA : BaseRing := baseLambda+baseLambdaInv
def baseB : BaseRing := baseI*(baseLambda-baseLambdaInv)

theorem baseLambda_mul_inverse : baseLambda*baseLambdaInv=1 :=
  IsLocalization.Away.mul_invSelf (S := BaseRing) (Polynomial.X : ParameterRing)

def lambda : BaseField := algebraMap ParameterRing BaseField Polynomial.X

theorem lambda_ne_zero : lambda ≠ 0 := by
  intro h
  exact Polynomial.X_ne_zero (IsFractionRing.injective ParameterRing BaseField
    (h.trans (map_zero (algebraMap ParameterRing BaseField)).symm))

def baseFieldMap : BaseRing →+* BaseField :=
  Localization.awayLift (algebraMap ParameterRing BaseField) Polynomial.X
    (isUnit_iff_ne_zero.mpr lambda_ne_zero)

@[simp] theorem baseFieldMap_base (r : ParameterRing) :
    baseFieldMap (algebraMap ParameterRing BaseRing r)=
      algebraMap ParameterRing BaseField r := by
  simp [baseFieldMap, Localization.awayLift]

theorem baseFieldMap_injective : Function.Injective baseFieldMap := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n,r,hr⟩ := IsLocalization.Away.surj (Polynomial.X : ParameterRing) z
  have hm := congrArg baseFieldMap hr
  simp only [map_mul, map_pow, baseFieldMap_base, hz, zero_mul] at hm
  have hr0 : r=0 := IsFractionRing.injective ParameterRing BaseField
    (hm.symm.trans (map_zero (algebraMap ParameterRing BaseField)).symm)
  rw [hr0,map_zero] at hr
  exact (mul_eq_zero.mp hr).resolve_right
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : ParameterRing)).pow n).ne_zero

@[simp] theorem baseFieldMap_complex (r : ℂ) :
    baseFieldMap (algebraMap ℂ BaseRing r)=algebraMap ℂ BaseField r := by
  change baseFieldMap (algebraMap ParameterRing BaseRing (Polynomial.C r))=_
  rw [baseFieldMap_base]
  rfl

@[simp] theorem baseFieldMap_lambda : baseFieldMap baseLambda=lambda :=
  baseFieldMap_base Polynomial.X

@[simp] theorem baseFieldMap_inverse : baseFieldMap baseLambdaInv=lambda⁻¹ := by
  apply mul_left_cancel₀ lambda_ne_zero
  calc
    lambda*baseFieldMap baseLambdaInv = baseFieldMap (baseLambda*baseLambdaInv) := by simp
    _=1 := by rw [baseLambda_mul_inverse,map_one]
    _=lambda*lambda⁻¹ := (mul_inv_cancel₀ lambda_ne_zero).symm

abbrev genericA : BaseField := baseFieldMap baseA
abbrev genericB : BaseField := baseFieldMap baseB

theorem genericA_value : genericA=lambda+lambda⁻¹ := by
  simp [genericA,baseA]

theorem genericB_value : genericB=algebraMap ℂ BaseField Complex.I*(lambda-lambda⁻¹) := by
  simp [genericB,baseB,baseI]

def baseSeedMap : BaseRing →+* ℂ :=
  Localization.awayLift (Polynomial.evalRingHom Complex.I) Polynomial.X
    (by simpa using isUnit_iff_ne_zero.mpr Complex.I_ne_zero)

@[simp] theorem baseSeedMap_base (r : ParameterRing) :
    baseSeedMap (algebraMap ParameterRing BaseRing r)=r.eval Complex.I := by
  simp [baseSeedMap,Localization.awayLift]

@[simp] theorem baseSeedMap_complex (r : ℂ) :
    baseSeedMap (algebraMap ℂ BaseRing r)=r := by
  change baseSeedMap (algebraMap ParameterRing BaseRing (Polynomial.C r))=r
  simp

@[simp] theorem baseSeedMap_lambda : baseSeedMap baseLambda=Complex.I := by
  simp [baseLambda]

@[simp] theorem baseSeedMap_inverse : baseSeedMap baseLambdaInv = -Complex.I := by
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I*baseSeedMap baseLambdaInv=baseSeedMap (baseLambda*baseLambdaInv) := by simp
    _=1 := by rw [baseLambda_mul_inverse,map_one]
    _=Complex.I*(-Complex.I) := by simp [← pow_two,Complex.I_sq]

@[simp] theorem baseSeedMap_A : baseSeedMap baseA=0 := by simp [baseA]

@[simp] theorem baseSeedMap_B : baseSeedMap baseB = -2 := by
  simp [baseB,baseI,sub_neg_eq_add]
  linear_combination 2*Complex.I_sq

theorem baseB_ne_zero : baseB ≠ 0 := by
  intro h
  have hh := congrArg baseSeedMap h
  norm_num at hh

theorem genericB_ne_zero : genericB ≠ 0 := by
  exact fun h => baseB_ne_zero (baseFieldMap_injective
    (h.trans (map_zero baseFieldMap).symm))

abbrev IntegralEndpoint := EndpointCoordinateRing baseA baseB
abbrev GenericEndpoint := EndpointCoordinateRing genericA genericB
abbrev EndpointField := FractionRing GenericEndpoint
abbrev QuotientRing := QuotientCoordinateRing genericA genericB
abbrev QuotientField := FractionRing QuotientRing

/-- Stated once so that instance search does not have to rediscover it. -/
instance parameterRing_integrallyClosed : IsIntegrallyClosed (MvPolynomial (Fin 4) BaseField) :=
  UniqueFactorizationMonoid.instIsIntegrallyClosed

instance integralEndpoint_domain : IsDomain IntegralEndpoint :=
  endpoint_adjoinRoot_isDomain baseA baseB baseB_ne_zero

instance genericEndpoint_domain : IsDomain GenericEndpoint :=
  endpoint_adjoinRoot_isDomain genericA genericB genericB_ne_zero

instance quotientRing_domain : IsDomain QuotientRing :=
  quotient_adjoinRoot_isDomain genericA genericB genericB_ne_zero

instance integralEndpoint_charZero : CharZero IntegralEndpoint := endpoint_charZero _ _
instance genericEndpoint_charZero : CharZero GenericEndpoint := endpoint_charZero _ _

def endpointGenericMap : IntegralEndpoint →+* EndpointField :=
  (algebraMap GenericEndpoint EndpointField).comp (endpointMap baseFieldMap baseA baseB)

theorem endpointGenericMap_injective : Function.Injective endpointGenericMap := by
  intro x y h
  apply endpointMap_injective baseFieldMap baseFieldMap_injective baseA baseB
  apply IsFractionRing.injective GenericEndpoint EndpointField
  exact h

@[simp] theorem endpointGenericMap_root :
    endpointGenericMap (endpointRoot baseA baseB)=
      algebraMap GenericEndpoint EndpointField (endpointRoot genericA genericB) := by
  change algebraMap GenericEndpoint EndpointField
    (endpointMap baseFieldMap baseA baseB (endpointRoot baseA baseB))=_
  rw [endpointMap_root]

@[simp] theorem endpointGenericMap_parameter (j : Fin 3) :
    endpointGenericMap (endpointParameter baseA baseB j)=
      algebraMap GenericEndpoint EndpointField (endpointParameter genericA genericB j) := by
  change algebraMap GenericEndpoint EndpointField
    (endpointMap baseFieldMap baseA baseB (endpointParameter baseA baseB j))=_
  rw [endpointMap_parameter]

@[simp] theorem endpointGenericMap_base (r : BaseRing) :
    endpointGenericMap (algebraMap BaseRing IntegralEndpoint r)=
      algebraMap BaseField EndpointField (baseFieldMap r) := by
  change algebraMap GenericEndpoint EndpointField
    (endpointMap baseFieldMap baseA baseB
      (AdjoinRoot.of _ (MvPolynomial.C r)))=_
  simp only [endpointMap,AdjoinRoot.map_of,MvPolynomial.map_C]
  rfl

instance endpointGenericAlgebra : Algebra IntegralEndpoint EndpointField :=
  endpointGenericMap.toAlgebra

def integralEndpointSeedMap : IntegralEndpoint →+* ℂ :=
  AdjoinRoot.lift (f := endpointPolynomial baseA baseB)
    (MvPolynomial.eval₂Hom baseSeedMap ![1,4,1]) 1 (by
      norm_num [endpointPolynomial,baseSeedMap_A,baseSeedMap_B])

@[simp] theorem integralEndpointSeedMap_root :
    integralEndpointSeedMap (endpointRoot baseA baseB)=1 := by
  simp [integralEndpointSeedMap,endpointRoot]

@[simp] theorem integralEndpointSeedMap_parameter (j : Fin 3) :
    integralEndpointSeedMap (endpointParameter baseA baseB j)=![1,4,1] j := by
  simp [integralEndpointSeedMap,endpointParameter]

@[simp] theorem integralEndpointSeedMap_base (r : BaseRing) :
    integralEndpointSeedMap (algebraMap BaseRing IntegralEndpoint r)=baseSeedMap r := by
  change integralEndpointSeedMap (AdjoinRoot.of _ (MvPolynomial.C r))=baseSeedMap r
  simp [integralEndpointSeedMap]

theorem endpointField_trdeg : Algebra.trdeg BaseField EndpointField=3 := by
  apply monic_hypersurface_field_trdeg (endpointPolynomial genericA genericB)
    (endpointPolynomial_monic _ _)
  rw [endpointPolynomial_degree]
  decide

instance endpointField_essFiniteType : Algebra.EssFiniteType BaseField EndpointField :=
  monic_hypersurface_field_essFiniteType (endpointPolynomial genericA genericB)

theorem quotientField_trdeg : Algebra.trdeg BaseField QuotientField=4 := by
  apply monic_hypersurface_field_trdeg (quotientPolynomial genericA genericB)
    (quotientPolynomial_monic _ _)
  exact ne_of_gt ((quotientPolynomial_monic _ _).degree_pos_of_not_isUnit
    (quotientPolynomial_irreducible _ _ genericB_ne_zero).not_isUnit)

instance quotientField_essFiniteType : Algebra.EssFiniteType BaseField QuotientField :=
  monic_hypersurface_field_essFiniteType (quotientPolynomial genericA genericB)

end HoldoutBundle
