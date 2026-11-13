import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.ConicPolynomialFamily
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap
import HodgeComputer.Constructions.HoldoutCover.QuotientDerivatives

/- Source component: ConicCoefficientEmbedding -/
section
/-!
Dominance of the conic evaluation map on the four coordinates X1,X2,S,P.
The three endpoint parameters are independent by the monic endpoint
presentation. The anchored coordinate X1=k*t supplies the fourth
independent coordinate by the constant-coefficient injectivity theorem.
-/

noncomputable section


namespace HoldoutConicIncidence

open HoldoutConstruction Polynomial

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero

def endpointCoefficientEmbedding (p : HoldoutConic.Seed) :
    MvPolynomial (Fin 3) FermatBaseField →+* ConicCoefficientField p :=
  (algebraMap FermatEndpointField (ConicCoefficientField p)).comp
    ((algebraMap (EndpointRing FermatBaseField) FermatEndpointField).comp
      (AdjoinRoot.of (endpointPolynomial (R := FermatBaseField))))

theorem endpointCoefficientEmbedding_injective (p : HoldoutConic.Seed) :
    Function.Injective (endpointCoefficientEmbedding p) := by
  intro a b h
  apply endpoint_of_injective (R := FermatBaseField)
  apply IsFractionRing.injective (EndpointRing FermatBaseField) FermatEndpointField
  apply (algebraMap FermatEndpointField (ConicCoefficientField p)).injective
  exact h

def curveRemainingCoefficientMap (p : HoldoutConic.Seed) :
    MvPolynomial (Fin 3) FermatBaseField →+* Polynomial (ConicCoefficientField p) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (algebraMap FermatBaseField (ConicCoefficientField p)))
    ![conicCurve p 2, conicCurve p 3, conicCurve p 4]

theorem curveRemainingCoefficientMap_constant (p : HoldoutConic.Seed) :
    Polynomial.constantCoeff.comp (curveRemainingCoefficientMap p) =
      endpointCoefficientEmbedding p := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, curveRemainingCoefficientMap,
      MvPolynomial.eval₂Hom_C, Polynomial.coeff_C_zero,
      Polynomial.constantCoeff_apply, endpointCoefficientEmbedding]
    rfl
  · intro i
    simp only [RingHom.comp_apply, curveRemainingCoefficientMap,
      MvPolynomial.eval₂Hom_X', Polynomial.constantCoeff_apply, endpointCoefficientEmbedding]
    change (![conicCurve p 2, conicCurve p 3, conicCurve p 4] i).coeff 0 =
      algebraMap FermatEndpointField (ConicCoefficientField p)
        (algebraMap (EndpointRing FermatBaseField) FermatEndpointField (endpointParameter i))
    have hindex : ![conicCurve p 2, conicCurve p 3, conicCurve p 4] i =
        conicCurve p i.succ.succ := by
      fin_cases i <;> rfl
    have hendpoint : conicEndpoint p i.succ.succ =
        conicSourceMap p (endpointParameter i) := by
      fin_cases i <;> rfl
    rw [hindex, conicCurve_constant, hendpoint, conicSourceMap_parameter]

def curveTargetCoefficientMap (p : HoldoutConic.Seed) :
    MvPolynomial (Fin 4) FermatBaseField →+* Polynomial (ConicCoefficientField p) :=
  (Polynomial.eval₂RingHom (curveRemainingCoefficientMap p)
    (Polynomial.C (conicK p)*Polynomial.X)).comp
      (MvPolynomial.finSuccEquiv FermatBaseField 3).toRingHom

theorem curveTargetCoefficientMap_injective (p : HoldoutConic.Seed) :
    Function.Injective (curveTargetCoefficientMap p) := by
  have hconst : Function.Injective
      (Polynomial.constantCoeff.comp (curveRemainingCoefficientMap p)) := by
    rw [curveRemainingCoefficientMap_constant]
    exact endpointCoefficientEmbedding_injective p
  exact (polynomial_family_injective (curveRemainingCoefficientMap p) hconst
    (conicK p) (conicK_ne_zero p)).comp
      (MvPolynomial.finSuccEquiv FermatBaseField 3).injective

@[simp] theorem curveTargetCoefficientMap_C (p : HoldoutConic.Seed) (r : FermatBaseField) :
    curveTargetCoefficientMap p (MvPolynomial.C r) =
      Polynomial.C (algebraMap FermatBaseField (ConicCoefficientField p) r) := by
  simp [curveTargetCoefficientMap, MvPolynomial.finSuccEquiv_apply,
    curveRemainingCoefficientMap]

theorem curveTargetCoefficientMap_X (p : HoldoutConic.Seed) (i : Fin 4) :
    curveTargetCoefficientMap p (MvPolynomial.X i) = conicCurve p i.succ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [curveTargetCoefficientMap, MvPolynomial.finSuccEquiv_X_zero,
      conicCurve_middle]
  · change (Polynomial.eval₂RingHom (curveRemainingCoefficientMap p)
      (Polynomial.C (conicK p)*Polynomial.X))
      (MvPolynomial.finSuccEquiv FermatBaseField 3 (MvPolynomial.X j.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ (curveRemainingCoefficientMap p)
      (Polynomial.C (conicK p)*Polynomial.X) (Polynomial.C (MvPolynomial.X j)) = _
    rw [Polynomial.eval₂_C]
    simp only [curveRemainingCoefficientMap, MvPolynomial.eval₂Hom_X']
    change ![conicCurve p 2, conicCurve p 3, conicCurve p 4] j = conicCurve p j.succ.succ
    fin_cases j <;> rfl

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.curveTargetCoefficientMap_injective
end
end

/- Source component: ConicTargetEmbedding -/
section
/-!
The dominant evaluation map of the anchored conic family gives an actual
finite embedding of the weighted quotient function field. Injectivity is
proved before any algebra structure or finite-extension instance is used.
-/

noncomputable section


namespace HoldoutConicIncidence

open HoldoutConstruction Polynomial

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero
attribute [local instance] quotient_adjoinRoot_isDomain quotient_charZero

def genericAlpha : FermatBaseField := algebraMap FermatCurveBase FermatBaseField baseAlpha
def genericBeta : FermatBaseField := algebraMap FermatCurveBase FermatBaseField baseBeta

abbrev ConicTargetRing := QuotientRing genericAlpha genericBeta
abbrev ConicTargetField := QuotientField genericAlpha genericBeta
abbrev ConicFunctionField (p : HoldoutConic.Seed) :=
  FractionRing (Polynomial (ConicCoefficientField p))

noncomputable instance conicTargetField_field : Field ConicTargetField := inferInstance
instance conicTargetField_charZero : CharZero ConicTargetField := inferInstance

def conicFieldCoordinate (p : HoldoutConic.Seed) (i : Fin 5) : ConicFunctionField p :=
  algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p) (conicCurve p i)

def conicFieldEval (p : HoldoutConic.Seed) :
    MvPolynomial (Fin 5) FermatBaseField →+* ConicFunctionField p :=
  MvPolynomial.eval₂Hom (algebraMap FermatBaseField (ConicFunctionField p))
    (conicFieldCoordinate p)

def conicFieldCoefficientMap (p : HoldoutConic.Seed) :
    MvPolynomial (Fin 4) FermatBaseField →+* ConicFunctionField p :=
  (algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)).comp
    (curveTargetCoefficientMap p)

theorem conicFieldCoefficientMap_injective (p : HoldoutConic.Seed) :
    Function.Injective (conicFieldCoefficientMap p) :=
  (IsFractionRing.injective (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)).comp
    (curveTargetCoefficientMap_injective p)

@[simp] theorem conicFieldCoefficientMap_C (p : HoldoutConic.Seed) (r : FermatBaseField) :
    conicFieldCoefficientMap p (MvPolynomial.C r) =
      algebraMap FermatBaseField (ConicFunctionField p) r := by
  rw [conicFieldCoefficientMap, RingHom.comp_apply, curveTargetCoefficientMap_C]
  rfl

@[simp] theorem conicFieldCoefficientMap_X (p : HoldoutConic.Seed) (i : Fin 4) :
    conicFieldCoefficientMap p (MvPolynomial.X i) = conicFieldCoordinate p i.succ := by
  rw [conicFieldCoefficientMap, RingHom.comp_apply, curveTargetCoefficientMap_X]
  rfl

theorem conicPolynomial_root (p : HoldoutConic.Seed) :
    (quotientPolynomial genericAlpha genericBeta).eval₂ (curveTargetCoefficientMap p)
      (conicCurve p 0) = 0 := by
  have h := conicCurve_equation p
  simp only [quotientPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    map_add, map_sub, map_mul, map_pow, map_ofNat,
    curveTargetCoefficientMap_C, curveTargetCoefficientMap_X, genericAlpha, genericBeta,
    ← conicAlpha_base, ← conicBeta_base,
    show (0 : Fin 4).succ = (1 : Fin 5) by decide,
    show (1 : Fin 4).succ = (2 : Fin 5) by decide,
    show (2 : Fin 4).succ = (3 : Fin 5) by decide,
    show (3 : Fin 4).succ = (4 : Fin 5) by decide]
  unfold H at h
  linear_combination h

theorem conicField_root (p : HoldoutConic.Seed) :
    (quotientPolynomial genericAlpha genericBeta).eval₂ (conicFieldCoefficientMap p)
      (conicFieldCoordinate p 0) = 0 := by
  have h := congrArg
    (algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p))
    (conicPolynomial_root p)
  rw [map_zero] at h
  rw [Polynomial.hom_eval₂] at h
  exact h

def conicTargetRingMap (p : HoldoutConic.Seed) : ConicTargetRing →+* ConicFunctionField p :=
  AdjoinRoot.lift (f := quotientPolynomial genericAlpha genericBeta)
    (conicFieldCoefficientMap p) (conicFieldCoordinate p 0) (conicField_root p)

theorem conicTargetRingMap_injective (p : HoldoutConic.Seed) :
    Function.Injective (conicTargetRingMap p) :=
  monic_root_embedding_injective (quotientPolynomial genericAlpha genericBeta)
    (quotientPolynomial_monic genericAlpha genericBeta)
    (quotientPolynomial_irreducible genericAlpha genericBeta)
    (conicFieldCoefficientMap p) (conicFieldCoefficientMap_injective p)
    (conicFieldCoordinate p 0) (conicField_root p)

def conicTargetFieldMap (p : HoldoutConic.Seed) : ConicTargetField →+* ConicFunctionField p :=
  IsFractionRing.lift (conicTargetRingMap_injective p)

@[simp] theorem conicTargetFieldMap_ring (p : HoldoutConic.Seed) (r : ConicTargetRing) :
    conicTargetFieldMap p (algebraMap ConicTargetRing ConicTargetField r) =
      conicTargetRingMap p r :=
  IsFractionRing.lift_algebraMap (conicTargetRingMap_injective p) r

@[simp] theorem conicTargetFieldMap_base (p : HoldoutConic.Seed) (r : FermatBaseField) :
    conicTargetFieldMap p (algebraMap FermatBaseField ConicTargetField r) =
      algebraMap FermatBaseField (ConicFunctionField p) r := by
  change conicTargetFieldMap p (algebraMap ConicTargetRing ConicTargetField
    (AdjoinRoot.of (quotientPolynomial genericAlpha genericBeta) (MvPolynomial.C r))) = _
  rw [conicTargetFieldMap_ring]
  change AdjoinRoot.lift _ _ _
    (AdjoinRoot.of (quotientPolynomial genericAlpha genericBeta) (MvPolynomial.C r)) = _
  rw [AdjoinRoot.lift_of, conicFieldCoefficientMap_C]

noncomputable instance conicFunctionField_targetAlgebra (p : HoldoutConic.Seed) :
    Algebra ConicTargetField (ConicFunctionField p) := (conicTargetFieldMap p).toAlgebra

instance conicFunctionField_baseTower (p : HoldoutConic.Seed) :
    IsScalarTower FermatBaseField ConicTargetField (ConicFunctionField p) :=
  IsScalarTower.of_algebraMap_eq (R := FermatBaseField) (S := ConicTargetField)
    (A := ConicFunctionField p) (fun r => (conicTargetFieldMap_base p r).symm)

theorem conicTargetFieldMap_coordinate (p : HoldoutConic.Seed) (i : Fin 5) :
    conicTargetFieldMap p
      (quotientResidueMap genericAlpha genericBeta (MvPolynomial.X i)) =
        conicFieldCoordinate p i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [quotientResidueMap_X_zero, conicTargetFieldMap_ring]
    exact AdjoinRoot.lift_root (conicField_root p)
  · rw [quotientResidueMap_X_succ, conicTargetFieldMap_ring]
    change AdjoinRoot.lift _ _ _
      (AdjoinRoot.of (quotientPolynomial genericAlpha genericBeta) (MvPolynomial.X j)) = _
    rw [AdjoinRoot.lift_of, conicFieldCoefficientMap_X]

theorem conicTargetFieldMap_residue (p : HoldoutConic.Seed)
    (f : MvPolynomial (Fin 5) FermatBaseField) :
    conicTargetFieldMap p (quotientResidueMap genericAlpha genericBeta f) =
      conicFieldEval p f := by
  have h : (conicTargetFieldMap p).comp (quotientResidueMap genericAlpha genericBeta) =
      conicFieldEval p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [conicFieldEval]
    · intro i
      simp only [RingHom.comp_apply, conicTargetFieldMap_coordinate,
        conicFieldEval, MvPolynomial.eval₂Hom_X']
  exact congrArg (fun φ : MvPolynomial (Fin 5) FermatBaseField →+* ConicFunctionField p => φ f) h

theorem conicTargetField_trdeg : Algebra.trdeg FermatBaseField ConicTargetField = 4 := by
  apply monic_hypersurface_field_trdeg (quotientPolynomial genericAlpha genericBeta)
    (quotientPolynomial_monic genericAlpha genericBeta)
  exact ne_of_gt ((quotientPolynomial_monic genericAlpha genericBeta).degree_pos_of_not_isUnit
    (quotientPolynomial_irreducible genericAlpha genericBeta).not_isUnit)

instance conicFunctionField_finite (p : HoldoutConic.Seed) :
    Module.Finite ConicTargetField (ConicFunctionField p) := by
  apply finite_of_same_finite_trdeg (K := FermatBaseField)
  · rw [conicTargetField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [conicTargetField_trdeg, conic_function_field_trdeg]

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.conicTargetRingMap_injective
#print axioms HoldoutConicIncidence.conicTargetFieldMap_residue
#print axioms HoldoutConicIncidence.conicFunctionField_finite
end
end
