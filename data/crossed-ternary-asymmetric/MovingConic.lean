import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra
import Proposal.ConicSeed
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal
import Mathlib.Data.Complex.Basic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FixedConicParamSeed. -/
section

noncomputable section
namespace CrossedFixedConic
open Polynomial
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev ParamRing := MvPolynomial (Fin 3) ℤ
def parameterVariables : Fin 3 → ParamRing := MvPolynomial.X

def seedParamMap : ParamRing →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K) parameters
instance seedParamAlgebra : Algebra ParamRing K := seedParamMap.toAlgebra

lemma seed_parameters : (fun i => seedParamMap (parameterVariables i)) = parameters := by
  funext i
  simp [seedParamMap,parameterVariables]

lemma seed_eval (P : MvPolynomial (Fin 13) ParamRing) :
    MvPolynomial.aeval seed P = MvPolynomial.eval₂Hom (RingHom.id K) seed
      (MvPolynomial.map seedParamMap P) := by
  change MvPolynomial.eval₂Hom seedParamMap seed P = _
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

lemma param_seed_equations (i : Fin 13) :
    MvPolynomial.aeval seed (equations parameterVariables i)=0 := by
  rw [seed_eval,equations_map,seed_parameters]
  exact seed_equations i

lemma param_seed_jacobian : IsUnit (Matrix.det (fun i j =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (equations parameterVariables j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (equations parameterVariables j))) =
      (fun i j : Fin 13 => MvPolynomial.eval₂Hom (RingHom.id K) seed
        (MvPolynomial.pderiv i (equations parameters j))) := by
    funext i j
    rw [seed_eval,equations_pderiv_map,seed_parameters]
  rw [hm]
  exact seed_jacobian_unit

lemma param_seed_free_det : MvPolynomial.aeval seed (freeMatrix parameterVariables).det ≠ 0 := by
  rw [seed_eval,freeDet_map,seed_parameters,RingHom.map_det]
  exact seedFree_det_ne_zero

abbrev Incidence := CrossedOpenIncidence.OpenSystemRing
  (equations parameterVariables) (freeMatrix parameterVariables).det

instance incidence_nontrivial : Nontrivial Incidence :=
  CrossedOpenIncidence.open_nontrivial (equations parameterVariables) seed
    param_seed_equations param_seed_jacobian (freeMatrix parameterVariables).det
    (isUnit_iff_ne_zero.mpr param_seed_free_det)

end CrossedFixedConic
end
end

/- Source component: FixedConicCoefficientField. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option profiler true
set_option profiler.threshold 100
open scoped TensorProduct
namespace CrossedFixedConic
open HoldoutConstruction
abbrev ComplexParamRing := MvPolynomial (Fin 3) ℂ
abbrev ParamField := FractionRing ComplexParamRing

def baseMap : ParamRing →+* ParamField :=
  (algebraMap ComplexParamRing ParamField).comp (MvPolynomial.map (Int.castRingHom ℂ))
instance genericParamAlgebra : Algebra ParamRing ParamField := baseMap.toAlgebra
noncomputable instance (priority := 2000) genericParamModule : Module ParamRing ParamField :=
  Algebra.toModule

noncomputable instance (priority := 2000) paramField_complexModule : Module ℂ ParamField :=
  Algebra.toModule

noncomputable instance (priority := 2000) genericParamSMul : SMul ParamRing ParamField :=
  genericParamModule.toSMul
noncomputable instance (priority := 2000) paramField_complexSMul : SMul ℂ ParamField :=
  paramField_complexModule.toSMul

instance (priority := 2000) genericParamComm : SMulCommClass ParamRing ParamRing ParamField where
  smul_comm a b x := by
    simp only [Algebra.smul_def]
    ring

lemma baseMap_injective : Function.Injective baseMap :=
  (IsFractionRing.injective ComplexParamRing ParamField).comp
    (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)

abbrev GenericIncidence := ParamField ⊗[ParamRing] Incidence

def coefficientIdeal := Classical.choose
  (genericEtale_exists_fieldFactor ParamRing ParamField Incidence baseMap_injective)

instance coefficientIdeal_maximal : coefficientIdeal.IsMaximal :=
  (Classical.choose_spec (genericEtale_exists_fieldFactor
    ParamRing ParamField Incidence baseMap_injective)).1

abbrev CoefficientField := @HasQuotient.Quotient _ _ Ideal.instHasQuotient coefficientIdeal
noncomputable instance coefficientField_field : Field CoefficientField := Ideal.Quotient.field _
instance coefficientField_finite : Module.Finite ParamField CoefficientField :=
  (Classical.choose_spec (genericEtale_exists_fieldFactor
    ParamRing ParamField Incidence baseMap_injective)).2.1
instance coefficientField_charZero : CharZero CoefficientField :=
  charZero_of_injective_ringHom (f := algebraMap ParamField CoefficientField)
    (algebraMap ParamField CoefficientField).injective

noncomputable instance (priority := 2000) coefficientField_genericModule :
    Module ParamField CoefficientField := Algebra.toModule

noncomputable instance (priority := 2000) coefficientField_genericSMul :
    SMul ParamField CoefficientField := coefficientField_genericModule.toSMul

noncomputable instance coefficientField_complexAlgebra : Algebra ℂ CoefficientField :=
  ((algebraMap ParamField CoefficientField).comp (algebraMap ℂ ParamField)).toAlgebra
noncomputable instance (priority := 2000) coefficientField_complexModule : Module ℂ CoefficientField :=
  Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_complexSMul :
    SMul ℂ CoefficientField := coefficientField_complexModule.toSMul
instance coefficientField_complexTower : IsScalarTower ℂ ParamField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

noncomputable instance coefficientField_paramAlgebra : Algebra ParamRing CoefficientField :=
  ((algebraMap ParamField CoefficientField).comp baseMap).toAlgebra
noncomputable instance (priority := 2000) coefficientField_paramModule :
    Module ParamRing CoefficientField := Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_paramSMul :
    SMul ParamRing CoefficientField := coefficientField_paramModule.toSMul
instance coefficientField_paramTower : IsScalarTower ParamRing ParamField CoefficientField :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def coefficientMap : Incidence →ₐ[ParamRing] CoefficientField where
  toRingHom := (Ideal.Quotient.mk coefficientIdeal).comp
    (Algebra.TensorProduct.includeRight : Incidence →ₐ[ParamRing] GenericIncidence).toRingHom
  commutes' r := by
    change Ideal.Quotient.mk coefficientIdeal
      ((Algebra.TensorProduct.includeRight : Incidence →ₐ[ParamRing] GenericIncidence)
        (algebraMap ParamRing Incidence r)) =
      Ideal.Quotient.mk coefficientIdeal
        ((Algebra.TensorProduct.includeLeft : ParamField →ₐ[ParamRing] GenericIncidence)
          (baseMap r))
    apply congrArg (Ideal.Quotient.mk coefficientIdeal)
    exact (Algebra.TensorProduct.includeRight : Incidence →ₐ[ParamRing] GenericIncidence).commutes r |>.trans
      ((Algebra.TensorProduct.includeLeft : ParamField →ₐ[ParamRing] GenericIncidence).commutes r).symm

def coefficients : Fin 13 → CoefficientField :=
  CrossedOpenIncidence.coordinates (equations parameterVariables)
    (freeMatrix parameterVariables).det coefficientMap

lemma coefficients_equations (i : Fin 13) :
    MvPolynomial.aeval coefficients (equations parameterVariables i)=0 :=
  CrossedOpenIncidence.solution _ _ _ i

lemma coefficients_free_unit : IsUnit
    (MvPolynomial.aeval coefficients (freeMatrix parameterVariables).det) :=
  CrossedOpenIncidence.open_unit _ _ _

end CrossedFixedConic
end
end

/- Source component: FixedConicCurveBounds. -/
section

noncomputable section
set_option maxHeartbeats 3000000
namespace CrossedFixedConic
open Polynomial
open CrossedConicIncidence (H gradient H_map gradient_map)

lemma curveEval_constant {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i : Fin 5) :
    (curveEval k f v i).coeff 0 = ![0,v 0,f (k 0),f (k 1),f (k 2)] i := by
  fin_cases i <;> simp [curveEval,curve,coeffVar,constPoly]

lemma curveEval_first {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) :
    curveEval k f v 0 = 4*X := by
  change (4*X : CurvePoly R).map (MvPolynomial.eval₂Hom f v) = _
  have h4 : (4 : CurvePoly R).map (MvPolynomial.eval₂Hom f v) = (4 : Polynomial S) :=
    map_natCast (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) 4
  rw [Polynomial.map_mul,Polynomial.map_X,h4]

lemma freeColumn_bound {R : Type*} [CommRing R] (k : Fin 3 → R) (j : Fin 12) :
    (gradient (curve k) (freeCoordinate j)*X^freeDegree j).natDegree ≤ 11 := by
  fin_cases j <;> dsimp [freeCoordinate,freeDegree,gradient,curve,coeffVar,constPoly]
  all_goals compute_degree!
  all_goals omega

lemma H_eval_bound {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) :
    (H (curveEval k f v)).natDegree ≤ 12 := by
  have hm := H_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) (curve k)
  change (H (curve k)).map (MvPolynomial.eval₂Hom f v) = H (curveEval k f v) at hm
  rw [← hm]
  exact Polynomial.natDegree_map_le.trans (H_natDegree_le k)

lemma freeColumn_eval_bound {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (j : Fin 12) :
    (gradient (curveEval k f v) (freeCoordinate j)*X^freeDegree j).natDegree ≤ 11 := by
  have hm := gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v))
    (curve k) (freeCoordinate j)
  change (gradient (curve k) (freeCoordinate j)).map (MvPolynomial.eval₂Hom f v) =
    gradient (curveEval k f v) (freeCoordinate j) at hm
  rw [← hm]
  have hx : (X : Polynomial (Coeff R)).map (MvPolynomial.eval₂Hom f v) = X := Polynomial.map_X _
  rw [← hx,← Polynomial.map_pow,← Polynomial.map_mul]
  exact Polynomial.natDegree_map_le.trans (freeColumn_bound k j)

end CrossedFixedConic
end
end

/- Source component: FixedConicCurve. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction
open CrossedConicIncidence (H gradient)
open scoped BigOperators

def scalarParameter (i : Fin 3) : CoefficientField :=
  algebraMap ParamRing CoefficientField (parameterVariables i)

def conicCurve : Fin 5 → Polynomial CoefficientField :=
  curveEval parameterVariables (algebraMap ParamRing CoefficientField) coefficients

lemma conicCurve_first : conicCurve 0 = 4*X :=
  curveEval_first _ _ _

lemma conicCurve_constant (i : Fin 5) : (conicCurve i).coeff 0 =
    ![0,coefficients 0,scalarParameter 0,scalarParameter 1,scalarParameter 2] i :=
  curveEval_constant _ _ _ i

lemma conicCurve_equation : H conicCurve=0 := by
  apply Polynomial.ext
  intro n
  by_cases hn : n<13
  · have h := coefficients_equations ⟨n,hn⟩
    change MvPolynomial.eval₂Hom (algebraMap ParamRing CoefficientField) coefficients
      (equations parameterVariables ⟨n,hn⟩)=0 at h
    rw [equations_eval] at h
    exact h
  · have hb : (H conicCurve).natDegree ≤ 12 := H_eval_bound _ _ _
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega))

def conicGradient : Fin 5 → Polynomial CoefficientField := gradient conicCurve
def conicFreeMatrix : Matrix (Fin 12) (Fin 12) CoefficientField := fun i j =>
  (conicGradient (freeCoordinate j)*X^freeDegree j).coeff i.val

lemma conicFreeMatrix_unit : IsUnit conicFreeMatrix.det := by
  have hm : MvPolynomial.aeval coefficients (freeMatrix parameterVariables).det =
      conicFreeMatrix.det := by
    change (MvPolynomial.eval₂Hom (algebraMap ParamRing CoefficientField) coefficients)
      (freeMatrix parameterVariables).det = _
    rw [RingHom.map_det]
    congr 1
    funext i j
    exact eval_freeMatrix_entry _ _ _ i j
  have hu : IsUnit (MvPolynomial.aeval coefficients (freeMatrix parameterVariables).det) :=
    coefficients_free_unit
  rw [hm] at hu
  exact hu

lemma conicGradient_column_bound (j : Fin 12) :
    (conicGradient (freeCoordinate j)*X^freeDegree j).natDegree < 12 :=
  lt_of_le_of_lt (freeColumn_eval_bound parameterVariables
    (algebraMap ParamRing CoefficientField) coefficients j) (by decide)

lemma conicNormal_exists : ∃ N : Fin 5 → Polynomial CoefficientField,
    polynomialPairing conicGradient N=1 :=
  CrossedPolynomialNormal.exists_full_polynomial_normal (by decide : 0<12)
    conicGradient freeCoordinate freeDegree conicGradient_column_bound conicFreeMatrix_unit

def conicNormal : Fin 5 → Polynomial CoefficientField := Classical.choose conicNormal_exists
lemma conicNormal_pairing : polynomialPairing conicGradient conicNormal=1 :=
  Classical.choose_spec conicNormal_exists

def endpointEmbedding : ComplexParamRing →+* CoefficientField :=
  (algebraMap ParamField CoefficientField).comp (algebraMap ComplexParamRing ParamField)
lemma endpointEmbedding_injective : Function.Injective endpointEmbedding :=
  (algebraMap ParamField CoefficientField).injective.comp
    (IsFractionRing.injective ComplexParamRing ParamField)

lemma endpointEmbedding_X (i : Fin 3) :
    endpointEmbedding (MvPolynomial.X i) = scalarParameter i := by
  change algebraMap ParamField CoefficientField
    (algebraMap ComplexParamRing ParamField (MvPolynomial.X i)) =
    algebraMap ParamField CoefficientField (baseMap (parameterVariables i))
  congr 1
  simp [baseMap,parameterVariables]

lemma endpointEmbedding_C (c : ℂ) :
    endpointEmbedding (MvPolynomial.C c) = algebraMap ℂ CoefficientField c := by
  rfl

end CrossedFixedConic
end
end

/- Source component: FixedConicEvaluation. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction

def remainingCoefficientMap : ComplexParamRing →+* Polynomial CoefficientField :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ CoefficientField))
    ![conicCurve 2,conicCurve 3,conicCurve 4]

lemma remainingCoefficientMap_constant :
    Polynomial.constantCoeff.comp remainingCoefficientMap = endpointEmbedding := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [remainingCoefficientMap,endpointEmbedding_C]
  · intro i
    simp only [RingHom.comp_apply,remainingCoefficientMap,MvPolynomial.eval₂Hom_X',
      Polynomial.constantCoeff_apply,endpointEmbedding_X]
    fin_cases i <;> simp [conicCurve_constant]

def targetCoefficientMap : MvPolynomial (Fin 4) ℂ →+* Polynomial CoefficientField :=
  (Polynomial.eval₂RingHom remainingCoefficientMap (Polynomial.C (4 : CoefficientField)*X)).comp
    (MvPolynomial.finSuccEquiv ℂ 3).toRingHom

lemma targetCoefficientMap_injective : Function.Injective targetCoefficientMap := by
  have hi : Function.Injective (Polynomial.constantCoeff.comp remainingCoefficientMap) := by
    rw [remainingCoefficientMap_constant]
    exact endpointEmbedding_injective
  exact (polynomial_family_injective remainingCoefficientMap hi 4 (by norm_num)).comp
    (MvPolynomial.finSuccEquiv ℂ 3).injective

lemma targetCoefficientMap_C (c : ℂ) : targetCoefficientMap (MvPolynomial.C c) =
    Polynomial.C (algebraMap ℂ CoefficientField c) := by
  simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_apply,remainingCoefficientMap]

lemma targetCoefficientMap_X (i : Fin 4) : targetCoefficientMap (MvPolynomial.X i) =
    ![conicCurve 0,conicCurve 2,conicCurve 3,conicCurve 4] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show targetCoefficientMap (MvPolynomial.X 0) = Polynomial.C (4 : CoefficientField)*X by
      simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_X_zero]]
    have hc : Polynomial.C (4 : CoefficientField) = (4 : Polynomial CoefficientField) :=
      map_natCast Polynomial.C 4
    simp [conicCurve_first,hc]
  · change (Polynomial.eval₂RingHom remainingCoefficientMap (Polynomial.C (4 : CoefficientField)*X))
      (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X j.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ remainingCoefficientMap (Polynomial.C (4 : CoefficientField)*X)
      (Polynomial.C (MvPolynomial.X j)) = _
    rw [Polynomial.eval₂_C]
    simp only [remainingCoefficientMap,MvPolynomial.eval₂Hom_X']
    rw [Matrix.cons_val_succ]

abbrev ConicFunctionField := CurveFunctionField CoefficientField

noncomputable instance conicFunctionField_complexAlgebra : Algebra ℂ ConicFunctionField :=
  inferInstanceAs (Algebra ℂ (FractionRing (Polynomial CoefficientField)))
noncomputable instance (priority := 2000) conicFunctionField_complexModule : Module ℂ ConicFunctionField :=
  Algebra.toModule
noncomputable instance (priority := 2000) conicFunctionField_complexSMul : SMul ℂ ConicFunctionField :=
  conicFunctionField_complexModule.toSMul
noncomputable instance (priority := 2000) conicFunctionField_coefficientModule :
    Module CoefficientField ConicFunctionField := Algebra.toModule
noncomputable instance (priority := 2000) conicFunctionField_coefficientSMul :
    SMul CoefficientField ConicFunctionField := conicFunctionField_coefficientModule.toSMul
instance conicFunctionField_complexTower : IsScalarTower ℂ CoefficientField ConicFunctionField :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def conicFieldCoordinate (i : Fin 5) : ConicFunctionField :=
  algebraMap (Polynomial CoefficientField) ConicFunctionField (conicCurve i)

def conicFieldCoefficientMap : MvPolynomial (Fin 4) ℂ →+* ConicFunctionField :=
  (algebraMap (Polynomial CoefficientField) ConicFunctionField).comp targetCoefficientMap
lemma conicFieldCoefficientMap_injective : Function.Injective conicFieldCoefficientMap :=
  (IsFractionRing.injective (Polynomial CoefficientField) ConicFunctionField).comp
    targetCoefficientMap_injective

lemma conicFieldCoefficientMap_C (c : ℂ) :
    conicFieldCoefficientMap (MvPolynomial.C c) = algebraMap ℂ ConicFunctionField c := by
  rw [conicFieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_C]
  rfl
lemma conicFieldCoefficientMap_X (i : Fin 4) :
    conicFieldCoefficientMap (MvPolynomial.X i) =
      ![conicFieldCoordinate 0,conicFieldCoordinate 2,conicFieldCoordinate 3,conicFieldCoordinate 4] i := by
  simp only [conicFieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_X]
  fin_cases i <;> rfl

end CrossedFixedConic
end
end

/- Source component: FixedConicTargetField. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction

lemma conicField_equation : CrossedConicIncidence.H conicFieldCoordinate=0 := by
  have h := congrArg (algebraMap (Polynomial CoefficientField) ConicFunctionField)
    conicCurve_equation
  rw [map_zero,CrossedConicIncidence.H_map] at h
  exact h

lemma conicField_root : CrossedFano.equation.eval₂ conicFieldCoefficientMap
    (conicFieldCoordinate 1)=0 := by
  have h := conicField_equation
  simp only [CrossedFano.equation,CrossedFano.lower,Polynomial.eval₂_add,
    Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    map_add,map_mul,map_pow,conicFieldCoefficientMap_C,conicFieldCoefficientMap_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  have h5 : algebraMap ℂ ConicFunctionField (5/7 : ℂ)=(5/7 : ConicFunctionField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  have h10 : algebraMap ℂ ConicFunctionField (10/7 : ℂ)=(10/7 : ConicFunctionField) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  rw [h5,h10]
  dsimp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one]
  simp only [Matrix.cons_val_one,Matrix.cons_val_succ,Matrix.cons_val_zero]
  unfold CrossedConicIncidence.H at h
  linear_combination h/7

def conicTargetRingMap : CrossedFano.CoordinateRing →+* ConicFunctionField :=
  AdjoinRoot.lift (f:=CrossedFano.equation) conicFieldCoefficientMap
    (conicFieldCoordinate 1) conicField_root

lemma conicTargetRingMap_injective : Function.Injective conicTargetRingMap :=
  monic_root_embedding_injective CrossedFano.equation CrossedFano.equation_monic
    CrossedFano.equation_irreducible conicFieldCoefficientMap
    conicFieldCoefficientMap_injective (conicFieldCoordinate 1) conicField_root

def conicTargetFieldMap : CrossedFano.FunctionField →+* ConicFunctionField :=
  IsFractionRing.lift conicTargetRingMap_injective

@[simp] lemma conicTargetFieldMap_ring (r : CrossedFano.CoordinateRing) :
    conicTargetFieldMap (algebraMap CrossedFano.CoordinateRing CrossedFano.FunctionField r)=
      conicTargetRingMap r :=
  IsFractionRing.lift_algebraMap conicTargetRingMap_injective r

@[simp] lemma conicTargetFieldMap_base (r : ℂ) :
    conicTargetFieldMap (algebraMap ℂ CrossedFano.FunctionField r)=
      algebraMap ℂ ConicFunctionField r := by
  change conicTargetFieldMap (algebraMap CrossedFano.CoordinateRing CrossedFano.FunctionField
    (AdjoinRoot.of CrossedFano.equation (MvPolynomial.C r))) = _
  rw [conicTargetFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _) = _
  rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_C]

noncomputable instance conicFunctionField_targetAlgebra :
    Algebra CrossedFano.FunctionField ConicFunctionField := conicTargetFieldMap.toAlgebra
instance conicFunctionField_targetTower : IsScalarTower ℂ CrossedFano.FunctionField ConicFunctionField :=
  IsScalarTower.of_algebraMap_eq (fun r => (conicTargetFieldMap_base r).symm)

lemma targetFunctionField_trdeg : Algebra.trdeg ℂ CrossedFano.FunctionField=4 := by
  apply monic_hypersurface_field_trdeg CrossedFano.equation CrossedFano.equation_monic
  exact ne_of_gt (CrossedFano.equation_monic.degree_pos_of_not_isUnit
    CrossedFano.equation_irreducible.not_isUnit)

lemma paramField_trdeg : Algebra.trdeg ℂ ParamField=3 := by
  rw [fractionRing_trdeg]
  simp [MvPolynomial.trdeg_of_isDomain]

instance paramField_essFiniteType : Algebra.EssFiniteType ℂ ParamField :=
  fractionRing_essFiniteType ℂ ComplexParamRing

lemma conicFunctionField_trdeg : Algebra.trdeg ℂ ConicFunctionField=4 := by
  rw [polynomial_fractionRing_trdeg ℂ ParamField CoefficientField,paramField_trdeg]
  norm_num

instance conicFunctionField_essFiniteType : Algebra.EssFiniteType ℂ ConicFunctionField :=
  polynomial_fractionRing_essFiniteType ℂ ParamField CoefficientField

instance conicFunctionField_finite : Module.Finite CrossedFano.FunctionField ConicFunctionField := by
  apply finite_of_same_finite_trdeg (K:=ℂ)
  · rw [targetFunctionField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [targetFunctionField_trdeg,conicFunctionField_trdeg]

end CrossedFixedConic
end
end

/- Source component: FixedConicDerivations. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction

local instance : Algebra ℤ ParamField := Ring.toIntAlgebra _
local instance : Algebra ℤ CoefficientField := Ring.toIntAlgebra _
local instance : Algebra ℤ ConicFunctionField := Ring.toIntAlgebra _

def parameterDerivation (i : Fin 3) : Derivation ℤ ParamField ParamField :=
  extendRingDerivation (P:=ComplexParamRing) (L:=ParamField) (integerPartial (R:=ℂ) i)

@[simp] lemma parameterDerivation_polynomial (i : Fin 3) (p : ComplexParamRing) :
    parameterDerivation i (algebraMap ComplexParamRing ParamField p)=
      algebraMap ComplexParamRing ParamField (integerPartial i p) :=
  extendRingDerivation_apply _ p

lemma parameterDerivations_commute (i j : Fin 3) :
    Function.Commute (parameterDerivation i) (parameterDerivation j) :=
  extendRingDerivation_commute _ _ (integerPartials_commute i j)

@[simp] lemma parameterDerivation_base (i : Fin 3) (c : ℂ) :
    parameterDerivation i (algebraMap ℂ ParamField c)=0 := by
  change parameterDerivation i (algebraMap ComplexParamRing ParamField (MvPolynomial.C c))=0
  rw [parameterDerivation_polynomial,integerPartial_C,map_zero]

def endpointDerivation (i : Fin 3) : Derivation ℤ CoefficientField CoefficientField :=
  extendFiniteDerivation (L:=CoefficientField) (parameterDerivation i)

lemma endpointDerivation_apply (i : Fin 3) (a : ParamField) :
    endpointDerivation i (algebraMap ParamField CoefficientField a)=
      algebraMap ParamField CoefficientField (parameterDerivation i a) :=
  extendFiniteDerivation_apply _ a

lemma endpointDerivations_commute (i j : Fin 3) :
    Function.Commute (endpointDerivation i) (endpointDerivation j) :=
  extendFiniteDerivation_commute _ _ (parameterDerivations_commute i j)

@[simp] lemma endpointDerivation_base (i : Fin 3) (c : ℂ) :
    endpointDerivation i (algebraMap ℂ CoefficientField c)=0 := by
  rw [IsScalarTower.algebraMap_apply ℂ ParamField CoefficientField,
    endpointDerivation_apply,parameterDerivation_base,map_zero]

@[simp] lemma endpointDerivation_parameter (i j : Fin 3) :
    endpointDerivation i (scalarParameter j) = if j=i then 1 else 0 := by
  rw [← endpointEmbedding_X]
  change endpointDerivation i (algebraMap ParamField CoefficientField
    (algebraMap ComplexParamRing ParamField (MvPolynomial.X j))) = _
  rw [endpointDerivation_apply,parameterDerivation_polynomial]
  by_cases h : j=i
  · subst j; simp
  · simp [integerPartial_X_of_ne _ _ h,h]

def polynomialDerivation : Fin 4 → Derivation ℤ (Polynomial CoefficientField)
    (Polynomial CoefficientField) :=
  Fin.cases timePolynomialDerivation (fun i => coefficientPolynomialDerivation (endpointDerivation i))

@[simp] lemma polynomialDerivation_zero : polynomialDerivation 0=timePolynomialDerivation := rfl
@[simp] lemma polynomialDerivation_succ (i : Fin 3) :
    polynomialDerivation i.succ=coefficientPolynomialDerivation (endpointDerivation i) := rfl

lemma polynomialDerivations_commute (i j : Fin 4) :
    Function.Commute (polynomialDerivation i) (polynomialDerivation j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (endpointDerivations_commute i j)

def sourceDerivation (i : Fin 4) : Derivation ℤ ConicFunctionField ConicFunctionField :=
  extendRingDerivation (polynomialDerivation i)

@[simp] lemma sourceDerivation_zero : sourceDerivation 0=curveTimeDerivation := rfl
@[simp] lemma sourceDerivation_succ (i : Fin 3) :
    sourceDerivation i.succ=curveCoefficientDerivation (endpointDerivation i) := rfl

@[simp] lemma sourceDerivation_polynomial (i : Fin 4) (p : Polynomial CoefficientField) :
    sourceDerivation i (algebraMap (Polynomial CoefficientField) ConicFunctionField p)=
      algebraMap (Polynomial CoefficientField) ConicFunctionField (polynomialDerivation i p) :=
  extendRingDerivation_apply _ p

lemma sourceDerivations_commute (i j : Fin 4) :
    Function.Commute (sourceDerivation i) (sourceDerivation j) :=
  extendRingDerivation_commute _ _ (polynomialDerivations_commute i j)

@[simp] lemma sourceDerivation_base (i : Fin 4) (c : ℂ) :
    sourceDerivation i (algebraMap ℂ ConicFunctionField c)=0 := by
  change sourceDerivation i (algebraMap CoefficientField ConicFunctionField
    (algebraMap ℂ CoefficientField c))=0
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

end CrossedFixedConic
end
end

/- Source component: FixedConicEvaluationMatrix. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction CrossedConicIncidence
open scoped BigOperators
local instance : Algebra ℤ CoefficientField := Ring.toIntAlgebra _
local instance : Algebra ℤ ConicFunctionField := Ring.toIntAlgebra _

def polynomialMatrix : Matrix (Fin 5) (Fin 5) (Polynomial CoefficientField) :=
  fun i => Fin.cases (conicNormal i) (fun j => polynomialDerivation j (conicCurve i))

@[simp] lemma polynomialMatrix_normal (i : Fin 5) : polynomialMatrix i 0=conicNormal i := rfl
@[simp] lemma polynomialMatrix_tangent (i : Fin 5) (j : Fin 4) :
    polynomialMatrix i j.succ=polynomialDerivation j (conicCurve i) := rfl

def constantMatrix : Matrix (Fin 5) (Fin 5) CoefficientField :=
  Polynomial.constantCoeff.mapMatrix polynomialMatrix

def independentCoordinate : Fin 4 → Fin 5 := ![0,2,3,4]

def rowMatrix : Matrix (Fin 5) (Fin 5) CoefficientField :=
  fun i => Fin.cases (fun j => (conicGradient j).coeff 0)
    (fun k j => if j=independentCoordinate k then 1 else 0) i

lemma rowProduct_first (j : Fin 5) :
    (rowMatrix*constantMatrix) 0 j=if j=0 then 1 else 0 := by
  change (∑ k,(conicGradient k).coeff 0*(polynomialMatrix k j).coeff 0)=_
  have hm : (∑ k,(conicGradient k).coeff 0*(polynomialMatrix k j).coeff 0)=
      (∑ k,conicGradient k*polynomialMatrix k j).coeff 0 := by
    change (∑ k,Polynomial.constantCoeff (conicGradient k)*
      Polynomial.constantCoeff (polynomialMatrix k j))=
      Polynomial.constantCoeff (∑ k,conicGradient k*polynomialMatrix k j)
    rw [map_sum]
    simp only [map_mul]
  rw [hm]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [polynomialMatrix_normal,ite_true]
    have h := congrArg (fun p : Polynomial CoefficientField => p.coeff 0) conicNormal_pairing
    simpa only [polynomialPairing,Polynomial.coeff_one_zero] using h
  · simp only [polynomialMatrix_tangent,Fin.succ_ne_zero,ite_false]
    have h := gradient_derivation_pairing (polynomialDerivation j) conicCurve conicCurve_equation
    have hc := congrArg (fun p : Polynomial CoefficientField => p.coeff 0) h
    simpa only [conicGradient,Polynomial.coeff_zero] using hc

lemma rowProduct_succ (i : Fin 4) (j : Fin 5) :
    (rowMatrix*constantMatrix) i.succ j=(polynomialMatrix (independentCoordinate i) j).coeff 0 := by
  simp [Matrix.mul_apply,rowMatrix,constantMatrix]

lemma first_time : (polynomialDerivation 0 (conicCurve 0)).coeff 0=4 := by
  rw [polynomialDerivation_zero,timePolynomialDerivation_apply,conicCurve_first]
  simp

lemma first_parameter (j : Fin 3) :
    (polynomialDerivation j.succ (conicCurve 0)).coeff 0=0 := by
  rw [polynomialDerivation_succ,conicCurve_first]
  have h4 : endpointDerivation j (4 : CoefficientField)=0 := (endpointDerivation j).map_natCast 4
  have hc4 : Polynomial.C (4 : CoefficientField)=(4 : Polynomial CoefficientField) := map_natCast Polynomial.C 4
  rw [← hc4]
  simp [Derivation.leibniz,h4]

lemma endpoint_parameter (i j : Fin 3) :
    (polynomialDerivation j.succ (conicCurve i.succ.succ)).coeff 0=if i=j then 1 else 0 := by
  rw [polynomialDerivation_succ,coefficientPolynomialDerivation_coeff,conicCurve_constant]
  have hv (T : Type) (a b : T) (v : Fin 3 → T) (k : Fin 3) :
      ![a,b,v 0,v 1,v 2] k.succ.succ=v k := by
    fin_cases k <;> rfl
  rw [hv CoefficientField 0 (coefficients 0) scalarParameter i]
  exact endpointDerivation_parameter j i

lemma rowProduct_det : (rowMatrix*constantMatrix).det=4 := by
  apply two_step_evaluation_det
  · exact rowProduct_first
  · exact (rowProduct_succ 0 1).trans first_time
  · intro j
    exact (rowProduct_succ 0 j.succ.succ).trans (first_parameter j)
  · intro i j
    rw [rowProduct_succ,polynomialMatrix_tangent]
    have he : independentCoordinate i.succ=i.succ.succ := by
      fin_cases i <;> rfl
    rw [he]
    exact endpoint_parameter i j

lemma constantMatrix_det_ne_zero : constantMatrix.det≠0 := by
  intro h
  have hd := rowProduct_det
  rw [Matrix.det_mul,h,mul_zero] at hd
  exact (by norm_num : (0 : CoefficientField)≠4) hd

lemma polynomialMatrix_det_ne_zero : polynomialMatrix.det≠0 := by
  intro h
  apply constantMatrix_det_ne_zero
  change (Polynomial.constantCoeff.mapMatrix polynomialMatrix).det=0
  rw [← RingHom.map_det,h,map_zero]

def evaluationMatrix : Matrix (Fin 5) (Fin 5) ConicFunctionField :=
  (algebraMap (Polynomial CoefficientField) ConicFunctionField).mapMatrix polynomialMatrix

lemma evaluationMatrix_det_ne_zero : evaluationMatrix.det≠0 := by
  rw [evaluationMatrix,← RingHom.map_det]
  simpa only [map_zero] using
    (IsFractionRing.injective (Polynomial CoefficientField) ConicFunctionField).ne
      polynomialMatrix_det_ne_zero

end CrossedFixedConic
end
end

/- Source component: FixedConicResidue. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace CrossedFixedConic
open Polynomial HoldoutConstruction
open scoped BigOperators
local instance : Algebra ℤ CrossedFano.FunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ ConicFunctionField := Ring.toIntAlgebra _

instance companion_charZero : CharZero CrossedFano.FunctionField :=
  charZero_of_injective_ringHom (f:=algebraMap ℂ CrossedFano.FunctionField)
    (algebraMap ℂ CrossedFano.FunctionField).injective

def coordinateSwap : Equiv.Perm (Fin 5) := Equiv.swap 0 1
def fieldEval : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField :=
  MvPolynomial.eval₂Hom (algebraMap ℂ ConicFunctionField)
    (fun i => conicFieldCoordinate (coordinateSwap i))

lemma conicTargetFieldMap_coordinate (i : Fin 5) :
    conicTargetFieldMap (CrossedFano.residueMap (MvPolynomial.X i))=
      conicFieldCoordinate (coordinateSwap i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [CrossedFano.residueMap,RingHom.comp_apply,CrossedFano.projection_X_zero]
    rw [conicTargetFieldMap_ring]
    exact AdjoinRoot.lift_root conicField_root
  · rw [CrossedFano.residueMap,RingHom.comp_apply,CrossedFano.projection_X_succ]
    rw [conicTargetFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _) = _
    rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_X]
    fin_cases j <;> rfl

lemma conicTargetFieldMap_residue (p : MvPolynomial (Fin 5) ℂ) :
    conicTargetFieldMap (CrossedFano.residueMap p)=fieldEval p := by
  have h : conicTargetFieldMap.comp CrossedFano.residueMap=fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,CrossedFano.residueMap_C,conicTargetFieldMap_base,
        fieldEval,MvPolynomial.eval₂Hom_C]
    · intro i
      simp only [RingHom.comp_apply,conicTargetFieldMap_coordinate,fieldEval,
        MvPolynomial.eval₂Hom_X']
  exact congrArg (fun φ : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField => φ p) h

lemma fieldEval_polynomial (p : MvPolynomial (Fin 5) ℂ) :
    fieldEval p=algebraMap (Polynomial CoefficientField) ConicFunctionField
      (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ CoefficientField))
        (fun i => conicCurve (coordinateSwap i)) p) := by
  have h : (algebraMap (Polynomial CoefficientField) ConicFunctionField).comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ CoefficientField))
        (fun i => conicCurve (coordinateSwap i)))=fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C,fieldEval]
      rfl
    · intro i
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',fieldEval,conicFieldCoordinate]
  exact (congrArg (fun φ : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField => φ p) h).symm

lemma gradient_evaluation (j : Fin 5) :
    fieldEval (MvPolynomial.pderiv j CrossedFano.hypersurface)=
      algebraMap (Polynomial CoefficientField) ConicFunctionField (conicGradient (coordinateSwap j)) := by
  change fieldEval (integerPartial j CrossedFano.hypersurface)=_
  rw [CrossedFano.hypersurface_partial]
  change fieldEval (CrossedConicIncidence.gradient
    ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
    (coordinateSwap j))=_
  have h := CrossedConicIncidence.gradient_map fieldEval
    ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
    (coordinateSwap j)
  rw [h]
  have hv : (fun i => fieldEval
      (![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] i))=
      conicFieldCoordinate := by
    funext i
    fin_cases i <;> simp [fieldEval,coordinateSwap,Equiv.swap_apply_def]
  rw [hv]
  exact (CrossedConicIncidence.gradient_map
    (algebraMap (Polynomial CoefficientField) ConicFunctionField) conicCurve (coordinateSwap j)).symm

def normalField (j : Fin 5) : ConicFunctionField :=
  algebraMap (Polynomial CoefficientField) ConicFunctionField (conicNormal (coordinateSwap j))

def bridgeMatrix : Matrix (Fin 5) (Fin 5) ConicFunctionField :=
  evaluationMatrix.submatrix coordinateSwap id

lemma bridgeMatrix_det_ne_zero : bridgeMatrix.det≠0 := by
  rw [bridgeMatrix,Matrix.det_permute]
  apply mul_ne_zero _ evaluationMatrix_det_ne_zero
  simp [coordinateSwap,Equiv.Perm.sign_swap,show (0 : Fin 5)≠1 by decide]

lemma gradient_normal_pairing :
    (∑ j,fieldEval (MvPolynomial.pderiv j CrossedFano.hypersurface)*normalField j)=1 := by
  simp only [gradient_evaluation,normalField,← map_mul,← map_sum]
  have h := conicNormal_pairing
  change (∑ j,conicGradient j*conicNormal j)=1 at h
  have he : (∑ j,conicGradient (coordinateSwap j)*conicNormal (coordinateSwap j))=
      ∑ j,conicGradient j*conicNormal j :=
    Equiv.sum_comp coordinateSwap (fun j => conicGradient j*conicNormal j)
  rw [he,h,map_one]

def targetDerivation (j : Fin 4) : Derivation ℤ ConicFunctionField ConicFunctionField :=
  extendFiniteDerivation (L:=ConicFunctionField) (CrossedFano.tangent j)

lemma targetDerivation_apply (j : Fin 4) (a : CrossedFano.FunctionField) :
    targetDerivation j (algebraMap CrossedFano.FunctionField ConicFunctionField a)=
      algebraMap CrossedFano.FunctionField ConicFunctionField (CrossedFano.tangent j a) :=
  extendFiniteDerivation_apply _ a

lemma finiteEvaluation (p : MvPolynomial (Fin 5) ℂ) :
    finiteQuotientEvaluation (K:=CrossedFano.FunctionField) (L:=ConicFunctionField)
      CrossedFano.projection p=fieldEval p := conicTargetFieldMap_residue p

theorem companion_residue_solution (A : MvPolynomial (Fin 5) ℂ) :
    ∃ w : Fin 4 → CrossedFano.FunctionField,
      residueDivergence CrossedFano.tangent
        (CrossedFano.residueMap (MvPolynomial.pderiv 0 CrossedFano.hypersurface)) w=
      -(CrossedFano.residueMap (MvPolynomial.pderiv 0 A)/
          CrossedFano.residueMap (MvPolynomial.pderiv 0 CrossedFano.hypersurface)-
        CrossedFano.residueMap A *CrossedFano.residueMap
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 CrossedFano.hypersurface))/
          (CrossedFano.residueMap (MvPolynomial.pderiv 0 CrossedFano.hypersurface))^2) := by
  let π := CrossedFano.projection
  let f := CrossedFano.hypersurface
  let ρ := finiteQuotientEvaluation (K:=CrossedFano.FunctionField) (L:=ConicFunctionField) π
  let χ := algebraMap CoefficientField ConicFunctionField
  have heval : Polynomial.eval₂RingHom χ (curveTime (E:=CoefficientField))=
      algebraMap (Polynomial CoefficientField) ConicFunctionField := curvePolynomial_eval₂
  have hρ (p : MvPolynomial (Fin 5) ℂ) : ρ p=fieldEval p := finiteEvaluation p
  have hρC (c : ℂ) : ρ (MvPolynomial.C c)=algebraMap ℂ ConicFunctionField c := by
    rw [hρ]
    exact MvPolynomial.eval₂Hom_C _ _ c
  have hρX (i : Fin 5) : ρ (MvPolynomial.X i)=conicFieldCoordinate (coordinateSwap i) := by
    rw [hρ]
    exact MvPolynomial.eval₂Hom_X' _ _ i
  have hf : ρ f=0 := by
    change algebraMap CrossedFano.FunctionField ConicFunctionField (CrossedFano.residueMap f)=0
    rw [(CrossedFano.residueMap_kernel f).mpr (dvd_refl _),map_zero]
  have hg : ρ (MvPolynomial.pderiv 0 f)≠0 := by
    change algebraMap CrossedFano.FunctionField ConicFunctionField
      (CrossedFano.residueMap (integerPartial 0 f))≠0
    exact (_root_.map_ne_zero _).mpr CrossedFano.normal_ne_zero
  have hE (j : Fin 4) (p : MvPolynomial (Fin 5) ℂ) : targetDerivation j (ρ p)=
      ρ (MvPolynomial.pderiv j.succ p)-ρ (MvPolynomial.pderiv j.succ f)/
        ρ (MvPolynomial.pderiv 0 f)*ρ (MvPolynomial.pderiv 0 p) := by
    change targetDerivation j (algebraMap CrossedFano.FunctionField ConicFunctionField
      (CrossedFano.residueMap p))=_
    rw [targetDerivation_apply,CrossedFano.tangent_apply]
    simp only [map_sub,map_div₀,map_mul,integerPartial_apply]
    rfl
  have hfamily : ∃ w : Fin 4 → ConicFunctionField,
      residueDivergence targetDerivation (ρ (MvPolynomial.pderiv 0 f)) w=
        -(ρ (MvPolynomial.pderiv 0 A)/ρ (MvPolynomial.pderiv 0 f)-
          ρ A*ρ (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 f))/
            (ρ (MvPolynomial.pderiv 0 f))^2) := by
    apply residue_solution_from_polynomial_curve (K:=CrossedFano.FunctionField)
      π CrossedFano.projection_surjective f A sourceDerivation targetDerivation
      bridgeMatrix normalField χ (curveTime (E:=CoefficientField)) 0
    · intro a
      exact curveTimeDerivation_coefficient a
    · exact curveTimeDerivation_time
    · exact hf
    · exact hg
    · exact bridgeMatrix_det_ne_zero
    · intro j; rfl
    · intro k i
      rw [hρX]
      exact (sourceDerivation_polynomial i (conicCurve (coordinateSwap k))).symm
    · change (∑ j,ρ (MvPolynomial.pderiv j f)*normalField j)=1
      simp_rw [hρ]
      exact gradient_normal_pairing
    · intro i c
      rw [hρC]
      exact sourceDerivation_base i c
    · exact sourceDerivations_commute
    · exact hE
    · intro c
      rw [hρC,heval]
      exact ⟨C (algebraMap ℂ CoefficientField c),rfl⟩
    · intro i
      rw [hρX,heval]
      exact ⟨conicCurve (coordinateSwap i),rfl⟩
    · intro i
      rw [heval]
      exact ⟨conicNormal (coordinateSwap i),rfl⟩
    · intro i x hx
      rw [heval] at hx ⊢
      exact extendRingDerivation_mem_range (polynomialDerivation i) x hx
  apply residue_solution_descends_finite CrossedFano.tangent targetDerivation targetDerivation_apply
  obtain ⟨w,hw⟩ := hfamily
  refine ⟨w,?_⟩
  rw [map_neg,map_sub,map_div₀,map_div₀,map_mul,map_pow]
  exact hw

end CrossedFixedConic
end
end
