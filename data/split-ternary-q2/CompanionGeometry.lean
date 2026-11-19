import Proposal.CompanionSeeds
import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting

/-!
A characteristic-zero polynomial family for each of the two fixed companions.
The nonsingular finite-field incidences are proved in CompanionSeeds. Arithmetic
lifting, normal linear algebra and anchored dominance use the shared libraries
of fqlx and 1337isnot1337, with their original attribution. This target-specific
application was prepared with OpenAI Codex assistance for fqlx.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace SplitCompanion
open Polynomial HoldoutConstruction
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

lemma curve_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 3 → R) (i : Fin 5) :
    (curve k i).map (MvPolynomial.map f)=curve (fun j => f (k j)) i := by
  have h4 : (4 : CurvePoly R).map (MvPolynomial.map f)=(4 : CurvePoly S) :=
    map_natCast (Polynomial.mapRingHom (MvPolynomial.map f)) 4
  fin_cases i <;> simp [curve,coeffVar,constPoly,h4]

lemma equations_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (which : Bool) (s : R) (k : Fin 3 → R) (i : Fin 13) :
    MvPolynomial.map f (equations which s k i)=equations which (f s) (fun j => f (k j)) i := by
  rw [equations,← Polynomial.coeff_map]
  have hh : (H which (constPoly s) (curve k)).map (MvPolynomial.map f)=
      H which (constPoly (f s)) (curve (fun j => f (k j))) := by
    have h := H_map (Polynomial.mapRingHom (MvPolynomial.map f)) which (constPoly s) (curve k)
    change (H which (constPoly s) (curve k)).map (MvPolynomial.map f)=_ at h
    rw [h]
    have hc : (Polynomial.mapRingHom (MvPolynomial.map f)) (constPoly s)=constPoly (f s) := by
      simp [constPoly]
    rw [hc]
    congr 1
    funext j
    exact curve_map f k j
  rw [hh]
  rfl

lemma equations_pderiv_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (which : Bool) (s : R) (k : Fin 3 → R) (i j : Fin 13) :
    MvPolynomial.map f (MvPolynomial.pderiv j (equations which s k i))=
      MvPolynomial.pderiv j (equations which (f s) (fun j => f (k j)) i) := by
  rw [← MvPolynomial.pderiv_map,equations_map]

abbrev ParamRing := MvPolynomial (Fin 3) ℤ
abbrev ComplexParamRing := MvPolynomial (Fin 3) ℂ
abbrev ParamField := FractionRing ComplexParamRing

def parameterVariables : Fin 3 → ParamRing := MvPolynomial.X

def integralEquations (which : Bool) : Fin 13 → MvPolynomial (Fin 13) ParamRing :=
  equations which 0 parameterVariables

def seedParamMap : ParamRing →+* K := MvPolynomial.eval₂Hom (Int.castRingHom K) parameters
instance seedParamAlgebra : Algebra ParamRing K := seedParamMap.toAlgebra

lemma seed_parameters : (fun i => seedParamMap (parameterVariables i))=parameters := by
  funext i
  simp [seedParamMap,parameterVariables]

lemma seed_eval (P : MvPolynomial (Fin 13) ParamRing) :
    MvPolynomial.aeval seed P=MvPolynomial.eval₂Hom (RingHom.id K) seed
      (MvPolynomial.map seedParamMap P) := by
  change MvPolynomial.eval₂Hom seedParamMap seed P=_
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

lemma param_seed_equations (which : Bool) (i : Fin 13) :
    MvPolynomial.aeval seed (integralEquations which i)=0 := by
  rw [seed_eval,integralEquations,equations_map,seed_parameters,map_zero]
  exact seed_equations which 0 i

lemma param_seed_jacobian (which : Bool) : IsUnit (Matrix.det (fun i j =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (integralEquations which j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integralEquations which j)))=
      (fun i j : Fin 13 => MvPolynomial.eval₂Hom (RingHom.id K) seed
        (MvPolynomial.pderiv i (equations which 0 parameters j))) := by
    funext i j
    rw [seed_eval,integralEquations,equations_pderiv_map,seed_parameters,map_zero]
  rw [hm]
  exact seed_jacobian_unit which 0

abbrev Incidence (which : Bool) := SquareEtaleRing (integralEquations which)
instance incidence_nontrivial (which : Bool) : Nontrivial (Incidence which) :=
  square_system_jacobian_nontrivial (integralEquations which) seed
    (param_seed_equations which) (param_seed_jacobian which)

def baseMap : ParamRing →+* ParamField :=
  (algebraMap ComplexParamRing ParamField).comp (MvPolynomial.map (Int.castRingHom ℂ))
instance genericParamAlgebra : Algebra ParamRing ParamField := baseMap.toAlgebra
noncomputable instance (priority := 2000) genericParamModule : Module ParamRing ParamField := Algebra.toModule
noncomputable instance (priority := 2000) paramField_complexModule : Module ℂ ParamField := Algebra.toModule
noncomputable instance (priority := 2000) genericParamSMul : SMul ParamRing ParamField := genericParamModule.toSMul
noncomputable instance (priority := 2000) paramField_complexSMul : SMul ℂ ParamField := paramField_complexModule.toSMul
instance (priority := 2000) genericParamComm : SMulCommClass ParamRing ParamRing ParamField where
  smul_comm a b x := by simp only [Algebra.smul_def]; ring

lemma baseMap_injective : Function.Injective baseMap :=
  (IsFractionRing.injective ComplexParamRing ParamField).comp
    (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)

abbrev GenericIncidence (which : Bool) := SquareGenericAlgebra ParamField (integralEquations which)

def coefficientIdeal (which : Bool) := Classical.choose
  (squareGeneric_exists_fieldFactor (K:=ParamField) (integralEquations which) baseMap_injective)
instance coefficientIdeal_maximal (which : Bool) : (coefficientIdeal which).IsMaximal :=
  (Classical.choose_spec (squareGeneric_exists_fieldFactor (K:=ParamField)
    (integralEquations which) baseMap_injective)).1

abbrev CoefficientField (which : Bool) :=
  @HasQuotient.Quotient _ _ Ideal.instHasQuotient (coefficientIdeal which)
noncomputable instance coefficientField_field (which : Bool) : Field (CoefficientField which) := Ideal.Quotient.field _
instance coefficientField_finite (which : Bool) : Module.Finite ParamField (CoefficientField which) :=
  (Classical.choose_spec (squareGeneric_exists_fieldFactor (K:=ParamField)
    (integralEquations which) baseMap_injective)).2.1
instance coefficientField_charZero (which : Bool) : CharZero (CoefficientField which) :=
  charZero_of_injective_ringHom (f:=algebraMap ParamField (CoefficientField which))
    (algebraMap ParamField (CoefficientField which)).injective
noncomputable instance (priority := 2000) coefficientField_genericModule (which : Bool) :
    Module ParamField (CoefficientField which) := Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_genericSMul (which : Bool) :
    SMul ParamField (CoefficientField which) := (coefficientField_genericModule which).toSMul
noncomputable instance coefficientField_complexAlgebra (which : Bool) : Algebra ℂ (CoefficientField which) :=
  ((algebraMap ParamField (CoefficientField which)).comp (algebraMap ℂ ParamField)).toAlgebra
noncomputable instance (priority := 2000) coefficientField_complexModule (which : Bool) :
    Module ℂ (CoefficientField which) := Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_complexSMul (which : Bool) :
    SMul ℂ (CoefficientField which) := (coefficientField_complexModule which).toSMul
instance coefficientField_complexTower (which : Bool) : IsScalarTower ℂ ParamField (CoefficientField which) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
noncomputable instance coefficientField_paramAlgebra (which : Bool) : Algebra ParamRing (CoefficientField which) :=
  ((algebraMap ParamField (CoefficientField which)).comp baseMap).toAlgebra
noncomputable instance (priority := 2000) coefficientField_paramModule (which : Bool) :
    Module ParamRing (CoefficientField which) := Algebra.toModule
noncomputable instance (priority := 2000) coefficientField_paramSMul (which : Bool) :
    SMul ParamRing (CoefficientField which) := (coefficientField_paramModule which).toSMul
instance coefficientField_paramTower (which : Bool) : IsScalarTower ParamRing ParamField (CoefficientField which) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def coefficients (which : Bool) : Fin 13 → CoefficientField which :=
  squareGenericCoordinates (integralEquations which) (coefficientIdeal which)
lemma coefficients_equations (which : Bool) (i : Fin 13) :
    MvPolynomial.aeval (coefficients which) (integralEquations which i)=0 :=
  squareGeneric_solution _ _ i
lemma coefficients_jacobian_unit (which : Bool) : IsUnit (Matrix.det (fun i j =>
    MvPolynomial.aeval (coefficients which) (MvPolynomial.pderiv i (integralEquations which j)))) :=
  squareGeneric_jacobian _ _

lemma curveEval_constant {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (i : Fin 5) :
    (curveEval k f v i).coeff 0=![0,v 0,f (k 0),f (k 1),f (k 2)] i := by
  fin_cases i <;> simp [curveEval,curve,coeffVar,constPoly]
lemma curveEval_first {R S : Type*} [CommRing R] [CommRing S]
    (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) : curveEval k f v 0=4*X := by
  change (4*X : CurvePoly R).map (MvPolynomial.eval₂Hom f v)=_
  have h4 : (4 : CurvePoly R).map (MvPolynomial.eval₂Hom f v)=(4 : Polynomial S) :=
    map_natCast (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) 4
  rw [Polynomial.map_mul,Polynomial.map_X,h4]

lemma column_bound {R : Type*} [CommRing R] (which : Bool) (s : R)
    (k : Fin 3 → R) (j : Fin 13) :
    (gradient which (constPoly s) (curve k) (slotCoordinate j)*X^slotDegree j).natDegree ≤ 12 := by
  cases which <;> fin_cases j <;>
    dsimp [slotCoordinate,slotDegree,gradient,curve,coeffVar,constPoly]
  all_goals compute_degree!
  all_goals omega

lemma H_eval_bound {R S : Type*} [CommRing R] [CommRing S]
    (which : Bool) (s : R) (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) :
    (H which (Polynomial.C (f s)) (curveEval k f v)).natDegree ≤ 12 := by
  have hm := H_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) which (constPoly s) (curve k)
  have he : (H which (constPoly s) (curve k)).map (MvPolynomial.eval₂Hom f v)=
      H which (Polynomial.C (f s)) (curveEval k f v) := by
    convert hm using 1 <;> simp [constPoly] <;> rfl
  rw [← he]
  exact Polynomial.natDegree_map_le.trans (H_natDegree_le which s k)

lemma column_eval_bound {R S : Type*} [CommRing R] [CommRing S]
    (which : Bool) (s : R) (k : Fin 3 → R) (f : R →+* S) (v : Fin 13 → S) (j : Fin 13) :
    (gradient which (Polynomial.C (f s)) (curveEval k f v) (slotCoordinate j)*X^slotDegree j).natDegree ≤ 12 := by
  have hm := gradient_map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f v)) which (constPoly s) (curve k) (slotCoordinate j)
  have he : (gradient which (constPoly s) (curve k) (slotCoordinate j)).map (MvPolynomial.eval₂Hom f v)=
      gradient which (Polynomial.C (f s)) (curveEval k f v) (slotCoordinate j) := by
    convert hm using 1 <;> simp [constPoly] <;> rfl
  rw [← he]
  have hx : (X : Polynomial (Coeff R)).map (MvPolynomial.eval₂Hom f v)=X := Polynomial.map_X _
  rw [← hx,← Polynomial.map_pow,← Polynomial.map_mul]
  exact Polynomial.natDegree_map_le.trans (column_bound which s k j)

def scalarParameter (which : Bool) (i : Fin 3) : CoefficientField which :=
  algebraMap ParamRing (CoefficientField which) (parameterVariables i)
def conicCurve (which : Bool) : Fin 5 → Polynomial (CoefficientField which) :=
  curveEval parameterVariables (algebraMap ParamRing (CoefficientField which)) (coefficients which)
lemma conicCurve_first (which : Bool) : conicCurve which 0=4*X := curveEval_first _ _ _
lemma conicCurve_constant (which : Bool) (i : Fin 5) : (conicCurve which i).coeff 0=
    ![0,coefficients which 0,scalarParameter which 0,scalarParameter which 1,scalarParameter which 2] i :=
  curveEval_constant _ _ _ i
lemma conicCurve_equation (which : Bool) : H which 0 (conicCurve which)=0 := by
  ext n
  by_cases hn : n<13
  · have h := coefficients_equations which ⟨n,hn⟩
    change MvPolynomial.eval₂Hom (algebraMap ParamRing (CoefficientField which)) (coefficients which)
      (equations which 0 parameterVariables ⟨n,hn⟩)=0 at h
    rw [equations_eval] at h
    convert h using 1 <;> simp only [map_zero,Polynomial.coeff_zero] <;> rfl
  · have hb : (H which 0 (conicCurve which)).natDegree ≤ 12 := by
      convert H_eval_bound which (0 : ParamRing) parameterVariables
        (algebraMap ParamRing (CoefficientField which)) (coefficients which) using 1 <;>
          simp only [map_zero] <;> rfl
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega))

def conicGradient (which : Bool) : Fin 5 → Polynomial (CoefficientField which) := gradient which 0 (conicCurve which)
def conicJacobian (which : Bool) : Matrix (Fin 13) (Fin 13) (CoefficientField which) := fun i j =>
  (conicGradient which (slotCoordinate j)*X^slotDegree j).coeff i.val
lemma conicJacobian_unit (which : Bool) : IsUnit (conicJacobian which).det := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval (coefficients which)
      (MvPolynomial.pderiv i (integralEquations which j)))=(conicJacobian which).transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (algebraMap ParamRing (CoefficientField which)) (coefficients which)
      (MvPolynomial.pderiv i (equations which 0 parameterVariables j))=_
    rw [equations_pderiv_eval]
    simp only [map_zero]
    rfl
  have hu := coefficients_jacobian_unit which
  rw [hm,Matrix.det_transpose] at hu
  exact hu

lemma normalCoefficients_exists (which : Bool) : ∃ u : Fin 13 → CoefficientField which,
    ∑ j, C (u j)*(conicGradient which (slotCoordinate j)*X^slotDegree j)=1 := by
  apply CrossedPolynomialNormal.full_linear_combination_one (by decide : 0<13)
  · intro j
    have h := column_eval_bound which (0 : ParamRing) parameterVariables
      (algebraMap ParamRing (CoefficientField which)) (coefficients which) j
    apply lt_of_le_of_lt (b:=12) ?_ (by decide)
    convert h using 1 <;> (try simp only [map_zero]) <;> rfl
  · exact conicJacobian_unit which

def normalCoefficients (which : Bool) : Fin 13 → CoefficientField which := Classical.choose (normalCoefficients_exists which)
def conicNormal (which : Bool) (i : Fin 5) : Polynomial (CoefficientField which) :=
  ∑ j, C (normalCoefficients which j)*(if i=slotCoordinate j then X^slotDegree j else 0)
lemma conicNormal_pairing (which : Bool) : polynomialPairing (conicGradient which) (conicNormal which)=1 := by
  have h := Classical.choose_spec (normalCoefficients_exists which)
  have he : polynomialPairing (conicGradient which) (conicNormal which)=
      ∑ j, C (normalCoefficients which j)*(conicGradient which (slotCoordinate j)*X^slotDegree j) := by
    unfold polynomialPairing conicNormal
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (slotCoordinate j)]
    · simp; ring
    · intro b hb hbj
      simp [hbj]
    · simp
  rw [he]
  exact h
lemma conicNormal_first (which : Bool) : conicNormal which 0=0 := by
  simp [conicNormal,slotCoordinate,Fin.sum_univ_succ]
def endpointIndex : Fin 3 → Fin 5 := ![2,3,4]
lemma conicNormal_endpoint_constant (which : Bool) (i : Fin 3) :
    (conicNormal which (endpointIndex i)).coeff 0=0 := by
  fin_cases i <;> simp [endpointIndex,conicNormal,slotCoordinate,slotDegree,Fin.sum_univ_succ]

def endpointEmbedding (which : Bool) : ComplexParamRing →+* CoefficientField which :=
  (algebraMap ParamField (CoefficientField which)).comp (algebraMap ComplexParamRing ParamField)
lemma endpointEmbedding_injective (which : Bool) : Function.Injective (endpointEmbedding which) :=
  (algebraMap ParamField (CoefficientField which)).injective.comp
    (IsFractionRing.injective ComplexParamRing ParamField)
lemma endpointEmbedding_X (which : Bool) (i : Fin 3) :
    endpointEmbedding which (MvPolynomial.X i)=scalarParameter which i := by
  change algebraMap ParamField (CoefficientField which)
    (algebraMap ComplexParamRing ParamField (MvPolynomial.X i))=
      algebraMap ParamField (CoefficientField which) (baseMap (parameterVariables i))
  congr 1
  simp [baseMap,parameterVariables]
lemma endpointEmbedding_C (which : Bool) (c : ℂ) :
    endpointEmbedding which (MvPolynomial.C c)=algebraMap ℂ (CoefficientField which) c := rfl

end SplitCompanion

namespace SplitCompanionDomain
open Polynomial
abbrev Coeff := MvPolynomial (Fin 4) ℂ

/-- The normal variable is the second ordinary coordinate; coefficient
coordinates are the first, third and two cubic companion coordinates. -/
def lower (which : Bool) : Polynomial Coeff :=
  let x := MvPolynomial.X 0
  let y := MvPolynomial.X 1
  C (x^6+y^6+MvPolynomial.X 2^3+MvPolynomial.X 3^3)+
    C (MvPolynomial.C (5/7 : ℂ)) *
      (if which then C (x^5)*X+C (x^2*y)*X^3+C (3*x*y^5)+C (2*y)*X^5
       else C (2*x^5+2*x^3*y^2)*X+C (x*y^5)+C (3*y)*X^5)
def equation (which : Bool) : Polynomial Coeff := X^6+lower which
lemma lower_degree (which : Bool) : (lower which).degree<6 := by
  cases which <;> unfold lower <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    compute_degree <;> norm_num
lemma equation_monic (which : Bool) : (equation which).Monic :=
  monic_X_pow_add (by simpa using lower_degree which)
def specialization : Coeff →+* ℂ[X] := MvPolynomial.eval₂Hom C ![0,0,X-1,1]
lemma equation_specialization (which : Bool) : (equation which).map specialization=
    (X : (ℂ[X])[X])^6+C ((X-1)^3+1) := by
  cases which <;> simp [equation,lower,specialization]
lemma equation_irreducible (which : Bool) : Irreducible (equation which) := by
  apply (equation_monic which).irreducible_of_irreducible_map specialization
  rw [equation_specialization]
  have he : (X-1)^3+1=(X^3-3*X^2+3*X : ℂ[X]) := by ring
  rw [he]
  exact HoldoutConstruction.irreducible_power_add_constant
    (X^3-3*X^2+3*X : ℂ[X]) (by simp) (by norm_num) 6 (by decide)
abbrev CoordinateRing (which : Bool) := AdjoinRoot (equation which)
instance (which : Bool) : IsDomain (CoordinateRing which) :=
  AdjoinRoot.isDomain_of_prime (equation_irreducible which).prime
abbrev FunctionField (which : Bool) := FractionRing (CoordinateRing which)

end SplitCompanionDomain

namespace SplitCompanion
open Polynomial HoldoutConstruction

def remainingCoefficientMap (which : Bool) : ComplexParamRing →+* Polynomial (CoefficientField which) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ (CoefficientField which)))
    ![conicCurve which 2,conicCurve which 3,conicCurve which 4]
lemma remainingCoefficientMap_constant (which : Bool) :
    Polynomial.constantCoeff.comp (remainingCoefficientMap which)=endpointEmbedding which := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [remainingCoefficientMap,endpointEmbedding_C]
  · intro i
    simp only [RingHom.comp_apply,remainingCoefficientMap,MvPolynomial.eval₂Hom_X',
      Polynomial.constantCoeff_apply,endpointEmbedding_X]
    fin_cases i <;> simp [conicCurve_constant]

def targetCoefficientMap (which : Bool) : MvPolynomial (Fin 4) ℂ →+* Polynomial (CoefficientField which) :=
  (Polynomial.eval₂RingHom (remainingCoefficientMap which) (Polynomial.C (4 : CoefficientField which)*X)).comp
    (MvPolynomial.finSuccEquiv ℂ 3).toRingHom
lemma targetCoefficientMap_injective (which : Bool) : Function.Injective (targetCoefficientMap which) := by
  have hi : Function.Injective (Polynomial.constantCoeff.comp (remainingCoefficientMap which)) := by
    rw [remainingCoefficientMap_constant]
    exact endpointEmbedding_injective which
  exact (polynomial_family_injective (remainingCoefficientMap which) hi 4 (by norm_num)).comp
    (MvPolynomial.finSuccEquiv ℂ 3).injective
lemma targetCoefficientMap_C (which : Bool) (c : ℂ) : targetCoefficientMap which (MvPolynomial.C c)=
    Polynomial.C (algebraMap ℂ (CoefficientField which) c) := by
  simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_apply,remainingCoefficientMap]
lemma targetCoefficientMap_X (which : Bool) (i : Fin 4) : targetCoefficientMap which (MvPolynomial.X i)=
    ![conicCurve which 0,conicCurve which 2,conicCurve which 3,conicCurve which 4] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show targetCoefficientMap which (MvPolynomial.X 0)=Polynomial.C (4 : CoefficientField which)*X by
      simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_X_zero]]
    have hc : Polynomial.C (4 : CoefficientField which)=(4 : Polynomial (CoefficientField which)) := map_natCast Polynomial.C 4
    simp [conicCurve_first,hc]
  · change (Polynomial.eval₂RingHom (remainingCoefficientMap which) (Polynomial.C (4 : CoefficientField which)*X))
      (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X j.succ))=_
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ (remainingCoefficientMap which) (Polynomial.C (4 : CoefficientField which)*X)
      (Polynomial.C (MvPolynomial.X j))=_
    rw [Polynomial.eval₂_C]
    simp only [remainingCoefficientMap,MvPolynomial.eval₂Hom_X']
    rw [Matrix.cons_val_succ]

abbrev ConicFunctionField (which : Bool) := CurveFunctionField (CoefficientField which)
noncomputable instance conicFunctionField_complexAlgebra (which : Bool) : Algebra ℂ (ConicFunctionField which) :=
  inferInstanceAs (Algebra ℂ (FractionRing (Polynomial (CoefficientField which))))
noncomputable instance (priority := 2000) conicFunctionField_complexModule (which : Bool) :
    Module ℂ (ConicFunctionField which) := Algebra.toModule
noncomputable instance (priority := 2000) conicFunctionField_complexSMul (which : Bool) :
    SMul ℂ (ConicFunctionField which) := (conicFunctionField_complexModule which).toSMul
noncomputable instance (priority := 2000) conicFunctionField_coefficientModule (which : Bool) :
    Module (CoefficientField which) (ConicFunctionField which) := Algebra.toModule
noncomputable instance (priority := 2000) conicFunctionField_coefficientSMul (which : Bool) :
    SMul (CoefficientField which) (ConicFunctionField which) := (conicFunctionField_coefficientModule which).toSMul
instance conicFunctionField_complexTower (which : Bool) : IsScalarTower ℂ (CoefficientField which) (ConicFunctionField which) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def conicFieldCoordinate (which : Bool) (i : Fin 5) : ConicFunctionField which :=
  algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) (conicCurve which i)
def conicFieldCoefficientMap (which : Bool) : MvPolynomial (Fin 4) ℂ →+* ConicFunctionField which :=
  (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).comp (targetCoefficientMap which)
lemma conicFieldCoefficientMap_injective (which : Bool) : Function.Injective (conicFieldCoefficientMap which) :=
  (IsFractionRing.injective (Polynomial (CoefficientField which)) (ConicFunctionField which)).comp
    (targetCoefficientMap_injective which)
lemma conicFieldCoefficientMap_C (which : Bool) (c : ℂ) :
    conicFieldCoefficientMap which (MvPolynomial.C c)=algebraMap ℂ (ConicFunctionField which) c := by
  rw [conicFieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_C]
  rfl
lemma conicFieldCoefficientMap_X (which : Bool) (i : Fin 4) :
    conicFieldCoefficientMap which (MvPolynomial.X i)=
      ![conicFieldCoordinate which 0,conicFieldCoordinate which 2,conicFieldCoordinate which 3,conicFieldCoordinate which 4] i := by
  simp only [conicFieldCoefficientMap,RingHom.comp_apply,targetCoefficientMap_X]
  fin_cases i <;> rfl
lemma conicField_equation (which : Bool) : H which 0 (conicFieldCoordinate which)=0 := by
  have h := congrArg (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which))
    (conicCurve_equation which)
  rw [map_zero,H_map,map_zero] at h
  exact h
lemma conicField_root (which : Bool) : (SplitCompanionDomain.equation which).eval₂
    (conicFieldCoefficientMap which) (conicFieldCoordinate which 1)=0 := by
  have h := conicField_equation which
  have h5 : algebraMap ℂ (ConicFunctionField which) (5/7 : ℂ)=(5/7 : ConicFunctionField which) := by
    rw [map_div₀]
    congr 1 <;> exact map_natCast _ _
  cases which <;>
    simp only [SplitCompanionDomain.equation,SplitCompanionDomain.lower,
      Bool.false_eq_true,ite_false,ite_true,
      Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,
      map_add,map_mul,map_pow,map_ofNat,conicFieldCoefficientMap_C,conicFieldCoefficientMap_X,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,h5]
  all_goals unfold H first second at h
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,zero_mul,add_zero] at h
  all_goals dsimp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one] at *
  all_goals simp only [Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Polynomial.eval₂_ofNat] at *
  all_goals linear_combination h/7

def conicTargetRingMap (which : Bool) : SplitCompanionDomain.CoordinateRing which →+* ConicFunctionField which :=
  AdjoinRoot.lift (f:=SplitCompanionDomain.equation which) (conicFieldCoefficientMap which)
    (conicFieldCoordinate which 1) (conicField_root which)
lemma conicTargetRingMap_injective (which : Bool) : Function.Injective (conicTargetRingMap which) :=
  monic_root_embedding_injective (SplitCompanionDomain.equation which) (SplitCompanionDomain.equation_monic which)
    (SplitCompanionDomain.equation_irreducible which) (conicFieldCoefficientMap which)
    (conicFieldCoefficientMap_injective which) (conicFieldCoordinate which 1) (conicField_root which)
def conicTargetFieldMap (which : Bool) : SplitCompanionDomain.FunctionField which →+* ConicFunctionField which :=
  IsFractionRing.lift (conicTargetRingMap_injective which)
@[simp] lemma conicTargetFieldMap_ring (which : Bool) (r : SplitCompanionDomain.CoordinateRing which) :
    conicTargetFieldMap which (algebraMap (SplitCompanionDomain.CoordinateRing which) (SplitCompanionDomain.FunctionField which) r)=
      conicTargetRingMap which r := IsFractionRing.lift_algebraMap (conicTargetRingMap_injective which) r
@[simp] lemma conicTargetFieldMap_base (which : Bool) (r : ℂ) :
    conicTargetFieldMap which (algebraMap ℂ (SplitCompanionDomain.FunctionField which) r)=
      algebraMap ℂ (ConicFunctionField which) r := by
  change conicTargetFieldMap which (algebraMap (SplitCompanionDomain.CoordinateRing which) (SplitCompanionDomain.FunctionField which)
    (AdjoinRoot.of (SplitCompanionDomain.equation which) (MvPolynomial.C r)))=_
  rw [conicTargetFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
  rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_C]
noncomputable instance conicFunctionField_targetAlgebra (which : Bool) :
    Algebra (SplitCompanionDomain.FunctionField which) (ConicFunctionField which) := (conicTargetFieldMap which).toAlgebra
instance conicFunctionField_targetTower (which : Bool) :
    IsScalarTower ℂ (SplitCompanionDomain.FunctionField which) (ConicFunctionField which) :=
  IsScalarTower.of_algebraMap_eq (fun r => (conicTargetFieldMap_base which r).symm)
lemma targetFunctionField_trdeg (which : Bool) : Algebra.trdeg ℂ (SplitCompanionDomain.FunctionField which)=4 := by
  apply monic_hypersurface_field_trdeg (SplitCompanionDomain.equation which) (SplitCompanionDomain.equation_monic which)
  exact ne_of_gt ((SplitCompanionDomain.equation_monic which).degree_pos_of_not_isUnit
    (SplitCompanionDomain.equation_irreducible which).not_isUnit)
lemma paramField_trdeg : Algebra.trdeg ℂ ParamField=3 := by
  rw [fractionRing_trdeg]
  simp [MvPolynomial.trdeg_of_isDomain]
instance paramField_essFiniteType : Algebra.EssFiniteType ℂ ParamField := fractionRing_essFiniteType ℂ ComplexParamRing
lemma conicFunctionField_trdeg (which : Bool) : Algebra.trdeg ℂ (ConicFunctionField which)=4 := by
  rw [polynomial_fractionRing_trdeg ℂ ParamField (CoefficientField which),paramField_trdeg]
  norm_num
instance conicFunctionField_essFiniteType (which : Bool) : Algebra.EssFiniteType ℂ (ConicFunctionField which) :=
  polynomial_fractionRing_essFiniteType ℂ ParamField (CoefficientField which)
instance conicFunctionField_finite (which : Bool) :
    Module.Finite (SplitCompanionDomain.FunctionField which) (ConicFunctionField which) := by
  apply finite_of_same_finite_trdeg (K:=ℂ)
  · rw [targetFunctionField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [targetFunctionField_trdeg,conicFunctionField_trdeg]

end SplitCompanion

namespace SplitCompanion
open Polynomial HoldoutConstruction

lemma conicNormal_distinguished_constant_ne_zero (which : Bool) :
    (conicNormal which 1).coeff 0 ≠ 0 := by
  have hp := congrArg (Polynomial.constantCoeff :
    Polynomial (CoefficientField which) →+* CoefficientField which) (conicNormal_pairing which)
  unfold polynomialPairing at hp
  rw [map_sum,map_one] at hp
  simp only [map_mul,Polynomial.constantCoeff_apply] at hp
  have h0 : (conicNormal which 0).coeff 0=0 := by rw [conicNormal_first]; rfl
  have h2 : (conicNormal which 2).coeff 0=0 := conicNormal_endpoint_constant which 0
  have h3 : (conicNormal which 3).coeff 0=0 := conicNormal_endpoint_constant which 1
  have h4 : (conicNormal which 4).coeff 0=0 := conicNormal_endpoint_constant which 2
  simp only [Fin.sum_univ_succ] at hp
  simp only [h0,h2,h3,h4,mul_zero,zero_add,add_zero,Fin.sum_univ_zero] at hp
  change (conicGradient which 1).coeff 0*(conicNormal which 1).coeff 0+
    ((conicGradient which 2).coeff 0*(conicNormal which 2).coeff 0+
      ((conicGradient which 3).coeff 0*(conicNormal which 3).coeff 0+
        (conicGradient which 4).coeff 0*(conicNormal which 4).coeff 0))=1 at hp
  simp only [h2,h3,h4,mul_zero,add_zero] at hp
  intro hz
  rw [hz,mul_zero] at hp
  exact zero_ne_one hp

#print axioms conicCurve_equation
#print axioms conicNormal_pairing
#print axioms conicTargetRingMap_injective
#print axioms conicFunctionField_finite

end SplitCompanion
