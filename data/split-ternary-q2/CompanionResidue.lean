import Proposal.CompanionGeometry
import HodgeComputer.Constructions.EllipticCompanions.CompanionAlgebra

/-!
Finite polynomial-curve residue primitives for the exact split companions.
This target-specific application adapts the accepted crossed-ternary construction
of 1337isnot1337 to the two companion equations proved here. Generic finite
trace, curve integration, derivations and normal algebra are imported from the
maintained constructions, with their original attribution to fqlx, HeadOfNaps,
the Sextics contributors, Lean and mathlib. Prepared with Codex assistance for fqlx.
-/
noncomputable section
open scoped BigOperators

namespace SplitCompanionDomain
open Polynomial HoldoutConstruction

def coordinateSwap : Equiv.Perm (Fin 5) := Equiv.swap 0 1

def hypersurface (which : Bool) : MvPolynomial (Fin 5) ℂ :=
  SplitCompanion.H which 0 ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,
    MvPolynomial.X 3,MvPolynomial.X 4]

lemma scalar_five_seven : C (MvPolynomial.C (5/7 : ℂ))*(7 : Polynomial Coeff)=5 := by
  let φ : ℂ →+* Polynomial Coeff := Polynomial.C.comp MvPolynomial.C
  change φ (5/7)*7=5
  rw [← show φ 7=(7 : Polynomial Coeff) from map_natCast φ 7,← map_mul]
  norm_num
  exact map_natCast φ 5

lemma independent_vector : (Fin.cases (Polynomial.X : Polynomial Coeff)
    (fun j => C (MvPolynomial.X j)))=
    ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),C (MvPolynomial.X 3)] := by
  funext i
  fin_cases i <;> rfl

lemma hypersurface_univariate (which : Bool) :
    MvPolynomial.finSuccEquiv ℂ 4 (hypersurface which)=7*equation which := by
  cases which <;> simp [hypersurface,SplitCompanion.H,SplitCompanion.first,SplitCompanion.second,
    equation,lower,MvPolynomial.finSuccEquiv_apply,Polynomial.C_ofNat,independent_vector]
  · linear_combination -(2*C (MvPolynomial.X 0)^5*X+
      2*C (MvPolynomial.X 0)^3*C (MvPolynomial.X 1)^2*X+
      C (MvPolynomial.X 0)*C (MvPolynomial.X 1)^5+3*C (MvPolynomial.X 1)*X^5)*scalar_five_seven
  · linear_combination -(C (MvPolynomial.X 0)^5*X+
      C (MvPolynomial.X 0)^2*C (MvPolynomial.X 1)*X^3+
      3*C (MvPolynomial.X 0)*C (MvPolynomial.X 1)^5+2*C (MvPolynomial.X 1)*X^5)*scalar_five_seven

lemma hypersurface_partial (which : Bool) (j : Fin 5) : integerPartial j (hypersurface which)=
    SplitCompanion.gradient which 0
      ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]
      (coordinateSwap j) := by
  have h (z : Fin 5 → MvPolynomial (Fin 5) ℂ) : integerPartial j (SplitCompanion.H which 0 z)=
      ∑ i,SplitCompanion.gradient which 0 z i*integerPartial j (z i) :=
    SplitCompanion.H_derivation (integerPartial j) which 0 (map_zero _) z
  rw [hypersurface,h]
  fin_cases j <;>
    simp [SplitCompanion.gradient,Fin.sum_univ_succ,coordinateSwap,Equiv.swap_apply_def,integerPartial_X_of_ne]

abbrev projection (which : Bool) := CrossedMonicHypersurface.projection (equation which)
lemma projection_surjective (which : Bool) : Function.Surjective (projection which) :=
  CrossedMonicHypersurface.projection_surjective _
lemma seven_unit : IsUnit (7 : Polynomial Coeff) := by
  have h : IsUnit (7 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
  exact (h.map (MvPolynomial.C : ℂ →+* Coeff)).map (Polynomial.C : Coeff →+* Polynomial Coeff)
lemma projection_kernel (which : Bool) (p : MvPolynomial (Fin 5) ℂ) :
    projection which p=0 ↔ hypersurface which ∣ p := by
  change AdjoinRoot.mk (equation which) (MvPolynomial.finSuccEquiv ℂ 4 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero]
  rw [← map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 4),hypersurface_univariate]
  exact (seven_unit.mul_left_dvd).symm
abbrev residueMap (which : Bool) := CrossedMonicHypersurface.residueMap (equation which)
lemma residueMap_kernel (which : Bool) (p : MvPolynomial (Fin 5) ℂ) :
    residueMap which p=0 ↔ hypersurface which ∣ p :=
  residue_fractionMap_kernel (projection which) (hypersurface which) (projection_kernel which) p

lemma hypersurface_normal_univariate (which : Bool) :
    MvPolynomial.finSuccEquiv ℂ 4 (integerPartial 0 (hypersurface which))=7*(equation which).derivative := by
  rw [← CrossedMonicHypersurface.derivative_finSuccEquiv,hypersurface_univariate]
  simp
lemma normal_ne_zero (which : Bool) : residueMap which (integerPartial 0 (hypersurface which))≠0 := by
  have hp : (equation which).natDegree≠0 := by
    intro h
    have he := (equation_monic which).degree_pos_of_not_isUnit (equation_irreducible which).not_isUnit
    rw [degree_eq_natDegree (equation_monic which).ne_zero,h] at he
    exact (lt_irrefl _ he)
  have hd := AdjoinRoot.mk_ne_zero_of_degree_lt (equation_monic which)
    (Polynomial.derivative_ne_zero.mpr hp) (degree_derivative_lt (equation_monic which).ne_zero)
  change algebraMap (CoordinateRing which) (FunctionField which)
    (AdjoinRoot.mk (equation which) (MvPolynomial.finSuccEquiv ℂ 4 (integerPartial 0 (hypersurface which))))≠0
  rw [hypersurface_normal_univariate,map_mul,map_mul]
  apply mul_ne_zero
  · exact (seven_unit.map (AdjoinRoot.mk (equation which))).map
      (algebraMap (CoordinateRing which) (FunctionField which)) |>.ne_zero
  · simpa only [map_zero] using (IsFractionRing.injective (CoordinateRing which) (FunctionField which)).ne hd

local instance (which : Bool) : Algebra ℤ (FunctionField which) := Ring.toIntAlgebra _
def tangent (which : Bool) (i : Fin 4) : Derivation ℤ (FunctionField which) (FunctionField which) :=
  residueTangent (K:=FunctionField which) (projection which) (projection_surjective which)
    (integerPartial 0) (integerPartial i.succ) (hypersurface which) (projection_kernel which) (normal_ne_zero which)
lemma tangent_apply (which : Bool) (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    tangent which i (residueMap which p)=residueMap which (integerPartial i.succ p)-
      residueMap which (integerPartial i.succ (hypersurface which))/
        residueMap which (integerPartial 0 (hypersurface which))*residueMap which (integerPartial 0 p) :=
  residueTangent_apply (K:=FunctionField which) (projection which) (projection_surjective which)
    (integerPartial 0) (integerPartial i.succ) (hypersurface which) (projection_kernel which) (normal_ne_zero which) p

end SplitCompanionDomain

namespace SplitCompanion
open Polynomial HoldoutConstruction
local instance : Algebra ℤ ParamField := Ring.toIntAlgebra _
local instance (which : Bool) : Algebra ℤ (CoefficientField which) := Ring.toIntAlgebra _
local instance (which : Bool) : Algebra ℤ (ConicFunctionField which) := Ring.toIntAlgebra _

def parameterDerivation (i : Fin 3) : Derivation ℤ ParamField ParamField :=
  extendRingDerivation (P:=ComplexParamRing) (L:=ParamField) (integerPartial (R:=ℂ) i)
@[simp] lemma parameterDerivation_polynomial (i : Fin 3) (p : ComplexParamRing) :
    parameterDerivation i (algebraMap ComplexParamRing ParamField p)=
      algebraMap ComplexParamRing ParamField (integerPartial i p) := extendRingDerivation_apply _ p
lemma parameterDerivations_commute (i j : Fin 3) : Function.Commute (parameterDerivation i) (parameterDerivation j) :=
  extendRingDerivation_commute _ _ (integerPartials_commute i j)
@[simp] lemma parameterDerivation_base (i : Fin 3) (c : ℂ) : parameterDerivation i (algebraMap ℂ ParamField c)=0 := by
  change parameterDerivation i (algebraMap ComplexParamRing ParamField (MvPolynomial.C c))=0
  rw [parameterDerivation_polynomial,integerPartial_C,map_zero]

def endpointDerivation (which : Bool) (i : Fin 3) : Derivation ℤ (CoefficientField which) (CoefficientField which) :=
  extendFiniteDerivation (L:=CoefficientField which) (parameterDerivation i)
lemma endpointDerivation_apply (which : Bool) (i : Fin 3) (a : ParamField) :
    endpointDerivation which i (algebraMap ParamField (CoefficientField which) a)=
      algebraMap ParamField (CoefficientField which) (parameterDerivation i a) := extendFiniteDerivation_apply _ a
lemma endpointDerivations_commute (which : Bool) (i j : Fin 3) :
    Function.Commute (endpointDerivation which i) (endpointDerivation which j) :=
  extendFiniteDerivation_commute _ _ (parameterDerivations_commute i j)
@[simp] lemma endpointDerivation_base (which : Bool) (i : Fin 3) (c : ℂ) :
    endpointDerivation which i (algebraMap ℂ (CoefficientField which) c)=0 := by
  rw [IsScalarTower.algebraMap_apply ℂ ParamField (CoefficientField which),endpointDerivation_apply,parameterDerivation_base,map_zero]
@[simp] lemma endpointDerivation_parameter (which : Bool) (i j : Fin 3) :
    endpointDerivation which i (scalarParameter which j)=if j=i then 1 else 0 := by
  rw [← endpointEmbedding_X]
  change endpointDerivation which i (algebraMap ParamField (CoefficientField which)
    (algebraMap ComplexParamRing ParamField (MvPolynomial.X j)))=_
  rw [endpointDerivation_apply,parameterDerivation_polynomial]
  by_cases h : j=i
  · subst j; simp
  · simp [integerPartial_X_of_ne _ _ h,h]

def polynomialDerivation (which : Bool) : Fin 4 → Derivation ℤ (Polynomial (CoefficientField which)) (Polynomial (CoefficientField which)) :=
  Fin.cases timePolynomialDerivation (fun i => coefficientPolynomialDerivation (endpointDerivation which i))
@[simp] lemma polynomialDerivation_zero (which : Bool) : polynomialDerivation which 0=timePolynomialDerivation := rfl
@[simp] lemma polynomialDerivation_succ (which : Bool) (i : Fin 3) :
    polynomialDerivation which i.succ=coefficientPolynomialDerivation (endpointDerivation which i) := rfl
lemma polynomialDerivations_commute (which : Bool) (i j : Fin 4) :
    Function.Commute (polynomialDerivation which i) (polynomialDerivation which j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro f; rfl
    · exact time_coefficientPolynomialDerivation_commute _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (time_coefficientPolynomialDerivation_commute _).symm
    · exact coefficientPolynomialDerivation_commute _ _ (endpointDerivations_commute which i j)

def sourceDerivation (which : Bool) (i : Fin 4) : Derivation ℤ (ConicFunctionField which) (ConicFunctionField which) :=
  extendRingDerivation (polynomialDerivation which i)
@[simp] lemma sourceDerivation_zero (which : Bool) : sourceDerivation which 0=curveTimeDerivation := rfl
@[simp] lemma sourceDerivation_succ (which : Bool) (i : Fin 3) :
    sourceDerivation which i.succ=curveCoefficientDerivation (endpointDerivation which i) := rfl
@[simp] lemma sourceDerivation_polynomial (which : Bool) (i : Fin 4) (p : Polynomial (CoefficientField which)) :
    sourceDerivation which i (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) p)=
      algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) (polynomialDerivation which i p) :=
  extendRingDerivation_apply _ p
lemma sourceDerivations_commute (which : Bool) (i j : Fin 4) :
    Function.Commute (sourceDerivation which i) (sourceDerivation which j) :=
  extendRingDerivation_commute _ _ (polynomialDerivations_commute which i j)
@[simp] lemma sourceDerivation_base (which : Bool) (i : Fin 4) (c : ℂ) :
    sourceDerivation which i (algebraMap ℂ (ConicFunctionField which) c)=0 := by
  change sourceDerivation which i (algebraMap (CoefficientField which) (ConicFunctionField which)
    (algebraMap ℂ (CoefficientField which) c))=0
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

end SplitCompanion

namespace SplitCompanion
open Polynomial HoldoutConstruction
local instance (which : Bool) : Algebra ℤ (CoefficientField which) := Ring.toIntAlgebra _
local instance (which : Bool) : Algebra ℤ (ConicFunctionField which) := Ring.toIntAlgebra _

lemma gradient_derivation_pairing {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) (which : Bool) (z : Fin 5 → R) (hz : H which 0 z=0) :
    (∑ i,gradient which 0 z i*D (z i))=0 := by
  rw [← H_derivation D which 0 (map_zero _),hz,map_zero]

lemma two_step_evaluation_det {R : Type*} [CommRing R]
    (P : Matrix (Fin 5) (Fin 5) R)
    (h0 : ∀ j,P 0 j=if j=0 then 1 else 0)
    (h11 : P 1 1=4) (h1 : ∀ j : Fin 3,P 1 j.succ.succ=0)
    (he : ∀ i j : Fin 3,P i.succ.succ j.succ.succ=if i=j then 1 else 0) : P.det=4 := by
  rw [det_single_first_row P (by intro j; simp [h0])]
  rw [det_single_first_row (P.submatrix Fin.succ Fin.succ) h1]
  have hi : (P.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ=(1 : Matrix (Fin 3) (Fin 3) R) := by
    funext i j
    exact he i j
  rw [hi,Matrix.det_one,mul_one]
  change P 0 0*P 1 1=4
  rw [h0,ite_eq_left rfl,h11,one_mul]

def polynomialMatrix (which : Bool) : Matrix (Fin 5) (Fin 5) (Polynomial (CoefficientField which)) :=
  fun i => Fin.cases (conicNormal which i) (fun j => polynomialDerivation which j (conicCurve which i))
@[simp] lemma polynomialMatrix_normal (which : Bool) (i : Fin 5) : polynomialMatrix which i 0=conicNormal which i := rfl
@[simp] lemma polynomialMatrix_tangent (which : Bool) (i : Fin 5) (j : Fin 4) :
    polynomialMatrix which i j.succ=polynomialDerivation which j (conicCurve which i) := rfl

def constantMatrix (which : Bool) : Matrix (Fin 5) (Fin 5) (CoefficientField which) :=
  Polynomial.constantCoeff.mapMatrix (polynomialMatrix which)
def independentCoordinate : Fin 4 → Fin 5 := ![0,2,3,4]
def rowMatrix (which : Bool) : Matrix (Fin 5) (Fin 5) (CoefficientField which) :=
  fun i => Fin.cases (fun j => (conicGradient which j).coeff 0)
    (fun k j => if j=independentCoordinate k then 1 else 0) i
lemma rowProduct_first (which : Bool) (j : Fin 5) :
    (rowMatrix which*constantMatrix which) 0 j=if j=0 then 1 else 0 := by
  change (∑ k,(conicGradient which k).coeff 0*(polynomialMatrix which k j).coeff 0)=_
  have hm : (∑ k,(conicGradient which k).coeff 0*(polynomialMatrix which k j).coeff 0)=
      (∑ k,conicGradient which k*polynomialMatrix which k j).coeff 0 := by
    change (∑ k,Polynomial.constantCoeff (conicGradient which k)*Polynomial.constantCoeff (polynomialMatrix which k j))=
      Polynomial.constantCoeff (∑ k,conicGradient which k*polynomialMatrix which k j)
    rw [map_sum]
    simp only [map_mul]
  rw [hm]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [polynomialMatrix_normal,ite_true]
    have h := congrArg (fun p : Polynomial (CoefficientField which) => p.coeff 0) (conicNormal_pairing which)
    simpa only [polynomialPairing,AddMonoidAlgebra.coeff_one_zero] using h
  · simp only [polynomialMatrix_tangent,Fin.succ_ne_zero,ite_false]
    have h := gradient_derivation_pairing (polynomialDerivation which j) which (conicCurve which) (conicCurve_equation which)
    have hc := congrArg (fun p : Polynomial (CoefficientField which) => p.coeff 0) h
    simp only [conicGradient,Polynomial.coeff_zero] at hc ⊢
    exact hc
lemma rowProduct_succ (which : Bool) (i : Fin 4) (j : Fin 5) :
    (rowMatrix which*constantMatrix which) i.succ j=(polynomialMatrix which (independentCoordinate i) j).coeff 0 := by
  simp [Matrix.mul_apply,rowMatrix,constantMatrix]
lemma first_time (which : Bool) : (polynomialDerivation which 0 (conicCurve which 0)).coeff 0=4 := by
  rw [polynomialDerivation_zero,timePolynomialDerivation_apply,conicCurve_first]
  simp
lemma first_parameter (which : Bool) (j : Fin 3) :
    (polynomialDerivation which j.succ (conicCurve which 0)).coeff 0=0 := by
  rw [polynomialDerivation_succ,conicCurve_first]
  have h4 : endpointDerivation which j (4 : CoefficientField which)=0 := (endpointDerivation which j).map_natCast 4
  have hc4 : Polynomial.C (4 : CoefficientField which)=(4 : Polynomial (CoefficientField which)) := map_natCast Polynomial.C 4
  rw [← hc4]
  simp [Derivation.leibniz,h4]
lemma endpoint_parameter (which : Bool) (i j : Fin 3) :
    (polynomialDerivation which j.succ (conicCurve which i.succ.succ)).coeff 0=if i=j then 1 else 0 := by
  rw [polynomialDerivation_succ,coefficientPolynomialDerivation_coeff,conicCurve_constant]
  have hv (T : Type) (a b : T) (v : Fin 3 → T) (k : Fin 3) : ![a,b,v 0,v 1,v 2] k.succ.succ=v k := by
    fin_cases k <;> rfl
  rw [hv (CoefficientField which) 0 (coefficients which 0) (scalarParameter which) i]
  exact endpointDerivation_parameter which j i
lemma rowProduct_det (which : Bool) : (rowMatrix which*constantMatrix which).det=4 := by
  apply two_step_evaluation_det
  · exact rowProduct_first which
  · exact (rowProduct_succ which 0 1).trans (first_time which)
  · intro j
    exact (rowProduct_succ which 0 j.succ.succ).trans (first_parameter which j)
  · intro i j
    rw [rowProduct_succ,polynomialMatrix_tangent]
    have he : independentCoordinate i.succ=i.succ.succ := by fin_cases i <;> rfl
    rw [he]
    exact endpoint_parameter which i j
lemma constantMatrix_det_ne_zero (which : Bool) : (constantMatrix which).det≠0 := by
  intro h
  have hd := rowProduct_det which
  rw [Matrix.det_mul,h,mul_zero] at hd
  exact (by norm_num : (0 : CoefficientField which)≠4) hd
lemma polynomialMatrix_det_ne_zero (which : Bool) : (polynomialMatrix which).det≠0 := by
  intro h
  apply constantMatrix_det_ne_zero which
  change (Polynomial.constantCoeff.mapMatrix (polynomialMatrix which)).det=0
  rw [← RingHom.map_det,h,map_zero]
def evaluationMatrix (which : Bool) : Matrix (Fin 5) (Fin 5) (ConicFunctionField which) :=
  (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).mapMatrix (polynomialMatrix which)
lemma evaluationMatrix_det_ne_zero (which : Bool) : (evaluationMatrix which).det≠0 := by
  rw [evaluationMatrix,← RingHom.map_det]
  simpa only [map_zero] using (IsFractionRing.injective (Polynomial (CoefficientField which)) (ConicFunctionField which)).ne
    (polynomialMatrix_det_ne_zero which)

end SplitCompanion

namespace SplitCompanion
open Polynomial HoldoutConstruction
open SplitCompanionDomain (coordinateSwap)
local instance (which : Bool) : Algebra ℤ (SplitCompanionDomain.FunctionField which) := Ring.toIntAlgebra _
local instance (which : Bool) : Algebra ℤ (ConicFunctionField which) := Ring.toIntAlgebra _
instance companion_charZero (which : Bool) : CharZero (SplitCompanionDomain.FunctionField which) :=
  charZero_of_injective_ringHom (f:=algebraMap ℂ (SplitCompanionDomain.FunctionField which))
    (algebraMap ℂ (SplitCompanionDomain.FunctionField which)).injective

def fieldEval (which : Bool) : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField which :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (ConicFunctionField which))
    (fun i => conicFieldCoordinate which (coordinateSwap i))
lemma conicTargetFieldMap_coordinate (which : Bool) (i : Fin 5) :
    conicTargetFieldMap which (SplitCompanionDomain.residueMap which (MvPolynomial.X i))=
      conicFieldCoordinate which (coordinateSwap i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [CrossedMonicHypersurface.residueMap_X_zero,conicTargetFieldMap_ring]
    exact AdjoinRoot.lift_root (conicField_root which)
  · rw [CrossedMonicHypersurface.residueMap_X_succ,conicTargetFieldMap_ring]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
    rw [AdjoinRoot.lift_of,conicFieldCoefficientMap_X]
    fin_cases j <;> rfl
lemma conicTargetFieldMap_residue (which : Bool) (p : MvPolynomial (Fin 5) ℂ) :
    conicTargetFieldMap which (SplitCompanionDomain.residueMap which p)=fieldEval which p := by
  have h : (conicTargetFieldMap which).comp (SplitCompanionDomain.residueMap which)=fieldEval which := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,CrossedMonicHypersurface.residueMap_C,conicTargetFieldMap_base,
        fieldEval,MvPolynomial.eval₂Hom_C]
    · intro i
      simp only [RingHom.comp_apply,conicTargetFieldMap_coordinate,fieldEval,MvPolynomial.eval₂Hom_X']
  exact congrArg (fun φ : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField which => φ p) h
lemma fieldEval_polynomial (which : Bool) (p : MvPolynomial (Fin 5) ℂ) :
    fieldEval which p=algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)
      (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ (CoefficientField which)))
        (fun i => conicCurve which (coordinateSwap i)) p) := by
  have h : (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ (CoefficientField which)))
        (fun i => conicCurve which (coordinateSwap i)))=fieldEval which := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C,fieldEval]
      rfl
    · intro i
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',fieldEval,conicFieldCoordinate]
  exact (congrArg (fun φ : MvPolynomial (Fin 5) ℂ →+* ConicFunctionField which => φ p) h).symm
lemma gradient_evaluation (which : Bool) (j : Fin 5) :
    fieldEval which (MvPolynomial.pderiv j (SplitCompanionDomain.hypersurface which))=
      algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)
        (conicGradient which (coordinateSwap j)) := by
  change fieldEval which (integerPartial j (SplitCompanionDomain.hypersurface which))=_
  rw [SplitCompanionDomain.hypersurface_partial]
  have h := gradient_map (fieldEval which) which 0
    ![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] (coordinateSwap j)
  rw [h,map_zero]
  have hv : (fun i => fieldEval which
      (![MvPolynomial.X 1,MvPolynomial.X 0,MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4] i))=
      conicFieldCoordinate which := by
    funext i
    fin_cases i <;> simp [fieldEval,coordinateSwap,Equiv.swap_apply_def]
  rw [hv]
  have he := (gradient_map (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which))
    which 0 (conicCurve which) (coordinateSwap j)).symm
  convert he using 1 <;> (try simp only [map_zero]) <;> rfl

def normalField (which : Bool) (j : Fin 5) : ConicFunctionField which :=
  algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) (conicNormal which (coordinateSwap j))
def bridgeMatrix (which : Bool) : Matrix (Fin 5) (Fin 5) (ConicFunctionField which) :=
  (evaluationMatrix which).submatrix coordinateSwap id
lemma bridgeMatrix_det_ne_zero (which : Bool) : (bridgeMatrix which).det≠0 := by
  rw [bridgeMatrix,Matrix.det_permute]
  apply mul_ne_zero _ (evaluationMatrix_det_ne_zero which)
  simp [coordinateSwap,Equiv.Perm.sign_swap,show (0 : Fin 5)≠1 by decide]
lemma gradient_normal_pairing (which : Bool) :
    (∑ j,fieldEval which (MvPolynomial.pderiv j (SplitCompanionDomain.hypersurface which))*normalField which j)=1 := by
  have h := conicNormal_pairing which
  change (∑ j,conicGradient which j*conicNormal which j)=1 at h
  have he : (∑ j,conicGradient which (coordinateSwap j)*conicNormal which (coordinateSwap j))=
      ∑ j,conicGradient which j*conicNormal which j :=
    Equiv.sum_comp coordinateSwap (fun j => conicGradient which j*conicNormal which j)
  rw [← he] at h
  simp only [Fin.sum_univ_five] at h ⊢
  simp only [gradient_evaluation,normalField,← RingHom.map_mul,← RingHom.map_add]
  rw [h,RingHom.map_one]

def targetDerivation (which : Bool) (j : Fin 4) : Derivation ℤ (ConicFunctionField which) (ConicFunctionField which) :=
  extendFiniteDerivation (L:=ConicFunctionField which) (SplitCompanionDomain.tangent which j)
lemma targetDerivation_apply (which : Bool) (j : Fin 4) (a : SplitCompanionDomain.FunctionField which) :
    targetDerivation which j (algebraMap (SplitCompanionDomain.FunctionField which) (ConicFunctionField which) a)=
      algebraMap (SplitCompanionDomain.FunctionField which) (ConicFunctionField which) (SplitCompanionDomain.tangent which j a) :=
  extendFiniteDerivation_apply _ a
lemma finiteEvaluation (which : Bool) (p : MvPolynomial (Fin 5) ℂ) :
    finiteQuotientEvaluation (K:=SplitCompanionDomain.FunctionField which) (L:=ConicFunctionField which)
      (SplitCompanionDomain.projection which) p=fieldEval which p := conicTargetFieldMap_residue which p

theorem companion_residue_solution (which : Bool) (A : MvPolynomial (Fin 5) ℂ) :
    ∃ w : Fin 4 → SplitCompanionDomain.FunctionField which,
      residueDivergence (SplitCompanionDomain.tangent which)
        (SplitCompanionDomain.residueMap which (MvPolynomial.pderiv 0 (SplitCompanionDomain.hypersurface which))) w=
      -(SplitCompanionDomain.residueMap which (MvPolynomial.pderiv 0 A)/
          SplitCompanionDomain.residueMap which (MvPolynomial.pderiv 0 (SplitCompanionDomain.hypersurface which))-
        SplitCompanionDomain.residueMap which A*SplitCompanionDomain.residueMap which
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (SplitCompanionDomain.hypersurface which)))/
          (SplitCompanionDomain.residueMap which (MvPolynomial.pderiv 0 (SplitCompanionDomain.hypersurface which)))^2) := by
  let π := SplitCompanionDomain.projection which
  let f := SplitCompanionDomain.hypersurface which
  let ρ := finiteQuotientEvaluation (K:=SplitCompanionDomain.FunctionField which) (L:=ConicFunctionField which) π
  let χ := algebraMap (CoefficientField which) (ConicFunctionField which)
  have heval : Polynomial.eval₂RingHom χ (curveTime (E:=CoefficientField which))=
      algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) := curvePolynomial_eval₂
  have hρ (p : MvPolynomial (Fin 5) ℂ) : ρ p=fieldEval which p := finiteEvaluation which p
  have hρC (c : ℂ) : ρ (MvPolynomial.C c)=algebraMap ℂ (ConicFunctionField which) c := by
    rw [hρ]
    exact MvPolynomial.eval₂Hom_C _ _ c
  have hρX (i : Fin 5) : ρ (MvPolynomial.X i)=conicFieldCoordinate which (coordinateSwap i) := by
    rw [hρ]
    exact MvPolynomial.eval₂Hom_X' _ _ i
  have hf : ρ f=0 := by
    change algebraMap (SplitCompanionDomain.FunctionField which) (ConicFunctionField which)
      (SplitCompanionDomain.residueMap which f)=0
    rw [(SplitCompanionDomain.residueMap_kernel which f).mpr (dvd_refl _),map_zero]
  have hg : ρ (MvPolynomial.pderiv 0 f)≠0 := by
    change algebraMap (SplitCompanionDomain.FunctionField which) (ConicFunctionField which)
      (SplitCompanionDomain.residueMap which (integerPartial 0 f))≠0
    exact (_root_.map_ne_zero _).mpr (SplitCompanionDomain.normal_ne_zero which)
  have hE (j : Fin 4) (p : MvPolynomial (Fin 5) ℂ) : targetDerivation which j (ρ p)=
      ρ (MvPolynomial.pderiv j.succ p)-ρ (MvPolynomial.pderiv j.succ f)/
        ρ (MvPolynomial.pderiv 0 f)*ρ (MvPolynomial.pderiv 0 p) := by
    change targetDerivation which j (algebraMap (SplitCompanionDomain.FunctionField which) (ConicFunctionField which)
      (SplitCompanionDomain.residueMap which p))=_
    rw [targetDerivation_apply,SplitCompanionDomain.tangent_apply]
    simp only [map_sub,map_div₀,map_mul,integerPartial_apply]
    rfl
  have hfamily : ∃ w : Fin 4 → ConicFunctionField which,
      residueDivergence (targetDerivation which) (ρ (MvPolynomial.pderiv 0 f)) w=
        -(ρ (MvPolynomial.pderiv 0 A)/ρ (MvPolynomial.pderiv 0 f)-
          ρ A*ρ (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 f))/(ρ (MvPolynomial.pderiv 0 f))^2) := by
    apply residue_solution_from_polynomial_curve (K:=SplitCompanionDomain.FunctionField which)
      π (SplitCompanionDomain.projection_surjective which) f A (sourceDerivation which) (targetDerivation which)
      (bridgeMatrix which) (normalField which) χ (curveTime (E:=CoefficientField which)) 0
    · intro a
      exact curveTimeDerivation_coefficient a
    · exact curveTimeDerivation_time
    · exact hf
    · exact hg
    · exact bridgeMatrix_det_ne_zero which
    · intro j; rfl
    · intro k i
      rw [hρX]
      exact (sourceDerivation_polynomial which i (conicCurve which (coordinateSwap k))).symm
    · change (∑ j,ρ (MvPolynomial.pderiv j f)*normalField which j)=1
      simp_rw [hρ]
      exact gradient_normal_pairing which
    · intro i c
      rw [hρC]
      exact sourceDerivation_base which i c
    · exact sourceDerivations_commute which
    · exact hE
    · intro c
      rw [hρC,heval]
      exact ⟨C (algebraMap ℂ (CoefficientField which) c),rfl⟩
    · intro i
      rw [hρX,heval]
      exact ⟨conicCurve which (coordinateSwap i),rfl⟩
    · intro i
      rw [heval]
      exact ⟨conicNormal which (coordinateSwap i),rfl⟩
    · intro i x hx
      rw [heval] at hx ⊢
      exact extendRingDerivation_mem_range (polynomialDerivation which i) x hx
  apply residue_solution_descends_finite (SplitCompanionDomain.tangent which) (targetDerivation which) (targetDerivation_apply which)
  obtain ⟨w,hw⟩ := hfamily
  refine ⟨w,?_⟩
  rw [map_neg,map_sub,map_div₀,map_div₀,map_mul,map_pow]
  exact hw

#print axioms companion_residue_solution

end SplitCompanion
