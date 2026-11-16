import Proposal.JacobianNormal
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace

/-! Polynomial residue exactness on the mixed-polar Jacobian, via the checked
conic, polynomial integration, and normalized finite trace. This specializes
fqlx's shared polynomial-family bridge and finite-trace theorems; the physical
certificate is assembled separately in PhysicalPrimitive. Adapted from the
accepted constructions of fqlx and hodgepodgeconjecture. Prepared for
benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace MixedPolarJacobianResidue
open HoldoutConstruction MixedPolarJacobianFamily MixedPolarJacobianParameters MixedPolarJacobianEmbedding
  MixedPolarJacobianHypersurface MixedPolarJacobianNormal Polynomial
open scoped BigOperators
local instance : Algebra ℤ CoefficientField := Ring.toIntAlgebra _
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ TargetField := Ring.toIntAlgebra _
instance targetField_charZero : CharZero TargetField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ TargetField) (algebraMap ℂ TargetField).injective

def fieldEval : Ambient →+* FunctionField :=
  (algebraMap (Polynomial CoefficientField) FunctionField).comp polynomialEval
lemma fieldEval_X (i : Fin 6) : fieldEval (MvPolynomial.X i)=fieldCoordinate i := by
  simp [fieldEval,polynomialEval_X,fieldCoordinate]
lemma fieldEval_C (z : ℂ) :
    fieldEval (MvPolynomial.C z)=algebraMap CoefficientField FunctionField (constantMap z) := by
  simp only [fieldEval,RingHom.comp_apply,polynomialEval_C]
  rfl
lemma finite_evaluation (p : Ambient) :
    finiteQuotientEvaluation (K := TargetField) (L := FunctionField) projection p=fieldEval p := by
  have h : finiteQuotientEvaluation (K := TargetField) (L := FunctionField) projection=fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro z
      change targetFieldMap (residueMap (MvPolynomial.C z))=_
      rw [residueMap_C,targetFieldMap_complex,fieldEval_C]
      rfl
    · intro i
      change targetFieldMap (algebraMap TargetRing TargetField (projection (MvPolynomial.X i)))=_
      rw [targetFieldMap_ring,fieldEval_X]
      refine Fin.cases ?_ (fun j => ?_) i
      · change AdjoinRoot.lift _ _ _
          (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 0)))=_
        rw [MvPolynomial.finSuccEquiv_X_zero]
        exact AdjoinRoot.lift_root _
      · change AdjoinRoot.lift _ _ _
          (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X j.succ)))=_
        rw [MvPolynomial.finSuccEquiv_X_succ]
        change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (MvPolynomial.X j))=_
        rw [AdjoinRoot.lift_of]
        simp [fieldCoefficientMap,MixedPolarJacobianGeometry.coefficientMap_X,fieldCoordinate]
  exact congrArg (fun f : Ambient →+* FunctionField => f p) h

def sourceDerivation (i : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  extendRingDerivation (P := Polynomial CoefficientField) (L := FunctionField) (polynomialDerivation i)
lemma sourceDerivation_polynomial (i : Fin 5) (p : Polynomial CoefficientField) :
    sourceDerivation i (algebraMap (Polynomial CoefficientField) FunctionField p)=
      algebraMap (Polynomial CoefficientField) FunctionField (polynomialDerivation i p) :=
  extendRingDerivation_apply _ p
lemma sourceDerivations_commute (i j : Fin 5) : Function.Commute (sourceDerivation i) (sourceDerivation j) :=
  extendRingDerivation_commute (L := FunctionField) _ _ (polynomialDerivations_commute i j)
lemma sourceDerivation_base (i : Fin 5) (z : ℂ) :
    sourceDerivation i (algebraMap CoefficientField FunctionField (constantMap z))=0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact curveTimeDerivation_coefficient _
  · change curveCoefficientDerivation (coefficientDerivation j)
      (algebraMap CoefficientField FunctionField (constantMap z))=0
    simp [coefficientDerivation_constant]
lemma sourceDerivation_eval_range (i : Fin 5) (x : FunctionField)
    (hx : x ∈ (Polynomial.eval₂RingHom (algebraMap CoefficientField FunctionField)
      (curveTime (E := CoefficientField))).range) :
    sourceDerivation i x ∈ (Polynomial.eval₂RingHom (algebraMap CoefficientField FunctionField)
      (curveTime (E := CoefficientField))).range := by
  rw [curvePolynomial_eval₂] at hx ⊢
  exact extendRingDerivation_mem_range _ x hx

def targetDerivation (i : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  extendFiniteDerivation (tangent i)
lemma targetDerivation_apply (i : Fin 5) (x : TargetField) :
    targetDerivation i (algebraMap TargetField FunctionField x)=
      algebraMap TargetField FunctionField (tangent i x) := extendFiniteDerivation_apply _ x

def matrix : Matrix (Fin 6) (Fin 6) FunctionField :=
  (algebraMap (Polynomial CoefficientField) FunctionField).mapMatrix evaluationMatrix
lemma matrix_det_ne_zero : matrix.det≠0 := by
  rw [matrix,← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial CoefficientField) FunctionField)).mpr
    evaluationMatrix_det_ne_zero

lemma family_residue_solution (A : Ambient) :
    ∃ w : Fin 5 → FunctionField,
      residueDivergence targetDerivation (fieldEval (MvPolynomial.pderiv 0 hypersurface)) w=
        -(fieldEval (MvPolynomial.pderiv 0 A)/fieldEval (MvPolynomial.pderiv 0 hypersurface)-
          fieldEval A*fieldEval (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface))/
            (fieldEval (MvPolynomial.pderiv 0 hypersurface))^2) := by
  let ρ := finiteQuotientEvaluation (K := TargetField) (L := FunctionField) projection
  let ψ : Fin 6 → FunctionField := fun i =>
    algebraMap (Polynomial CoefficientField) FunctionField (normal i)
  have hf : ρ hypersurface=0 := by
    change algebraMap TargetField FunctionField (residueMap hypersurface)=0
    rw [(residueMap_kernel _).mpr (dvd_refl _),map_zero]
  have hg : ρ (MvPolynomial.pderiv 0 hypersurface)≠0 :=
    (map_ne_zero (algebraMap TargetField FunctionField)).2 normal_ne_zero
  have hE (i : Fin 5) (p : Ambient) : targetDerivation i (ρ p)=
      ρ (MvPolynomial.pderiv i.succ p)-ρ (MvPolynomial.pderiv i.succ hypersurface)/
        ρ (MvPolynomial.pderiv 0 hypersurface)*ρ (MvPolynomial.pderiv 0 p) := by
    change targetDerivation i (algebraMap TargetField FunctionField (residueMap p))=_
    rw [targetDerivation_apply,tangent_apply]
    simp only [map_sub,map_div₀,map_mul]
    rfl
  have hp : (∑ i,ρ (MvPolynomial.pderiv i hypersurface)*ψ i)=1 := by
    have h := congrArg (algebraMap (Polynomial CoefficientField) FunctionField) normal_pairing
    simpa only [map_sum,map_mul,map_one,ρ,ψ,finite_evaluation,fieldEval,RingHom.comp_apply] using h
  suffices h : ∃ w : Fin 5 → FunctionField,
      residueDivergence targetDerivation (ρ (MvPolynomial.pderiv 0 hypersurface)) w=
        -(ρ (MvPolynomial.pderiv 0 A)/ρ (MvPolynomial.pderiv 0 hypersurface)-
          ρ A*ρ (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface))/
            (ρ (MvPolynomial.pderiv 0 hypersurface))^2) by
    simpa only [ρ,finite_evaluation] using h
  apply residue_solution_from_polynomial_curve (K := TargetField)
    projection projection_surjective hypersurface A sourceDerivation targetDerivation matrix ψ
    (algebraMap CoefficientField FunctionField) (curveTime (E := CoefficientField)) 0
  · exact curveTimeDerivation_coefficient
  · exact curveTimeDerivation_time
  · exact hf
  · exact hg
  · exact matrix_det_ne_zero
  · intro i; rfl
  · intro k i
    rw [finite_evaluation,fieldEval_X]
    exact (sourceDerivation_polynomial i (fullCurve k)).symm
  · exact hp
  · intro i z
    rw [finite_evaluation,fieldEval_C]
    exact sourceDerivation_base i z
  · exact sourceDerivations_commute
  · exact hE
  · intro z
    rw [finite_evaluation,fieldEval_C,curvePolynomial_eval₂]
    exact ⟨C (constantMap z),rfl⟩
  · intro i
    rw [finite_evaluation,fieldEval_X,curvePolynomial_eval₂]
    exact ⟨fullCurve i,rfl⟩
  · intro i
    rw [curvePolynomial_eval₂]
    exact ⟨normal i,rfl⟩
  · exact sourceDerivation_eval_range

/-- Every polynomial numerator on the exact Jacobian has a rational residue primitive. -/
theorem target_residue_solution (A : Ambient) :
    ∃ w : Fin 5 → TargetField,
      residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 hypersurface)) w=
        -(residueMap (MvPolynomial.pderiv 0 A)/residueMap (MvPolynomial.pderiv 0 hypersurface)-
          residueMap A*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 hypersurface))/
            (residueMap (MvPolynomial.pderiv 0 hypersurface))^2) := by
  apply residue_solution_descends_finite tangent targetDerivation targetDerivation_apply
  obtain ⟨w,hw⟩ := family_residue_solution A
  refine ⟨w,?_⟩
  simp_rw [← finite_evaluation] at hw
  simp only [map_neg,map_sub,map_div₀,map_mul,map_pow]
  exact hw
#print axioms target_residue_solution
end MixedPolarJacobianResidue
