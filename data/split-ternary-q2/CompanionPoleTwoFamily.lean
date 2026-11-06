import Proposal.CompanionPoleTwo
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HigherResidues.HigherCurve

/-!
The actual finite polynomial curve for the normal-T order [T,x,a,y,S].
It reuses the checked incidence and dominance construction, with rows
permuted into this chart. Prepared with OpenAI Codex assistance for fqlx.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open scoped BigOperators

namespace SplitCompanionPoleTwo
open Polynomial HoldoutConstruction SplitCompanion
local instance (which : Bool) : Algebra ℤ (FunctionField which) := Ring.toIntAlgebra _
local instance (which : Bool) : Algebra ℤ (ConicFunctionField which) := Ring.toIntAlgebra _

/-- New normal-T coordinates to the original natural order [x,a,y,S,T]. -/
def curveIndexT : Equiv.Perm (Fin 5) := permutation.symm.trans SplitCompanionDomain.coordinateSwap

def fieldEvalT (which : Bool) : P5 →+* ConicFunctionField which :=
  (conicTargetFieldMap which).comp (residueMapT which)
lemma fieldEvalT_old (which : Bool) (P : P5) : fieldEvalT which P=
    fieldEval which (MvPolynomial.rename permutation.symm P) := by
  rw [fieldEvalT,RingHom.comp_apply,residueMapT_old,conicTargetFieldMap_residue]
@[simp] lemma fieldEvalT_C (which : Bool) (c : ℂ) :
    fieldEvalT which (MvPolynomial.C c)=algebraMap ℂ (ConicFunctionField which) c := by
  rw [fieldEvalT_old,MvPolynomial.rename_C]
  exact MvPolynomial.eval₂Hom_C _ _ c
lemma fieldEvalT_X (which : Bool) (j : Fin 5) :
    fieldEvalT which (MvPolynomial.X j)=conicFieldCoordinate which (curveIndexT j) := by
  rw [fieldEvalT_old,MvPolynomial.rename_X]
  exact MvPolynomial.eval₂Hom_X' _ _ _
lemma fieldEvalT_rename (which : Bool) (P : P5) :
    fieldEvalT which (MvPolynomial.rename permutation P)=fieldEval which P := by
  rw [fieldEvalT_old,MvPolynomial.rename_rename,permutation.symm_comp_self,MvPolynomial.rename_id_apply]
lemma hypersurfaceT_partial (which : Bool) (j : Fin 5) :
    MvPolynomial.pderiv j (hypersurfaceT which)=MvPolynomial.rename permutation
      (MvPolynomial.pderiv (permutation.symm j) (SplitCompanionDomain.hypersurface which)) := by
  rw [hypersurfaceT]
  convert MvPolynomial.pderiv_rename permutation.injective (permutation.symm j)
    (SplitCompanionDomain.hypersurface which) using 1 <;> simp
lemma fieldEvalT_partial (which : Bool) (j : Fin 5) :
    fieldEvalT which (MvPolynomial.pderiv j (hypersurfaceT which))=
      fieldEval which (MvPolynomial.pderiv (permutation.symm j) (SplitCompanionDomain.hypersurface which)) := by
  rw [hypersurfaceT_partial,fieldEvalT_rename]
lemma fieldEvalT_polynomial (which : Bool) (P : P5) :
    fieldEvalT which P ∈ (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).range := by
  rw [fieldEvalT_old,fieldEval_polynomial]
  exact ⟨_,rfl⟩

def normalFieldT (which : Bool) (j : Fin 5) : ConicFunctionField which :=
  normalField which (permutation.symm j)
def bridgeMatrixT (which : Bool) : Matrix (Fin 5) (Fin 5) (ConicFunctionField which) :=
  (bridgeMatrix which).submatrix permutation.symm id
lemma bridgeMatrixT_det_ne_zero (which : Bool) : (bridgeMatrixT which).det≠0 := by
  rw [bridgeMatrixT,Matrix.det_permute]
  apply mul_ne_zero _ (bridgeMatrix_det_ne_zero which)
  have hs : IsUnit ((Equiv.Perm.sign permutation.symm : ℤ) : ConicFunctionField which) :=
    (Equiv.Perm.sign permutation.symm).isUnit.map (Int.castRingHom (ConicFunctionField which))
  exact hs.ne_zero
lemma normalFieldT_pairing (which : Bool) :
    (∑ j,fieldEvalT which (MvPolynomial.pderiv j (hypersurfaceT which))*normalFieldT which j)=1 := by
  simp only [fieldEvalT_partial,normalFieldT]
  rw [Equiv.sum_comp permutation.symm (fun j =>
    fieldEval which (MvPolynomial.pderiv j (SplitCompanionDomain.hypersurface which))*normalField which j)]
  exact gradient_normal_pairing which
lemma bridgeMatrixT_normal (which : Bool) (j : Fin 5) : bridgeMatrixT which j 0=normalFieldT which j := rfl
lemma bridgeMatrixT_coordinate (which : Bool) (j : Fin 5) (i : Fin 4) :
    bridgeMatrixT which j i.succ=sourceDerivation which i (fieldEvalT which (MvPolynomial.X j)) := by
  rw [fieldEvalT_X]
  exact (sourceDerivation_polynomial which i (conicCurve which (curveIndexT j))).symm
lemma normalFieldT_polynomial (which : Bool) (j : Fin 5) : normalFieldT which j ∈
    (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).range := ⟨_,rfl⟩
lemma bridgeMatrixT_polynomial (which : Bool) (j k : Fin 5) : bridgeMatrixT which j k ∈
    (algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which)).range := by
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [bridgeMatrixT_normal]; exact normalFieldT_polynomial which j
  · rw [bridgeMatrixT_coordinate,fieldEvalT_X]
    exact ⟨_,(sourceDerivation_polynomial which i (conicCurve which (curveIndexT j))).symm⟩

lemma tangentT_commute (which : Bool) (i j : Fin 4) :
    Function.Commute (tangentT which i) (tangentT which j) :=
  residueTangent_commute (K:=FunctionField which) (projectionT which) (projectionT_surjective which)
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) (hypersurfaceT which)
    (projectionT_kernel which) (normal_ne_zero which)
    (integerPartials_commute i.succ 0) (integerPartials_commute j.succ 0)
    (integerPartials_commute i.succ j.succ)
def targetDerivationT (which : Bool) (i : Fin 4) :
    Derivation ℤ (ConicFunctionField which) (ConicFunctionField which) :=
  extendFiniteDerivation (L:=ConicFunctionField which) (tangentT which i)
lemma targetDerivationT_apply (which : Bool) (i : Fin 4) (a : FunctionField which) :
    targetDerivationT which i (algebraMap (FunctionField which) (ConicFunctionField which) a)=
      algebraMap (FunctionField which) (ConicFunctionField which) (tangentT which i a) :=
  extendFiniteDerivation_apply _ a
lemma targetDerivationT_commute (which : Bool) (i j : Fin 4) :
    Function.Commute (targetDerivationT which i) (targetDerivationT which j) :=
  extendFiniteDerivation_commute _ _ (tangentT_commute which i j)
lemma targetDerivationT_polynomial (which : Bool) (i : Fin 4) (P : P5) :
    targetDerivationT which i (fieldEvalT which P)=
      fieldEvalT which (MvPolynomial.pderiv i.succ P)-
        fieldEvalT which (MvPolynomial.pderiv i.succ (hypersurfaceT which))/
          fieldEvalT which (MvPolynomial.pderiv 0 (hypersurfaceT which))*fieldEvalT which (MvPolynomial.pderiv 0 P) := by
  change targetDerivationT which i (algebraMap (FunctionField which) (ConicFunctionField which) (residueMapT which P))=_
  rw [targetDerivationT_apply,tangentT_apply]
  simp only [map_sub,map_div₀,map_mul,integerPartial_apply]
  rfl
lemma finiteEvaluationT (which : Bool) (P : P5) :
    finiteQuotientEvaluation (K:=FunctionField which) (L:=ConicFunctionField which)
      (projectionT which) P=fieldEvalT which P := rfl
lemma fieldEvalT_hypersurface (which : Bool) : fieldEvalT which (hypersurfaceT which)=0 := by
  change conicTargetFieldMap which (residueMapT which (hypersurfaceT which))=0
  rw [(residueMapT_kernel which _).mpr (dvd_refl _),map_zero]
lemma fieldEvalT_normal_ne_zero (which : Bool) :
    fieldEvalT which (MvPolynomial.pderiv 0 (hypersurfaceT which))≠0 := by
  change conicTargetFieldMap which (residueMapT which (MvPolynomial.pderiv 0 (hypersurfaceT which)))≠0
  exact (_root_.map_ne_zero _).mpr (normal_ne_zero which)


lemma sourceDerivationT_chain (which : Bool) (i : Fin 4) (P : P5) :
    sourceDerivation which i (fieldEvalT which P)=
      ∑ j,fieldEvalT which (MvPolynomial.pderiv j P)*bridgeMatrixT which j i.succ := by
  have hc (c : ℂ) : sourceDerivation which i (fieldEvalT which (MvPolynomial.C c))=0 := by
    rw [fieldEvalT_C]; exact sourceDerivation_base which i c
  have h := derivation_polynomial_ringHom_chain (sourceDerivation which i) (fieldEvalT which) hc P
  simpa only [bridgeMatrixT_coordinate] using h

def gradientT (which : Bool) (j : Fin 5) : ConicFunctionField which :=
  fieldEvalT which (MvPolynomial.pderiv j (hypersurfaceT which))
def inverseMatrixT (which : Bool) : Matrix (Fin 5) (Fin 5) (ConicFunctionField which) :=
  (bridgeMatrixT which)⁻¹
lemma bridgeMatrixT_mul_inverse (which : Bool) : bridgeMatrixT which*inverseMatrixT which=1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (bridgeMatrixT_det_ne_zero which))
lemma inverseMatrixT_mul_bridge (which : Bool) : inverseMatrixT which*bridgeMatrixT which=1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (bridgeMatrixT_det_ne_zero which))
lemma gradientT_matrix_pairing (which : Bool) (j : Fin 5) :
    (∑ k,gradientT which k*bridgeMatrixT which k j)=if j=0 then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [bridgeMatrixT_normal,ite_true,gradientT]
    exact normalFieldT_pairing which
  · have h := sourceDerivationT_chain which i (hypersurfaceT which)
    rw [fieldEvalT_hypersurface,map_zero] at h
    simpa only [gradientT,Fin.succ_ne_zero,ite_false] using h.symm
lemma inverseMatrixT_normal (which : Bool) (j : Fin 5) : inverseMatrixT which 0 j=gradientT which j :=
  inverse_normal_row (bridgeMatrixT which) (inverseMatrixT which) (gradientT which)
    (bridgeMatrixT_mul_inverse which) (gradientT_matrix_pairing which) j
lemma targetDerivationT_full_chain (which : Bool) (j : Fin 4) (x : ConicFunctionField which) :
    targetDerivationT which j x=∑ i,tangentInverse (inverseMatrixT which) (gradientT which) i j*
      sourceDerivation which i x := by
  apply finite_quotient_tangent_chain (K:=FunctionField which) (projectionT which)
    (projectionT_surjective which) (hypersurfaceT which) (sourceDerivation which) (targetDerivationT which)
    (bridgeMatrixT which) (inverseMatrixT which) (normalFieldT which)
    (bridgeMatrixT_mul_inverse which) (inverseMatrixT_normal which) (bridgeMatrixT_normal which)
    (fun k i => bridgeMatrixT_coordinate which k i) (fieldEvalT_normal_ne_zero which)
    (fun i c => by rw [finiteEvaluationT,fieldEvalT_C]; exact sourceDerivation_base which i c)
    (fun i P => by simpa only [finiteEvaluationT] using targetDerivationT_polynomial which i P) j x
lemma bridgeMatrixT_mixed (which : Bool) (i j k : Fin 4) :
    sourceDerivation which k (bridgeMatrixT which j.succ i.succ)=
      sourceDerivation which i (bridgeMatrixT which j.succ k.succ) := by
  rw [bridgeMatrixT_coordinate,bridgeMatrixT_coordinate]
  exact sourceDerivations_commute which k i _

/-- The numerator whose second normal residue gives the protected first-block source. -/
def poleTwoSource : P5 := 49*MvPolynomial.X 1^4*MvPolynomial.X 2^3*MvPolynomial.X 4*MvPolynomial.X 0


/-- Degree-five rational q1 source, with its denominator kept explicit. -/
def rationalNumerator : P5 := -7*MvPolynomial.X 1^4*MvPolynomial.X 2^3*MvPolynomial.X 4
def rationalDenominator : P5 := 6*MvPolynomial.X 0^2
lemma poleTwoSource_partial : integerPartial 0 poleTwoSource=
    49*MvPolynomial.X 1^4*MvPolynomial.X 2^3*MvPolynomial.X 4 := by
  have h49 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (49 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 49
  simp [poleTwoSource,integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h49]
lemma poleTwoSource_second : integerPartial 0 (integerPartial 0 poleTwoSource)=0 := by
  rw [poleTwoSource_partial]
  have h49 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (49 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 49
  simp [integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h49]
lemma rationalNumerator_partial : integerPartial 0 rationalNumerator=0 := by
  have h7 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (7 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 7
  simp [rationalNumerator,integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h7]
lemma rationalDenominator_partial : integerPartial 0 rationalDenominator=12*MvPolynomial.X 0 := by
  have h6 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (6 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 6
  simp [rationalDenominator,integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h6]
  ring
lemma hypersurfaceT_second (which : Bool) : integerPartial 0 (integerPartial 0 (hypersurfaceT which))=
    42*MvPolynomial.X 0 := by
  rw [normal_polynomial]
  have h21 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (21 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 21
  simp [integerPartial_apply,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h21]
  ring
lemma hypersurfaceT_third (which : Bool) :
    integerPartial 0 (integerPartial 0 (integerPartial 0 (hypersurfaceT which)))=42 := by
  rw [hypersurfaceT_second]
  have h42 : MvPolynomial.pderiv (R:=ℂ) (0 : Fin 5) (42 : P5)=0 := (MvPolynomial.pderiv 0).map_natCast 42
  simp [integerPartial_apply,Derivation.leibniz,smul_eq_mul,h42]
lemma rationalDenominator_ne_zero (which : Bool) : residueMapT which rationalDenominator≠0 := by
  rw [rationalDenominator,map_mul,map_pow,map_ofNat]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (T_ne_zero which))

/-- Exact conversion from the polynomial q2 numerator to the rational q1
normal source. This uses actual ambient polynomial derivatives throughout. -/
theorem poleTwo_source_binding (which : Bool) :
    SplitHigherResidue.normalSourceTwo
      (residueMapT which poleTwoSource)
      (residueMapT which (integerPartial 0 poleTwoSource))
      (residueMapT which (integerPartial 0 (integerPartial 0 poleTwoSource)))
      (residueMapT which (integerPartial 0 (hypersurfaceT which)))
      (residueMapT which (integerPartial 0 (integerPartial 0 (hypersurfaceT which))))
      (residueMapT which (integerPartial 0 (integerPartial 0 (integerPartial 0 (hypersurfaceT which))))) =
    residueMapT which (integerPartial 0 rationalNumerator)/
        (residueMapT which rationalDenominator*residueMapT which (integerPartial 0 (hypersurfaceT which)))-
      residueMapT which rationalNumerator*residueMapT which (integerPartial 0 rationalDenominator)/
        ((residueMapT which rationalDenominator)^2*residueMapT which (integerPartial 0 (hypersurfaceT which)))-
      residueMapT which rationalNumerator*residueMapT which
          (integerPartial 0 (integerPartial 0 (hypersurfaceT which)))/
        (residueMapT which rationalDenominator*(residueMapT which (integerPartial 0 (hypersurfaceT which)))^2) := by
  rw [poleTwoSource_second,poleTwoSource_partial,rationalNumerator_partial,
    rationalDenominator_partial,hypersurfaceT_third,hypersurfaceT_second,normal_polynomial]
  simp only [SplitHigherResidue.normalSourceTwo,poleTwoSource,rationalNumerator,rationalDenominator,
    map_mul,map_pow,map_neg,map_zero,map_ofNat]
  field_simp [T_ne_zero which]
  ring


/-- The second normal residue evaluated on the actual companion function field. -/
def secondResidueT (which : Bool) (A : P5) : FunctionField which :=
  SplitHigherResidue.normalSourceTwo
    (residueMapT which A) (residueMapT which (integerPartial 0 A))
    (residueMapT which (integerPartial 0 (integerPartial 0 A)))
    (residueMapT which (integerPartial 0 (hypersurfaceT which)))
    (residueMapT which (integerPartial 0 (integerPartial 0 (hypersurfaceT which))))
    (residueMapT which (integerPartial 0 (integerPartial 0 (integerPartial 0 (hypersurfaceT which)))))
def secondResidueFamilyT (which : Bool) (A : P5) : ConicFunctionField which :=
  SplitHigherResidue.normalSourceTwo
    (fieldEvalT which A) (fieldEvalT which (integerPartial 0 A))
    (fieldEvalT which (integerPartial 0 (integerPartial 0 A)))
    (fieldEvalT which (integerPartial 0 (hypersurfaceT which)))
    (fieldEvalT which (integerPartial 0 (integerPartial 0 (hypersurfaceT which))))
    (fieldEvalT which (integerPartial 0 (integerPartial 0 (integerPartial 0 (hypersurfaceT which)))))
lemma secondResidueT_map (which : Bool) (A : P5) :
    conicTargetFieldMap which (secondResidueT which A)=secondResidueFamilyT which A := by
  simp only [secondResidueT,secondResidueFamilyT,SplitHigherResidue.normalSourceTwo,
    map_mul,map_sub,map_add,map_div₀,map_pow,map_one,map_ofNat]
  rfl
lemma second_residue_descends (which : Bool) (A : P5)
    (hfamily : ∃ w : Fin 4 → ConicFunctionField which,
      residueDivergence (targetDerivationT which)
        (fieldEvalT which (integerPartial 0 (hypersurfaceT which))) w= -secondResidueFamilyT which A) :
    ∃ w : Fin 4 → FunctionField which,
      residueDivergence (tangentT which)
        (residueMapT which (integerPartial 0 (hypersurfaceT which))) w= -secondResidueT which A := by
  apply residue_solution_descends_finite (tangentT which) (targetDerivationT which) (targetDerivationT_apply which)
  obtain ⟨w,hw⟩ := hfamily
  refine ⟨w,?_⟩
  change residueDivergence (targetDerivationT which)
    (fieldEvalT which (integerPartial 0 (hypersurfaceT which))) w=
      conicTargetFieldMap which (-secondResidueT which A)
  rw [map_neg,secondResidueT_map]
  exact hw

/-- The polynomial curve and finite trace give an actual second-normal
residue primitive on each fixed companion. -/
theorem companion_pole_two_residue_solution (which : Bool) (A : P5) :
    ∃ w : Fin 4 → FunctionField which,
      residueDivergence (tangentT which)
        (residueMapT which (integerPartial 0 (hypersurfaceT which))) w= -secondResidueT which A := by
  apply second_residue_descends which A
  let χ := algebraMap (CoefficientField which) (ConicFunctionField which)
  have heval : Polynomial.eval₂RingHom χ (curveTime (E:=CoefficientField which))=
      algebraMap (Polynomial (CoefficientField which)) (ConicFunctionField which) := curvePolynomial_eval₂
  apply SplitHigherResidue.residue_solution_from_polynomial_curve_two
    (fieldEvalT which) (hypersurfaceT which) A (sourceDerivation which) (targetDerivationT which)
    (bridgeMatrixT which) (inverseMatrixT which) (normalFieldT which) χ (curveTime (E:=CoefficientField which)) 0
  · intro a; exact curveTimeDerivation_coefficient a
  · exact curveTimeDerivation_time
  · exact fieldEvalT_normal_ne_zero which
  · exact bridgeMatrixT_det_ne_zero which
  · exact bridgeMatrixT_mul_inverse which
  · exact inverseMatrixT_mul_bridge which
  · exact bridgeMatrixT_normal which
  · exact normalFieldT_pairing which
  · exact fieldEvalT_hypersurface which
  · exact sourceDerivationT_chain which
  · exact targetDerivationT_polynomial which
  · exact targetDerivationT_full_chain which
  · exact bridgeMatrixT_mixed which
  · exact targetDerivationT_commute which
  · intro i j; rw [heval]; exact bridgeMatrixT_polynomial which i j
  · intro i; rw [heval]; exact normalFieldT_polynomial which i
  · intro B; rw [heval]; exact fieldEvalT_polynomial which B
  · intro i j
    rw [heval]
    exact extendRingDerivation_mem_range (polynomialDerivation which i) _ (normalFieldT_polynomial which j)

/-- The resulting cone primitive has exactly the quotient source needed
for the rational affine/elliptic construction. -/
theorem rational_source_residue_solution (which : Bool) :
    ∃ w : Fin 4 → FunctionField which,
      residueDivergence (tangentT which)
        (residueMapT which (integerPartial 0 (hypersurfaceT which))) w=
      -(residueMapT which (integerPartial 0 rationalNumerator)/
          (residueMapT which rationalDenominator*residueMapT which (integerPartial 0 (hypersurfaceT which)))-
        residueMapT which rationalNumerator*residueMapT which (integerPartial 0 rationalDenominator)/
          ((residueMapT which rationalDenominator)^2*residueMapT which (integerPartial 0 (hypersurfaceT which)))-
        residueMapT which rationalNumerator*residueMapT which
            (integerPartial 0 (integerPartial 0 (hypersurfaceT which)))/
          (residueMapT which rationalDenominator*(residueMapT which (integerPartial 0 (hypersurfaceT which)))^2)) := by
  obtain ⟨w,hw⟩ := companion_pole_two_residue_solution which poleTwoSource
  refine ⟨w,?_⟩
  rw [secondResidueT,poleTwo_source_binding] at hw
  exact hw

#print axioms companion_pole_two_residue_solution
#print axioms rational_source_residue_solution

#print axioms targetDerivationT_commute
#print axioms targetDerivationT_full_chain
#print axioms poleTwo_source_binding
#print axioms second_residue_descends
end SplitCompanionPoleTwo
