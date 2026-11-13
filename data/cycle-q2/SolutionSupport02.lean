import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport01

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicStandard.lean -/
section
namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem row0_good (q : Fin 9) : goodTowers 28 (cubicTable 0 q)=true := by
  fin_cases q
  · exact good0_0
  · exact good0_1
  · exact good0_2
  · exact good0_3
  · exact good0_4
  · exact good0_5
  · exact good0_6
  · exact good0_7
  · exact good0_8

theorem row1_good (q : Fin 9) : goodTowers 28 (cubicTable 1 q)=true := by
  fin_cases q
  · exact good1_0
  · exact good1_1
  · exact good1_2
  · exact good1_3
  · exact good1_4
  · exact good1_5
  · exact good1_6
  · exact good1_7
  · exact good1_8

theorem row2_good (q : Fin 9) : goodTowers 28 (cubicTable 2 q)=true := by
  fin_cases q
  · exact good2_0
  · exact good2_1
  · exact good2_2
  · exact good2_3
  · exact good2_4
  · exact good2_5
  · exact good2_6
  · exact good2_7
  · exact good2_8

theorem cubicTable_good (s : Fin 3) (q : Fin 9) :
    goodTowers 28 (cubicTable s q)=true := by
  fin_cases s
  · exact row0_good q
  · exact row1_good q
  · exact row2_good q

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.cubicTable_good
end


/- Component: continuation_3/SegreModularDetectorExpressions.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularDetectorExpressions
open CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial
  CycleQ2SegreGaussianActionData

def shift14 (a b u v : ℕ) : Exponent := (0,u,v,14-(a+u+v+2*b),0)

def dotAction (W : WeightData) (i j k l : Fin 3) (a b u v : ℕ) : ℕ :=
  dot W i j (shift14 a b u v) (flatActionTable k l a b)

def entryDot00 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (0) % 109

def entryDot01 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (0) % 109

def entryDot02 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (0) % 109

def entryDot10 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (108*(dotAction W 0 1 2 2 a b u v) + dotAction W 0 2 2 1 a b u v) % 109

def entryDot11 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (dotAction W 0 0 2 2 a b u v + 108*(dotAction W 0 2 2 0 a b u v)) % 109

def entryDot12 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (108*(dotAction W 0 0 2 1 a b u v) + dotAction W 0 1 2 0 a b u v) % 109

def entryDot20 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (dotAction W 0 1 1 2 a b u v + 108*(dotAction W 0 2 1 1 a b u v)) % 109

def entryDot21 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (108*(dotAction W 0 0 1 2 a b u v) + dotAction W 0 2 1 0 a b u v) % 109

def entryDot22 (W : WeightData) (a b u v : ℕ) : ℕ :=
  (dotAction W 0 0 1 1 a b u v + 108*(dotAction W 0 1 1 0 a b u v)) % 109

def entryDot : Fin 3 → Fin 3 → WeightData → ℕ → ℕ → ℕ → ℕ → ℕ :=
  ![![entryDot00, entryDot01, entryDot02], ![entryDot10, entryDot11, entryDot12], ![entryDot20, entryDot21, entryDot22]]

def allowed14 (a b u v : ℕ) : Bool :=
  decide (a+u+v+2*b≤14 ∧ (2*a+2*u+v)%3=0)

def checkEntryBlock (W : WeightData) (i j : Fin 3) (a b : ℕ) : Bool :=
  (List.range 15).all (fun u => (List.range 15).all (fun v =>
    if allowed14 a b u v then entryDot i j W a b u v == 0 else true))

def checkEntry (W : WeightData) (i j : Fin 3) : Bool :=
  (List.range 3).all (fun a => (List.range 3).all (fun b => checkEntryBlock W i j a b))

end CycleQ2SegreModularDetectorExpressions

namespace CycleQ2SegreModularDetectorExpressions
open CycleQ2SparseModularFunctional

def checkEntryRow (W : WeightData) (i j : Fin 3) (a b u : ℕ) : Bool :=
  (List.range 15).all (fun v =>
    if allowed14 a b u v then entryDot i j W a b u v == 0 else true)

theorem checkEntryBlock_eq_rows (W : WeightData) (i j : Fin 3) (a b : ℕ) :
    checkEntryBlock W i j a b=(List.range 15).all (checkEntryRow W i j a b) := rfl

end CycleQ2SegreModularDetectorExpressions
end


/- Component: continuation_3/SegreModularDetectorMatrixBinding.lean -/
section
/-! # The finite detector functionals act on the literal Jacobian columns

All indices are bound through their actual monomial exponents. The formulas
below have no assumption about the order of a saved monomial enumeration.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorMatrixBinding

open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceJacobianNaturality CycleQ2IncidenceUniversalChart
  CycleQ2GenericEntryCoefficientBinding CycleQ2SparseModularFunctional
  CycleQ2SparseGaussianPolynomial CycleQ2SegreModularDetectorData

section Grading

variable {K : Type*} [Field K]

private theorem regrade {p : Poly K} {a b : Grade} (hp : HG p a) (h : a=b) :
    HG p b := h ▸ hp

/-- The literal cofactor quotient has its actual degree and character. -/
theorem rawCofactorQuotient_homogeneous (r : K) (i j : Fin 3) :
    HG (rawCofactorQuotient r i j) (22,0) := by
  have hp : HG (seedG r*rawCofactorQuotient r i j) (28,0) := by
    rw [←rawSeedMatrix_cofactor]
    exact cofactors_homogeneous (rawSeedMatrix r) (rawSeedMatrix_homogeneous r) i j
  have heq : seedG r*weightedHomogeneousComponent fullGrading (22,0)
      (rawCofactorQuotient r i j)=seedG r*rawCofactorQuotient r i j := by
    calc
      _ = weightedHomogeneousComponent fullGrading (28,0)
          (seedG r*rawCofactorQuotient r i j) :=
        (CycleQ2WeightedComponent.component_mul_left fullGrading (seedG r)
          (rawCofactorQuotient r i j) (6,0) (22,0) (seedG_homogeneous r)).symm
      _ = _ := weightedHomogeneousComponent_eq_self hp
  have hq := mul_left_cancel₀ (seedG_ne_zero r) heq
  rw [←hq]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem cubicResidual_homogeneous (r ι : K) (e : FullInvariantIndex 3) (i j : Fin 3) :
    HG (MvPolynomial.monomial (fullExponentOf e.val) (1:K)*smoothK ι*
      rawCofactorQuotient r i j) (28,0) := by
  have hH : HG (MvPolynomial.monomial (fullExponentOf e.val) (1:K)) (3,0) :=
    isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e)
  exact regrade ((hH.mul (smoothK_homogeneous ι)).mul
    (rawCofactorQuotient_homogeneous r i j)) (by decide)

end Grading

theorem functional_monomial_any (W : WeightData) (i j : Fin 3)
    (e : Fin 5 →₀ ℕ) (c : F) :
    functional W i j (MvPolynomial.monomial e c)=c*polyWeight W i j e := by
  change Finsupp.linearCombination F (polyWeight W i j) (Finsupp.single e c)=_
  rw [Finsupp.linearCombination_single]
  rfl

theorem functional_standard_expansion (W : WeightData) (i j : Fin 3)
    (p : P) (hs : FullStandard p) (hg : HG p (28,0)) :
    functional W i j p=
      ∑e : StandardIndex 28,p.coeff (standardExponent e)*polyWeight W i j (standardExponent e) := by
  conv_lhs => rw [←expansion_coefficients 28 p hs hg]
  simp only [expansion,map_sum,map_smul,functional_monomial_any,one_mul,smul_eq_mul]

def detectorRow (W : WeightData) (q : EquationIndex) : F :=
  if q.1.1=0 then polyWeight W 0 q.1.2 (standardExponent q.2) else 0

def detectorMatrix : Matrix (Fin 7) EquationIndex F := fun k => detectorRow (weights k)

theorem detector_coefficients (W : WeightData)
    (p : Matrix (Fin 3) (Fin 3) P)
    (hs : ∀j,FullStandard (p 0 j)) (hg : ∀j,HG (p 0 j) (28,0)) :
    (∑q : EquationIndex,detectorRow W q*(p q.1.1 q.1.2).coeff (standardExponent q.2))=
      ∑j : Fin 3,functional W 0 j (p 0 j) := by
  classical
  simp only [detectorRow,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single 0]
  · simp only [if_pos rfl]
    apply Finset.sum_congr rfl
    intro j _
    rw [functional_standard_expansion W 0 j (p 0 j) (hs j) (hg j)]
    apply Finset.sum_congr rfl
    intro e _
    exact mul_comm _ _
  · intro i _ hi
    simp only [if_neg hi,zero_mul,Finset.sum_const_zero]
  · simp

def basisMatrix (c : MatrixParameter) : Matrix (Fin 3) (Fin 3) P :=
  rawInput (Pi.single c (1:F))

theorem basisMatrix_apply (c : MatrixParameter) (i j : Fin 3) :
    basisMatrix c i j=
      if (i,j)=c.1 then MvPolynomial.monomial (standardExponent c.2) (1:F) else 0 := by
  classical
  rcases c with ⟨⟨k,l⟩,e⟩
  by_cases hik : i=k <;> by_cases hjl : j=l
  · subst k
    subst l
    simp [basisMatrix,rawInput,expansion,Pi.single_apply]
  · simp [basisMatrix,rawInput,expansion,Pi.single_apply,hjl,eq_comm]
  · simp [basisMatrix,rawInput,expansion,Pi.single_apply,hik,eq_comm]
  · simp [basisMatrix,rawInput,expansion,Pi.single_apply,hik,hjl,eq_comm]

theorem entry_column (c : MatrixParameter) (q : EquationIndex) :
    entryJacobianBlock (57:F) 33 q c=
      (nf (57:F) 33 (cofactorDifferential (rawSeedMatrix (57:F))
        (basisMatrix c) q.1.1 q.1.2)).coeff (standardExponent q.2) := by
  rw [←entryCoefficients_matrix,LinearMap.toMatrix'_apply,entryCoefficients_apply]
  rfl

theorem detector_entry_column (k : Fin 7) (c : MatrixParameter) :
    (detectorMatrix*entryJacobianBlock (57:F) 33) k c=
      ∑j : Fin 3,functional (weights k) 0 j
        (nf (57:F) 33 (cofactorDifferential (rawSeedMatrix (57:F)) (basisMatrix c) 0 j)) := by
  simp only [Matrix.mul_apply,detectorMatrix,entry_column]
  exact detector_coefficients (weights k)
    (fun i j => nf (57:F) 33
      (cofactorDifferential (rawSeedMatrix (57:F)) (basisMatrix c) i j))
    (fun j => nf_standard 57 33 _)
    (fun j => nf_grade 57 33 28 _
      (rawDifferential_grade (57:F) (Pi.single c (1:F)) 0 j))

theorem fullInvariantPolynomial_single {K : Type*} [CommRing K]
    (d : ℕ) (e : FullInvariantIndex d) (c : K) :
    fullInvariantPolynomial d (Pi.single e c)=MvPolynomial.monomial (fullExponentOf e.val) c := by
  classical
  simp [fullInvariantPolynomial,Pi.single_apply,apply_ite,eq_comm]

theorem cubic_column (e : FullInvariantIndex 3) (q : EquationIndex) :
    linearizedMatrix (57:F) 33 q (Sum.inl e)=
      (nf (57:F) 33 (MvPolynomial.monomial (fullExponentOf e.val) (1:F)*
        smoothK 33*rawCofactorQuotient 57 q.1.1 q.1.2)).coeff (standardExponent q.2) := by
  classical
  have hH : (fun t : FullInvariantIndex 3 =>
      if (Sum.inl e : ParameterIndex)=Sum.inl t then (1:F) else 0)=Pi.single e 1 := by
    funext t
    simp [Pi.single_apply,eq_comm]
  have hF : (fun t : FullInvariantIndex 6 =>
      if (Sum.inl e : ParameterIndex)=Sum.inr (Sum.inl t) then (1:F) else 0)=0 := by
    funext t
    simp
  have hM : (fun i j t =>
      if (Sum.inl e : ParameterIndex)=Sum.inr (Sum.inr ((i,j),t)) then (1:F) else 0)=
        (fun _ _ _ => (0:F)) := by
    funext i j t
    simp
  have hzero : cofactorDifferential (rawSeedMatrix (57:F)) 0=0 :=
    (cofactorDifferentialLinear (rawSeedMatrix (57:F))).map_zero
  have hFzero : fullInvariantPolynomial 6 (0 : FullInvariantIndex 6 → F)=0 := by
    simp [fullInvariantPolynomial]
  have hMzero : perturbation (fun _ _ _ => (0:F))=0 := by
    funext i j
    simp [perturbation]
  rw [linearizedMatrix,hH,hF,hM]
  rw [linearizedEquations,fullInvariantPolynomial_single,hFzero,hMzero]
  simp only [fullFirstOrderResidual,firstOrderResidual,hzero,Matrix.zero_apply,
    zero_add,zero_mul,sub_zero]
  rfl

theorem cubicExponent_grade (k : Fin 9) :
    Finsupp.weight fullGrading (tupleExponent (cubicExponents k))=(3,0) := by
  apply (fullGrading_eq_iff _ 3).mpr
  change fullDegree (tupleFun (cubicExponents k))=3 ∧
    fullCharacter (tupleFun (cubicExponents k))=0
  fin_cases k <;> decide

def cubicIndex (k : Fin 9) : FullInvariantIndex 3 :=
  fullIndexOf (tupleExponent (cubicExponents k)) (cubicExponent_grade k)

theorem cubicIndex_exponent (k : Fin 9) :
    fullExponentOf (cubicIndex k).val=tupleExponent (cubicExponents k) :=
  fullIndexOf_exponent _ _

def selectedCubicBlock : Matrix EquationIndex (Fin 9) F :=
  (linearizedMatrix (57:F) 33).submatrix id (fun k => Sum.inl (cubicIndex k))

theorem detector_cubic_column (k : Fin 7) (c : Fin 9) :
    (detectorMatrix*selectedCubicBlock) k c=
      ∑j : Fin 3,functional (weights k) 0 j
        (nf (57:F) 33 (MvPolynomial.monomial (tupleExponent (cubicExponents c)) (1:F)*
          smoothK 33*rawCofactorQuotient 57 0 j)) := by
  simp only [Matrix.mul_apply,detectorMatrix,selectedCubicBlock,Matrix.submatrix_apply,
    id_eq,cubic_column]
  rw [cubicIndex_exponent]
  exact detector_coefficients (weights k)
    (fun i j => nf (57:F) 33
      (MvPolynomial.monomial (tupleExponent (cubicExponents c)) (1:F)*
        smoothK 33*rawCofactorQuotient 57 i j))
    (fun j => nf_standard 57 33 _)
    (fun j => nf_grade 57 33 28 _ (by
      rw [←cubicIndex_exponent]
      exact cubicResidual_homogeneous 57 33 (cubicIndex c) 0 j))

end CycleQ2SegreModularDetectorMatrixBinding

#print axioms CycleQ2SegreModularDetectorMatrixBinding.detector_entry_column
#print axioms CycleQ2SegreModularDetectorMatrixBinding.detector_cubic_column
end
end


/- Component: continuation_3/CurveCechRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechRestrictions

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization CycleQ2CurveCechLocalizedBasis

variable (R : Type*) [CommRing R]

instance curveLocalAway (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    IsLocalization.Away (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))
      (CurveLocal R side r ι s) := by
  have hh : Algebra.algebraMapSubmonoid (CurveRing side r ι)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem curveProduct_isUnit (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    IsUnit (algebraMap (CurveRing side r ι) (CurveLocal R side r ι t)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := CurveLocal R side r ι t)
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (CurveRing side r ι)) (baseProduct_dvd R hst)

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    CurveLocal R side r ι s →+* CurveLocal R side r ι t :=
  IsLocalization.Away.lift
    (S := CurveLocal R side r ι s)
    (P := CurveLocal R side r ι t)
    (g := algebraMap (CurveRing side r ι) (CurveLocal R side r ι t))
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))
    (curveProduct_isUnit R side r ι hst)

@[simp] theorem restriction_algebraMap (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t)
    (p : CurveRing side r ι) :
    restriction R side r ι hst (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι t) p :=
  IsLocalization.Away.lift_eq (S := CurveLocal R side r ι s)
    (P := CurveLocal R side r ι t) _ (curveProduct_isUnit R side r ι hst) p

theorem coordinates_mul_base [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : CurveLocal R side r ι s) (c : Base R) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s
      (p * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
        (algebraMap (Base R) (CurveRing side r ι) c)) ab =
      baseToLaurent R c * localizedCoordinates R side r ι s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (CurveRing side r ι) (CurveLocal R side r ι s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (CurveLocal R side r ι s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (side : Side) (r ι : R)
    {s t : Finset (Fin 2)} (hst : s ⊆ t) (z : CurveLocal R side r ι s) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι t (restriction R side r ι hst z) ab =
      localizedCoordinates R side r ι s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) z
  have hp' : z * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R side r ι s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R side r ι hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R side r ι t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- The actual two-coordinate curve Čech differential is surjective
in every total degree at least two. -/
theorem coordinateCech_exact [Nontrivial R] (side : Side) (r ι : R)
    (d : ℤ) (hd : 2≤d) (p : CurveLocal R side r ι {0,1})
    (hg : ∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0,1} p ab)) :
    ∃ (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}),
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0} q0 ab)) ∧
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {1} q1 ab)) ∧
      p=restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1-
        restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0 := by
  obtain ⟨q0,q1,hg0,hg1,he⟩ := localized_sixSummand_exact R side r ι d hd p hg
  refine ⟨q0,q1,hg0,hg1,?_⟩
  apply localizedCoordinates_injective R side r ι {0,1}
  funext ab
  simpa only [map_sub,Pi.sub_apply,coordinates_restriction] using congrFun he ab

end CycleQ2CurveCechRestrictions

#print axioms CycleQ2CurveCechRestrictions.coordinateCech_exact
end
end


/- Component: continuation_3/CurveRestrictionComplex.lean -/
section
/-! The actual complex restriction maps are surjective.  The two nonzero
minors come from independently checked modular polynomial identities and
inverse products, transported through the Gaussian integral family. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open CycleQ2CurveRestrictionReflection CycleQ2CurveRestrictionModularData
  CycleQ2CurveRestrictionModularChecks CycleQ2IncidenceGaussianArithmetic

/-- Every standard monomial of the full left curve piece occurs as a row. -/
theorem left_rows_cover : ∀ q : TargetIndex .left 10,
    ∃ i : Fin 57, leftRows i=targetTuple q := by decide +kernel

/-- Every standard monomial of the full right curve piece occurs as a row. -/
theorem right_rows_cover : ∀ q : TargetIndex .right 8,
    ∃ i : Fin 45, rightRows i=targetTuple q := by decide +kernel

theorem left_sources_good : ∀ j : Fin 57, sourceGood 10 0 (leftSources j)=true := by decide +kernel

theorem right_sources_good : ∀ j : Fin 45, sourceGood 8 1 (rightSources j)=true := by decide +kernel

noncomputable section

theorem complex_minor_nonzero_of_modular (s : Side) {n : ℕ}
    (rows : Fin n → CurveTuple) (columns : Fin n → SourceTuple)
    (hmod : Matrix.det (fun i j : Fin n =>
      matrixCoefficient s (57:F109) 33 (rows i) (columns j))≠0) :
    Matrix.det (fun i j : Fin n => matrixCoefficient s (57:ℂ) Complex.I (rows i) (columns j))≠0 := by
  let A : Matrix (Fin n) (Fin n) GaussianInt :=
    fun i j => matrixCoefficient s 57 gaussianI (rows i) (columns j)
  have hm : A.map reduction =
      (fun i j : Fin n => matrixCoefficient s (57:F109) 33 (rows i) (columns j)) := by
    ext i j
    change reduction (matrixCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,reduction_I] using
      matrixCoefficient_map reduction s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hc : A.map GaussianInt.toComplex =
      (fun i j : Fin n => matrixCoefficient s (57:ℂ) Complex.I (rows i) (columns j)) := by
    ext i j
    change GaussianInt.toComplex (matrixCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,complex_I] using
      matrixCoefficient_map GaussianInt.toComplex s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hA := determinant_nonzero_of_reduction A (by rw [hm]; exact hmod)
  rwa [hc] at hA

theorem left_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 57 => matrixCoefficient .left (57:ℂ) Complex.I (leftRows i) (leftSources j))≠0 :=
  complex_minor_nonzero_of_modular .left leftRows leftSources (left_minor_det_ne_zero (R:=F109))

theorem right_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 45 => matrixCoefficient .right (57:ℂ) Complex.I (rightRows i) (rightSources j))≠0 :=
  complex_minor_nonzero_of_modular .right rightRows rightSources (right_minor_det_ne_zero (R:=F109))

/-- Restriction from the actual degree10 invariant seed piece to the actual
left complete-intersection curve is onto over the complex numbers. -/
theorem left_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0) :=
  seedRestrictionPiece_surjective_of_minor .left 57 Complex.I 10 0 57
    leftRows leftSources left_rows_cover left_sources_good left_complex_minor_nonzero

/-- Restriction from the actual degree8 character-one seed piece to the actual
right complete-intersection curve is onto over the complex numbers. -/
theorem right_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1) :=
  seedRestrictionPiece_surjective_of_minor .right 57 Complex.I 8 1 45
    rightRows rightSources right_rows_cover right_sources_good right_complex_minor_nonzero

theorem left_restriction_kernel_rank :
    Module.finrank ℂ (LinearMap.ker (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0))=56 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 10 0 (by decide))
  have h := (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr left_restriction_surjective,finrank_top,
    left_seedPiece_rank,left_curvePiece_rank] at h
  omega

theorem right_restriction_kernel_rank :
    Module.finrank ℂ (LinearMap.ker (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1))=23 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 8 1 (by decide))
  have h := (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr right_restriction_surjective,finrank_top,
    right_seedPiece_rank,right_curvePiece_rank] at h
  omega

end
end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_restriction_surjective
#print axioms CycleQ2CurveRestriction.right_restriction_surjective
#print axioms CycleQ2CurveRestriction.left_restriction_kernel_rank
#print axioms CycleQ2CurveRestriction.right_restriction_kernel_rank
end


/- Component: continuation_3/HomogeneousIdealOpen.lean -/
section
/-! A finite homogeneous multiplication map is surjective on one actual
polynomial open whenever its seed specialization generates the entire
homogeneous piece. The degree and all finite indices remain symbolic in
this proof. Concrete large-degree applications use the theorem directly.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2HomogeneousIdealOpen

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic

variable {R K : Type*} [CommRing R] [CommRing K]
  {ι : Type*} [Fintype ι]

theorem exists_multiplication_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j≤N)
    (hseed : ∀ p : Poly K, HG p (N,0) →
      p∈generatorIdeal (fun j => map f (g j))) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        Function.Surjective ((multiplicationMatrix g degree N).map φ).mulVec := by
  classical
  have hA : Function.Surjective ((multiplicationMatrix g degree N).map f).mulVec := by
    rw [multiplicationMatrix_map]
    exact multiplication_surjective_of_membership (fun j => map f (g j)) degree
      (fun j => homogeneous_map f (hgen j)) N hle hseed
  obtain ⟨B,s,hsdet,hsseed,hs⟩ :=
    CycleQ2PolynomialSurjectivityOpen.exists_surjectivity_open
      (m:=FullInvariantIndex N) (n:=Column N degree) f c hfc
      (multiplicationMatrix g degree N) hA
  exact ⟨s,hsseed,hs⟩

theorem exists_homogeneous_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) (N : ℕ) (hle : ∀ j, degree j≤N)
    (hseed : ∀ p : Poly K, HG p (N,0) →
      p∈generatorIdeal (fun j => map f (g j))) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        ∀ p : Poly S, HG p (N,0) → p∈generatorIdeal (fun j => map φ (g j)) := by
  obtain ⟨s,hsseed,hs⟩ := exists_multiplication_open f c hfc g degree hgen N hle hseed
  refine ⟨s,hsseed,?_⟩
  intro S _ φ hφ p hp
  have hsurj := hs S φ hφ
  rw [multiplicationMatrix_map] at hsurj
  exact membership_of_multiplication_surjective (fun j => map φ (g j)) degree
    (fun j => homogeneous_map φ (hgen j)) N hle hsurj p hp

end CycleQ2HomogeneousIdealOpen

#print axioms CycleQ2HomogeneousIdealOpen.exists_multiplication_open
#print axioms CycleQ2HomogeneousIdealOpen.exists_homogeneous_open
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceCubicIndices.lean -/
section
/-! The literal nine detector cubic columns enumerate every invariant cubic
coefficient.  The enumeration is checked independently of any tangent data. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceCubicCechTrace
open CycleQ2IncidenceNormalForm CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2SegreModularDetectorData

theorem cubicIndex_injective : Function.Injective cubicIndex := by decide

theorem cubicIndex_bijective : Function.Bijective cubicIndex :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨cubicIndex_injective,by rw [Fintype.card_fin,CycleQ2IncidenceFullIndexCounts.cubic_count]⟩

def cubicEquiv : Fin 9 ≃ FullInvariantIndex 3 := Equiv.ofBijective cubicIndex cubicIndex_bijective

theorem cubicIndex8_eq_leading : cubicIndex 8=fullCubicLeadingIndex := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change CycleQ2SparseGaussianPolynomial.tupleFun (cubicExponents 8) i=
    (fullCubicLeadingIndex.val i).val
  fin_cases i <;> rfl

end CycleQ2IncidenceCubicCechTrace

#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex_injective
#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex_bijective
#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex8_eq_leading
end
end


/- Component: continuation_3/SeedCechLinearCoordinates.lean -/
section
/-! # Scalar compatibility of the actual localized seed coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechLinearCoordinates

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R]

theorem base_C_seed (r ι c : R) :
    algebraMap (Base R) (SeedRing r ι) (C c) = algebraMap R (SeedRing r ι) c := by
  change Ideal.Quotient.mk _ (remainingInclusion R (C c)) = Ideal.Quotient.mk _ (C c)
  simp [remainingInclusion]

theorem localized_scalar_eq (r ι : R) (s : Finset (Fin 3)) (c : R)
    (p : SeedLocal R r ι s) :
    algebraMap (Base R) (coordinateLocalization R s) (C c) • p = c • p := by
  simp only [Algebra.smul_def]
  rw [← IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SeedLocal R r ι s),
    IsScalarTower.algebraMap_apply (Base R) (SeedRing r ι) (SeedLocal R r ι s), base_C_seed,
    ← IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι s)]

theorem localizedCoordinates_R_smul [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (c : R) (p : SeedLocal R r ι s) :
    localizedCoordinates R r ι s (c • p) = c • localizedCoordinates R r ι s p := by
  funext ab
  rw [← localized_scalar_eq R r ι s c p, localizedCoordinates_smul,
    localizationToLaurent_algebraMap]
  change baseToLaurent R (algebraMap R (Base R) c) * _ = c • _
  rw [AlgHom.commutes, Algebra.smul_def]

def linearCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →ₗ[R] (ShiftIndex → Laurent (R := R)) where
  __ := localizedCoordinates R r ι s
  map_smul' c p := localizedCoordinates_R_smul R r ι s c p

@[simp] theorem linearCoordinates_apply [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) :
    linearCoordinates R r ι s p = localizedCoordinates R r ι s p := rfl

def restrictionLinear [Nontrivial R] (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SeedLocal R r ι s →ₗ[R] SeedLocal R r ι t where
  __ := (restriction R r ι hst).toAddMonoidHom
  map_smul' c p := by
    apply localizedCoordinates_injective R r ι t
    funext ab
    change localizedCoordinates R r ι t (restriction R r ι hst (c • p)) ab =
      localizedCoordinates R r ι t (c • restriction R r ι hst p) ab
    simp only [localizedCoordinates_R_smul, Pi.smul_apply, coordinates_restriction]

end CycleQ2SeedCechLinearCoordinates

#print axioms CycleQ2SeedCechLinearCoordinates.linearCoordinates
#print axioms CycleQ2SeedCechLinearCoordinates.restrictionLinear
end
end


/- Component: continuation_3/SeedLinkageIdeals.lean -/
section
/-! The literal linkage ideals in the actual smooth seed quotient. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageIdeals

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobian CycleQ2IncidenceJacobianNaturality CycleQ2SegreTangentLocal
  CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

variable {R : Type*} [CommRing R]

def linkageGenerator (s : Side) (r : R) : Fin 5 → Poly R :=
  match s with
  | .left => CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)
  | .right => CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)

def generatorDegree : Fin 5 → ℕ := ![4,6,6,6,6]
def generatorCharacter : Fin 5 → ℕ := ![1,0,1,2,0]

private theorem regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a=b) : HG p b := h ▸ hp

theorem linkageGenerator_homogeneous (s : Side) (r : R) (j : Fin 5) :
    HG (linkageGenerator s r j) (generatorDegree j,(generatorCharacter j:ZMod 3)) := by
  let a : Poly R := X 0^2
  let b : Poly R := C r*X 1*X 3
  let c : Poly R := X 4
  let d : Poly R := X 2^2
  have ha : HG a (2,1) := regrade ((isWeightedHomogeneous_X R fullGrading 0).pow 2) (by decide)
  have hb : HG b (2,2) := by
    apply regrade (p:=b) _ (show fullGrading 1+fullGrading 3=(2,2) from by decide)
    simpa only [b,mul_assoc] using
      ((isWeightedHomogeneous_X R fullGrading 1).mul (isWeightedHomogeneous_X R fullGrading 3)).C_mul r
  have hc : HG c (2,0) := isWeightedHomogeneous_X R fullGrading 4
  have hd : HG d (2,2) := regrade ((isWeightedHomogeneous_X R fullGrading 2).pow 2) (by decide)
  cases s <;> fin_cases j
  · change HG (a*c+b*d) (4,1)
    exact (regrade (ha.mul hc) (by decide)).add (regrade (hb.mul hd) (by decide))
  · change HG (a^3-b^3) (6,0)
    exact (regrade (ha.pow 3) (by decide)).sub (regrade (hb.pow 3) (by decide))
  · change HG (a^2*d+b^2*c) (6,1)
    exact (regrade ((ha.pow 2).mul hd) (by decide)).add (regrade ((hb.pow 2).mul hc) (by decide))
  · change HG (a*d^2-b*c^2) (6,2)
    exact (regrade (ha.mul (hd.pow 2)) (by decide)).sub (regrade (hb.mul (hc.pow 2)) (by decide))
  · change HG (c^3+d^3) (6,0)
    exact (regrade (hc.pow 3) (by decide)).add (regrade (hd.pow 3) (by decide))
  · change HG (a*c+b*d) (4,1)
    exact (regrade (ha.mul hc) (by decide)).add (regrade (hb.mul hd) (by decide))
  · change HG (a^3+d^3) (6,0)
    exact (regrade (ha.pow 3) (by decide)).add (regrade (hd.pow 3) (by decide))
  · change HG (a^2*b-c*d^2) (6,1)
    exact (regrade ((ha.pow 2).mul hb) (by decide)).sub (regrade (hc.mul (hd.pow 2)) (by decide))
  · change HG (a*b^2+c^2*d) (6,2)
    exact (regrade (ha.mul (hb.pow 2)) (by decide)).add (regrade ((hc.pow 2).mul hd) (by decide))
  · change HG (-b^3+c^3) (6,0)
    exact (regrade (hb.pow 3) (by decide)).neg.add (regrade (hc.pow 3) (by decide))

def curveGeneratorQuotient (s : Side) (r : R) : Fin 5 → CurvePoly R :=
  match s with
  | .left =>
      let a : CurvePoly R := X 0^2
      let b : CurvePoly R := C r*X 1*X 3
      let d : CurvePoly R := X 2^2
      ![-d,a^2+a*b+b^2,(a+b)*d,d^2,0]
  | .right =>
      let a : CurvePoly R := (X 0+X 2)^2
      let b : CurvePoly R := C (4*r)*X 1*X 3
      let d : CurvePoly R := (X 0-X 2)^2
      ![2*b,2*(a^2-a*d+d^2),2*b*(a-d),2*b^2,0]

theorem substitution_linkageGenerator (s : Side) (r : R) (j : Fin 5) :
    substitution s r (linkageGenerator s r j)=curveGeneratorQuotient s r j*quadric s r := by
  cases s <;> fin_cases j <;>
    simp [linkageGenerator,CycleQ2SegreSeed.linkageE,CycleQ2SegreSeed.linkageEprime,
      curveGeneratorQuotient,quadric,map_add,map_sub,map_mul,map_pow,
      restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat] <;> ring

def linkageIdeal (s : Side) (r ι : R) : Ideal (SeedRing r ι) :=
  Ideal.span (Set.range (fun j =>
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j)))

theorem linkageGenerator_mem (s : Side) (r ι : R) (j : Fin 5) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j) ∈
      linkageIdeal s r ι := Ideal.subset_span ⟨j,rfl⟩

theorem linkageIdeal_le_restrictionKernel (s : Side) (r ι : R) :
    linkageIdeal s r ι ≤ RingHom.ker (seedRestriction s r ι).toRingHom := by
  apply Ideal.span_le.mpr
  rintro z ⟨j,rfl⟩
  change seedRestriction s r ι
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j))=0
  rw [seedRestriction_mk]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [substitution_linkageGenerator]
  apply Ideal.mem_span_pair.mpr
  exact ⟨curveGeneratorQuotient s r j,0,by simp⟩

def linkagePiece (s : Side) (r ι : R) (d ch : ℕ) : Submodule R (SeedPiece r ι d ch) :=
  ((linkageIdeal s r ι).restrictScalars R).comap (SeedPiece r ι d ch).subtype

theorem linkagePiece_le_restrictionKernel (s : Side) (r ι : R) (d ch : ℕ) :
    linkagePiece s r ι d ch ≤ LinearMap.ker (seedRestrictionPiece s r ι d ch) := by
  intro q hq
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change seedRestriction s r ι q.val=0
  exact linkageIdeal_le_restrictionKernel s r ι hq

def seedNormal [Nontrivial R] (r ι : R) : Poly R →ₗ[R] Poly R :=
  fullRemainderLinear (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)

@[simp] theorem seedNormal_apply [Nontrivial R] (r ι : R) (p : Poly R) :
    seedNormal r ι p=fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p := rfl

theorem seedNormal_spec [Nontrivial R] (r ι : R) (p : Poly R) :
    FullStandard (seedNormal r ι p) ∧ ∃ a b,
      p=a*smoothH ι+b*seedG r+seedNormal r ι p := by
  obtain ⟨hs,a,b,hp⟩ := fullRemainder_spec (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial,smoothF] at hp
  refine ⟨hs,a+b*smoothK ι,b,?_⟩
  simp only [seedNormal_apply]
  linear_combination hp

theorem seedNormal_unique [Nontrivial R] (r ι : R) (p q a b : Poly R)
    (hq : FullStandard q) (hp : p=a*smoothH ι+b*seedG r+q) : q=seedNormal r ι p := by
  apply (existsUnique_full_invariant_representative (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) p).choose_spec.2
  refine ⟨hq,a-b*smoothK ι,b,?_⟩
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial,smoothF]
  linear_combination hp

theorem seedNormal_homogeneous [Nontrivial R] (r ι : R) {p : Poly R} {d : ℕ} {ch : ZMod 3}
    (hp : HG p (d,ch)) : HG (seedNormal r ι p) (d,ch) :=
  fullRemainder_preserves_grading (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) hp

theorem seedNormal_eq_zero_iff [Nontrivial R] (r ι : R) (p : Poly R) :
    seedNormal r ι p=0 ↔ p ∈ equationsIdeal (smoothH ι) (smoothF r ι) := by
  rw [seedNormal_apply,fullRemainder_eq_zero_iff,seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial]

theorem seedNormal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (r ι : R) (p : Poly R) :
    MvPolynomial.map φ (seedNormal r ι p)=seedNormal (φ r) (φ ι) (MvPolynomial.map φ p) := by
  simp only [seedNormal_apply]
  rw [fullRemainder_map]
  simp only [map_seedCubicCoefficients,map_seedSexticCoefficients]

@[simp] theorem map_linkageGenerator {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (j : Fin 5) :
    MvPolynomial.map φ (linkageGenerator s r j)=linkageGenerator s (φ r) j := by
  cases s <;> fin_cases j <;>
    simp [linkageGenerator,CycleQ2SegreSeed.linkageE,CycleQ2SegreSeed.linkageEprime,
      Matrix.cons_val_succ,Fin.reduceSucc]

end CycleQ2SeedLinkageIdeals

#print axioms CycleQ2SeedLinkageIdeals.linkagePiece_le_restrictionKernel
#print axioms CycleQ2SeedLinkageIdeals.seedNormal_map
end
end


/- Component: continuation_3/cylinder_bridge/SeedNormalGeneralParameter.lean -/
section
/-! # The actual seed conormal equation for every parameter

The Segre incidence family uses `smoothF r I`, whose definition is the
polynomial factorization for every `r`. The restriction `r^3 = 2` is needed
only to identify this polynomial with the fixed Fermat equation. This file
binds the actual incidence hypersurface to the actual curve ideal and its
conormal module without imposing that restriction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2NormalConnecting

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta

/-- The parameter-dependent hypersurface equation actually used by the
Segre incidence presentation. -/
def actualSeedEquation (r θ : ℂ) : WeightedPoly :=
  originalF1 r*originalG1 r+originalF2*originalG2+thetaH θ*thetaK θ

/-- The literal incidence polynomial `seedG` has this factorization for
all parameter values, without a Fermat specialization. -/
theorem seedG_eq_factorization (r : ℂ) :
    CycleQ2IncidenceEquations.seedG r =
      originalF1 r*originalG1 r+originalF2*originalG2 := by
  unfold CycleQ2IncidenceEquations.seedG
  rw [CycleQ2SegreSeed.seedG_expanded]
  unfold originalF1 originalG1 originalF2 originalG2
  simp only [map_pow]
  ring

/-- At the smooth cubic seed, this is the actual hypersurface equation of
the incidence system, including at `r = 57`. -/
theorem actualSeedEquation_eq_smoothF (r : ℂ) :
    actualSeedEquation r 1 = CycleQ2IncidenceEquations.smoothF r Complex.I := by
  unfold actualSeedEquation CycleQ2IncidenceEquations.smoothF
  rw [seedG_eq_factorization,smoothH_eq_thetaH]
  have hk : CycleQ2IncidenceEquations.smoothK Complex.I = thetaK 1 := by
    simp [CycleQ2IncidenceEquations.smoothK,CycleQ2IncidenceEquations.smoothB,
      CycleQ2IncidenceEquations.smoothA,thetaK,originalK,originalB]
    ring
  rw [hk]

/-- The older fixed-Fermat equation is recovered only at the specified
cube-root parameter. -/
theorem actualSeedEquation_eq_thetaEquation (r θ : ℂ) (hr : r^3=2) :
    actualSeedEquation r θ=thetaEquation θ := by
  exact (thetaEquation_decomposition r θ hr).symm

@[simp] theorem ambientCurveMap_actualSeedEquation (r θ : ℂ) :
    ambientCurveMap r θ (actualSeedEquation r θ)=0 := by
  simp [actualSeedEquation]

@[simp] theorem ambientCurveMap_smoothF (r : ℂ) :
    ambientCurveMap r 1 (CycleQ2IncidenceEquations.smoothF r Complex.I)=0 := by
  rw [← actualSeedEquation_eq_smoothF]
  exact ambientCurveMap_actualSeedEquation r 1

/-- Literal ideal membership for the parameter-dependent equation. -/
theorem actualSeedEquation_mem (r θ : ℂ) :
    actualSeedEquation r θ ∈ ambientCurveIdeal r θ := by
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 0))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 1)))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 2))

/-- The actual normal equation is the class of the actual incidence
hypersurface in the curve ideal modulo its square. -/
theorem actual_conormal_relation (r θ : ℂ) :
    (ambientCurveIdeal r θ).toCotangent
        ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ =
      originalG1 r • conormalGenerator r θ 0+
      originalG2 • conormalGenerator r θ 1+thetaK θ • conormalGenerator r θ 2 := by
  have hh :
      (⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ : ambientCurveIdeal r θ) =
      originalG1 r • ⟨curveEquations r θ 0,curveEquation_mem r θ 0⟩+
      originalG2 • ⟨curveEquations r θ 1,curveEquation_mem r θ 1⟩+
      thetaK θ • ⟨curveEquations r θ 2,curveEquation_mem r θ 2⟩ := by
    apply Subtype.ext
    change actualSeedEquation r θ = originalG1 r*originalF1 r+originalG2*originalF2+
      thetaK θ*thetaH θ
    unfold actualSeedEquation
    ring
  rw [hh,map_add,map_add,map_smul,map_smul,map_smul]
  rfl

theorem smoothF_mem_curveIdeal (r : ℂ) :
    CycleQ2IncidenceEquations.smoothF r Complex.I ∈ ambientCurveIdeal r 1 := by
  rw [← actualSeedEquation_eq_smoothF]
  exact actualSeedEquation_mem r 1

/-- Direct binding of the incidence `smoothF` to the checked equation-normal
map, with no hypothesis on the cube of `r`. -/
theorem smoothF_conormal_relation (r : ℂ) :
    (ambientCurveIdeal r 1).toCotangent
        ⟨CycleQ2IncidenceEquations.smoothF r Complex.I,smoothF_mem_curveIdeal r⟩ =
      originalG1 r • conormalGenerator r 1 0+
      originalG2 • conormalGenerator r 1 1+thetaK 1 • conormalGenerator r 1 2 := by
  convert actual_conormal_relation r 1 using 1
  congr 1
  exact Subtype.ext (actualSeedEquation_eq_smoothF r).symm

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.actualSeedEquation_eq_smoothF
#print axioms CycleQ2NormalConnecting.actual_conormal_relation
#print axioms CycleQ2NormalConnecting.smoothF_conormal_relation
end
end


/- Component: continuation_3/cylinder_bridge/SeedNormalResidue.lean -/
section
/-! # Binding the normal connecting coefficient to the checked curve residue

This file retains the actual `g₁g₂` denominator, the actual sextic direction
`A=x₂x₃³w`, and the first-minus-second overlap convention.  Its functional
is `-1/(3r)` times the already checked smooth incidence trace.  It does not
identify this coefficient functional with an Abel--Jacobi pairing.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalConnecting
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def curveToLaurent (r θ : ℂ) (e : Bool) : CurveRing r θ →+* LaurentChart r θ e :=
  (chartEmbedding r θ e).comp (curveChart r θ e)

@[simp] theorem curveToLaurent_curveMap (r θ : ℂ) (e : Bool) (p : Poly) :
    curveToLaurent r θ e (curveMap r θ p)=laurentEval r θ e p := rfl

def ambientLaurent (r θ : ℂ) (e : Bool) : WeightedPoly →+* LaurentChart r θ e :=
  (laurentEval r θ e).comp substitute.toRingHom

@[simp] theorem curveToLaurent_ambientCurveMap (r θ : ℂ) (e : Bool) (p : WeightedPoly) :
    curveToLaurent r θ e (ambientCurveMap r θ p)=ambientLaurent r θ e p := rfl

def scalarMap (r θ : ℂ) (e : Bool) : ℂ →+* LaurentChart r θ e :=
  (laurentEval r θ e).comp C

theorem ambientLaurent_g1 (r θ : ℂ) (e : Bool) :
    ambientLaurent r θ e (originalG1 r)=
      scalarMap r θ e (3*r^2)*(chartAUnit r θ e : LaurentChart r θ e)^2 := by
  have hh := congrArg (curveToLaurent r θ e) (ambientCurveMap_g1 r θ)
  simpa only [curveToLaurent_ambientCurveMap, curveToLaurent_curveMap,
    map_mul, map_pow, laurentEval_curveA_shared, scalarMap, RingHom.comp_apply] using hh

theorem ambientLaurent_g2 (r θ : ℂ) (e : Bool) :
    ambientLaurent r θ e originalG2=
      scalarMap r θ e 3*(laurentX2Unit r θ e : LaurentChart r θ e)^4 := by
  have hh := congrArg (curveToLaurent r θ e) (ambientCurveMap_g2 r θ)
  simpa only [curveToLaurent_ambientCurveMap, curveToLaurent_curveMap,
    map_mul, map_pow, laurentEval_curveB, scalarMap, RingHom.comp_apply] using hh

def g1Unit (r θ : ℂ) (e : Bool) (hr : r≠0) : (LaurentChart r θ e)ˣ :=
  Units.map (scalarMap r θ e).toMonoidHom
    (Units.mk0 (3*r^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))) * chartAUnit r θ e^2

def g2Unit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (scalarMap r θ e).toMonoidHom (Units.mk0 3 (by norm_num)) * laurentX2Unit r θ e^4

@[simp] theorem coe_g1Unit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    (g1Unit r θ e hr : LaurentChart r θ e)=ambientLaurent r θ e (originalG1 r) := by
  rw [ambientLaurent_g1]
  rfl

@[simp] theorem coe_g2Unit (r θ : ℂ) (e : Bool) :
    (g2Unit r θ e : LaurentChart r θ e)=ambientLaurent r θ e originalG2 := by
  rw [ambientLaurent_g2]
  rfl

theorem coe_g1Unit_inv (r θ : ℂ) (e : Bool) (hr : r≠0) :
    (((g1Unit r θ e hr)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e)=
      scalarMap r θ e ((3*r^2)⁻¹)*((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^2 := by
  unfold g1Unit
  rw [mul_inv_rev, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  exact mul_comm _ _

theorem coe_g2Unit_inv (r θ : ℂ) (e : Bool) :
    (((g2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e)=
      scalarMap r θ e ((3 : ℂ)⁻¹)*((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^4 := by
  unfold g2Unit
  rw [mul_inv_rev, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  exact mul_comm _ _

/-- Pair the fixed-h equation-normal overlap coefficient with the chosen
cubic.  The local lifts are `firstLift` and `secondLift` from the preceding
module, with their actual image equations already proved. -/
def pairedNormalCocycle (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) : LaurentChart r θ e :=
  overlapCoefficient (g1Unit r θ e hr) (g2Unit r θ e)
    (ambientLaurent r θ e (thetaK θ)) (ambientLaurent r θ e derivativeA) 0 *
      laurentEval r θ e p

theorem pairedNormalCocycle_eq_fraction (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) :
    pairedNormalCocycle r θ e hr p =
      scalarMap r θ e (-(9*r^2)⁻¹)*fraction r θ e (derivativeNumerator p) 2 4 := by
  have hc : -((3*r^2)⁻¹*(3 : ℂ)⁻¹)= -(9*r^2)⁻¹ := by
    field_simp [hr]
    <;> ring
  have hp : ambientLaurent r θ e derivativeA*laurentEval r θ e p=
      laurentEval r θ e (derivativeNumerator p) := by
    change laurentEval r θ e (substitute derivativeA)*laurentEval r θ e p = _
    rw [← map_mul, substitute_derivativeA]
  unfold pairedNormalCocycle overlapCoefficient
  simp only [mul_zero, zero_sub, coe_g1Unit_inv, coe_g2Unit_inv]
  calc
    _ = scalarMap r θ e (-((3*r^2)⁻¹*(3 : ℂ)⁻¹))*
        (ambientLaurent r θ e derivativeA*laurentEval r θ e p)*
        ((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^2*
        ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^4 := by
      simp only [map_neg, map_mul]
      ring
    _ = _ := by rw [hc,hp]; simp only [fraction, mul_assoc]

def pairedNormalTrace (r θ : ℂ) (hr : r≠0) (p : Poly) : ℂ :=
  endpointResidue r θ false (pairedNormalCocycle r θ false hr p)-
    endpointResidue r θ true (pairedNormalCocycle r θ true hr p)

theorem endpointResidue_scalarMap (r θ : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r θ e) :
    endpointResidue r θ e (scalarMap r θ e c*z)=c*endpointResidue r θ e z := by
  have hc : scalarMap r θ e c=
      laurentBase r θ e (CycleQ2SeedCech.seriesMap (PowerSeries.C c)) := by
    simp [scalarMap, laurentEval, powerEval_C, chartEmbedding, powerBase, laurentBase]
  rw [hc, endpointResidue_scalar]

theorem pairedNormalTrace_eq_residue (r θ : ℂ) (hr : r≠0) (p : Poly) :
    pairedNormalTrace r θ hr p = -(9*r^2)⁻¹*cechResidue r θ (derivativeNumerator p) 2 4 := by
  simp only [pairedNormalTrace, pairedNormalCocycle_eq_fraction, endpointResidue_scalarMap,
    cechResidue, fractionResidue_eq_endpointResidue]
  ring

/-- The actual fixed-h normal coefficient gives a nonzero multiple of the
smooth incidence trace, with its sign and normalization fully specified. -/
theorem pairedNormalTrace_deformation (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ) :
    pairedNormalTrace r θ hr (cubicDeformation v)= -(3*r)⁻¹*derivativeTrace θ v := by
  rw [pairedNormalTrace_eq_residue, deformation_residue]
  field_simp [hr]
  <;> ring

theorem pairedNormalTrace_nonzero (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ)
    (hv : derivativeTrace θ v≠0) : pairedNormalTrace r θ hr (cubicDeformation v)≠0 := by
  rw [pairedNormalTrace_deformation]
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) hr))) hv

theorem overlapProduct_isUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    IsUnit (curveToLaurent r θ e (curveG1 r θ*curveG2 r θ)) := by
  rw [map_mul]
  change IsUnit (ambientLaurent r θ e (originalG1 r)*ambientLaurent r θ e originalG2)
  rw [← coe_g1Unit r θ e hr, ← coe_g2Unit r θ e]
  exact (g1Unit r θ e hr).isUnit.mul (g2Unit r θ e).isUnit

def overlapToLaurent (r θ : ℂ) (e : Bool) (hr : r≠0) : Overlap r θ →+* LaurentChart r θ e :=
  IsLocalization.Away.lift (curveG1 r θ*curveG2 r θ) (overlapProduct_isUnit r θ e hr)

@[simp] theorem overlapToLaurent_base (r θ : ℂ) (e : Bool) (hr : r≠0) (z : CurveRing r θ) :
    overlapToLaurent r θ e hr (algebraMap (CurveRing r θ) (Overlap r θ) z)=
      curveToLaurent r θ e z := IsLocalization.Away.lift_eq _ _ _

theorem overlapToLaurent_firstUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    Units.map (overlapToLaurent r θ e hr).toMonoidHom (firstOverlapUnit r θ)=g1Unit r θ e hr := by
  apply Units.ext
  change overlapToLaurent r θ e hr (firstOverlapUnit r θ : Overlap r θ)=_
  rw [coe_firstOverlapUnit, overlapToLaurent_base, coe_g1Unit]
  rfl

theorem overlapToLaurent_secondUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    Units.map (overlapToLaurent r θ e hr).toMonoidHom (secondOverlapUnit r θ)=g2Unit r θ e := by
  apply Units.ext
  change overlapToLaurent r θ e hr (secondOverlapUnit r θ : Overlap r θ)=_
  rw [coe_secondOverlapUnit, overlapToLaurent_base, coe_g2Unit]
  rfl

def pairedNormalOverlap (r θ : ℂ) (p : Poly) : Overlap r θ :=
  normalOverlapCoefficient r θ derivativeA 0*
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)

/-- The residue is evaluated on the actual localization class, not on an
independently chosen Laurent expression. -/
theorem overlapToLaurent_pairedNormalOverlap (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) :
    overlapToLaurent r θ e hr (pairedNormalOverlap r θ p)=pairedNormalCocycle r θ e hr p := by
  have h₁ : overlapToLaurent r θ e hr (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ)=
      (↑((g1Unit r θ e hr)⁻¹) : LaurentChart r θ e) := by
    change (↑((Units.map (overlapToLaurent r θ e hr).toMonoidHom (firstOverlapUnit r θ))⁻¹) :
      LaurentChart r θ e)=_
    rw [overlapToLaurent_firstUnit]
  have h₂ : overlapToLaurent r θ e hr (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)=
      (↑((g2Unit r θ e)⁻¹) : LaurentChart r θ e) := by
    change (↑((Units.map (overlapToLaurent r θ e hr).toMonoidHom (secondOverlapUnit r θ))⁻¹) :
      LaurentChart r θ e)=_
    rw [overlapToLaurent_secondUnit]
  simp only [pairedNormalOverlap, normalOverlapCoefficient, overlapCoefficient,
    overlapAmbient, RingHom.comp_apply, map_zero, mul_zero, zero_sub, map_mul, map_neg,
    overlapToLaurent_base, curveToLaurent_ambientCurveMap, curveToLaurent_curveMap, h₁, h₂,
    pairedNormalCocycle]

theorem actual_overlap_trace_deformation (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ) :
    endpointResidue r θ false (overlapToLaurent r θ false hr
        (pairedNormalOverlap r θ (cubicDeformation v)))-
      endpointResidue r θ true (overlapToLaurent r θ true hr
        (pairedNormalOverlap r θ (cubicDeformation v)))=
      -(3*r)⁻¹*derivativeTrace θ v := by
  rw [overlapToLaurent_pairedNormalOverlap, overlapToLaurent_pairedNormalOverlap]
  exact pairedNormalTrace_deformation r θ hr v

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.pairedNormalCocycle_eq_fraction
#print axioms CycleQ2NormalConnecting.pairedNormalTrace_deformation
#print axioms CycleQ2NormalConnecting.actual_overlap_trace_deformation
end
end


/- Component: continuation_3/SegreComplexBasepoint.lean -/
section
/-!
# Characteristic-zero basepoint freeness of the actual Segre seed

The checked modular coordinate-power identities imply that the entire
weighted-degree120 invariant polynomial piece lies in the generator ideal:
every such monomial is divisible by one of the five checked powers.
Homogeneous projection turns this into surjectivity of a finite coefficient
matrix. Arithmetic surjectivity transfer proves the corresponding complex
membership statement, hence coordinate-power membership for the actual
complex seed quotient. No modular solution is asserted to lift individually.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreComplexBasepoint

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobianNaturality CycleQ2IncidenceGaussianArithmetic
  CycleQ2HomogeneousIdealArithmetic CycleQ2SegreTangentLocal

def seedGenerators {R : Type*} [CommRing R] (r ι : R) : Fin 11 → Poly R :=
  ![rawSeedMatrix r 0 0, rawSeedMatrix r 0 1, rawSeedMatrix r 0 2,
    rawSeedMatrix r 1 0, rawSeedMatrix r 1 1, rawSeedMatrix r 1 2,
    rawSeedMatrix r 2 0, rawSeedMatrix r 2 1, rawSeedMatrix r 2 2,
    smoothH ι, seedG r]

def generatorDegree : Fin 11 → ℕ := ![14,14,14,14,14,14,14,14,14,3,6]

theorem generators_homogeneous {R : Type*} [CommRing R] (r ι : R) (j : Fin 11) :
    HG (seedGenerators r ι j) (generatorDegree j,0) := by
  fin_cases j
  · exact rawSeedMatrix_homogeneous r 0 0
  · exact rawSeedMatrix_homogeneous r 0 1
  · exact rawSeedMatrix_homogeneous r 0 2
  · exact rawSeedMatrix_homogeneous r 1 0
  · exact rawSeedMatrix_homogeneous r 1 1
  · exact rawSeedMatrix_homogeneous r 1 2
  · exact rawSeedMatrix_homogeneous r 2 0
  · exact rawSeedMatrix_homogeneous r 2 1
  · exact rawSeedMatrix_homogeneous r 2 2
  · exact smoothH_homogeneous ι
  · exact seedG_homogeneous r

theorem generatorDegree_le (j : Fin 11) : generatorDegree j ≤ 120 := by
  fin_cases j <;> decide

theorem seedGenerators_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (r ι : R) :
    (fun j => MvPolynomial.map φ (seedGenerators r ι j)) = seedGenerators (φ r) (φ ι) := by
  have hm (a b : Fin 3) : map φ (rawSeedMatrix r a b) = rawSeedMatrix (φ r) a b := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly S) => M a b)
      (map_rawSeedMatrix φ r)
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using h
  funext j
  fin_cases j <;> simp [seedGenerators, hm, map_smoothH, map_seedG]

theorem high_degree_divisible (e : FullInvariantIndex 120) :
    ∃ j : Fin 5, CycleQ2SegreModularBasepoint.degrees j ≤ fullExponentOf e.val j := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have hd := e.property.1
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 0 = 24 by decide] at h0
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 1 = 24 by decide] at h1
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 2 = 24 by decide] at h2
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 3 = 24 by decide] at h3
  rw [fullExponentOf_apply,
    show CycleQ2SegreModularBasepoint.degrees 4 = 12 by decide] at h4
  simp only [fullDegree] at hd
  omega

theorem modular_monomial_mem (e : FullInvariantIndex 120) :
    (monomial (fullExponentOf e.val) 1 : Poly F109) ∈
      generatorIdeal (seedGenerators (57 : F109) 33) := by
  obtain ⟨j, hj⟩ := high_degree_divisible e
  have he : Finsupp.single j (CycleQ2SegreModularBasepoint.degrees j) ≤
      fullExponentOf e.val := Finsupp.single_le_iff.mpr hj
  have hh := CycleQ2SegreModularBasepoint.coordinate_power_mem (R := F109) j
  change (X j : Poly F109)^CycleQ2SegreModularBasepoint.degrees j ∈
    generatorIdeal (seedGenerators (57 : F109) 33) at hh
  have hm : (monomial (fullExponentOf e.val) 1 : Poly F109) =
      X j^CycleQ2SegreModularBasepoint.degrees j *
        monomial (fullExponentOf e.val-Finsupp.single j
          (CycleQ2SegreModularBasepoint.degrees j)) 1 := by
    rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ hh

theorem modular_homogeneous_mem (p : Poly F109) (hp : HG p (120,0)) :
    p ∈ generatorIdeal (seedGenerators (57 : F109) 33) := by
  rw [← fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial, mul_one] using
    Ideal.mul_mem_left (generatorIdeal (seedGenerators (57 : F109) 33))
      (C (p.coeff (fullExponentOf e.val))) (modular_monomial_mem e)

/-- The complete complex degree120 invariant piece lies in the ideal of
the actual raw matrix entries, h and G at r=57, i=Complex.I. -/
theorem complex_homogeneous_mem (p : Poly ℂ) (hp : HG p (120,0)) :
    p ∈ generatorIdeal (seedGenerators (57 : ℂ) Complex.I) := by
  have hmod : ∀ p : Poly F109, HG p (120,0) → p ∈ generatorIdeal
      (fun j => map reduction (seedGenerators (57 : GaussianInt) gaussianI j)) := by
    rw [seedGenerators_map, reduction_I, map_ofNat]
    exact modular_homogeneous_mem
  have h := gaussian_membership_transfer (seedGenerators (57 : GaussianInt) gaussianI)
    generatorDegree (generators_homogeneous _ _) 120 generatorDegree_le hmod p hp
  simpa only [seedGenerators_map, complex_I, map_ofNat] using h

def coordinatePower : Fin 5 → ℕ := ![120,120,120,120,60]

theorem coordinate_power_homogeneous (j : Fin 5) :
    HG (X j^coordinatePower j : Poly ℂ) (120,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem complex_coordinate_power_mem (j : Fin 5) :
    (X j : Poly ℂ)^coordinatePower j ∈
      generatorIdeal (seedGenerators (57 : ℂ) Complex.I) :=
  complex_homogeneous_mem _ (coordinate_power_homogeneous j)

abbrev ComplexSeedRing := SeedRing (57 : ℂ) Complex.I

def coordinate (j : Fin 5) : ComplexSeedRing := Ideal.Quotient.mk _ (X j)
def matrix : Matrix (Fin 3) (Fin 3) ComplexSeedRing := seedQuotientMatrix 57 Complex.I
def entryIdeal : Ideal ComplexSeedRing :=
  Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => matrix ij.1 ij.2))

theorem quotient_h :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (smoothH Complex.I) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem quotient_g :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (seedG (57 : ℂ)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (CycleQ2IncidenceFirstOrder.smoothSeed_mem_iff_linkage (57 : ℂ) Complex.I).mpr
  exact ⟨0,1,by simp⟩

theorem generator_quotient_mem (j : Fin 11) :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
      (seedGenerators (57 : ℂ) Complex.I j) ∈ entryIdeal := by
  have hm (a b : Fin 3) : matrix a b ∈ entryIdeal :=
    Ideal.subset_span (Set.mem_range_self (a,b))
  fin_cases j
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · change Ideal.Quotient.mk _ (smoothH Complex.I) ∈ _
    rw [quotient_h]
    exact Ideal.zero_mem _
  · change Ideal.Quotient.mk _ (seedG (57 : ℂ)) ∈ _
    rw [quotient_g]
    exact Ideal.zero_mem _

/-- Characteristic-zero coordinate-power membership in the actual seed
quotient, obtained nonconstructively from the verified modular certificate. -/
theorem seed_coordinate_power_mem (j : Fin 5) : coordinate j^coordinatePower j ∈ entryIdeal := by
  let φ := Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57 : ℂ) Complex.I))
  have hle : generatorIdeal (seedGenerators (57 : ℂ) Complex.I) ≤ entryIdeal.comap φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact generator_quotient_mem j
  have h := hle (complex_coordinate_power_mem j)
  change φ ((X j : Poly ℂ)^coordinatePower j) ∈ entryIdeal at h
  simpa only [map_pow, φ, coordinate] using h

theorem prime_pivot_cover (P : Ideal ComplexSeedRing) [P.IsPrime]
    (hx : ∃ j, coordinate j ∉ P) : ∃ i j, matrix i j ∉ P := by
  classical
  by_contra! hzero
  have hle : entryIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨ij,rfl⟩
    exact hzero ij.1 ij.2
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _ (hle (seed_coordinate_power_mem j)))

theorem field_pivot_cover {K : Type*} [Field K] (φ : ComplexSeedRing →+* K)
    (hx : ∃ j, φ (coordinate j) ≠ 0) : ∃ i j, IsUnit (φ (matrix i j)) :=
  CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
    matrix coordinate coordinatePower seed_coordinate_power_mem φ hx

theorem entries_generate_if_coordinate_unit {S : Type*} [CommRing S]
    (φ : ComplexSeedRing →+* S) (j : Fin 5) (hu : IsUnit (φ (coordinate j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (matrix ij.1 ij.2))) = ⊤ := by
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem j)
  have hunit : IsUnit (φ (coordinate j^coordinatePower j)) := by
    rw [map_pow]
    exact hu.pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hunit
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def] using ht

end CycleQ2SegreComplexBasepoint

#print axioms CycleQ2SegreComplexBasepoint.complex_homogeneous_mem
#print axioms CycleQ2SegreComplexBasepoint.seed_coordinate_power_mem
#print axioms CycleQ2SegreComplexBasepoint.prime_pivot_cover
#print axioms CycleQ2SegreComplexBasepoint.entries_generate_if_coordinate_unit
end
end


/- Component: continuation_3/cylinder_bridge/SegreFactorSequence.lean -/
section
/-! # The actual linear factor sequence

The factor map divides the literal numerator `v_i*b_j+a_i*w_j` by the
regular linkage element. Divisibility follows from the two factor ideals;
regularity makes the quotient unique and the map linear.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorSequence

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SegreFactorExact

variable {A : Type*} [CommRing A]

structure FactorData (A : Type*) [CommRing A] where
  leftIdeal : Ideal A
  rightIdeal : Ideal A
  linkage : A
  matrix : Matrix (Fin 3) (Fin 3) A
  left : Fin 3 → A
  right : Fin 3 → A
  left_mem : ∀ i, left i ∈ leftIdeal
  right_mem : ∀ j, right j ∈ rightIdeal
  product : ∀ i j, left i*right j=linkage*matrix i j
  ideals_product : leftIdeal*rightIdeal≤Ideal.span {linkage}
  regular : Function.Injective (fun z : A => linkage*z)
  cofactors_zero : CycleQ2SegreLocal.cofactors matrix=0
  entries_generate : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => matrix q.1 q.2))=⊤

variable (F : FactorData A)

abbrev FactorDomain := (Fin 3 → F.leftIdeal) × (Fin 3 → F.rightIdeal)

theorem numerator_divisible (v : FactorDomain F) (i j : Fin 3) :
    F.linkage ∣ (v.1 i : A)*F.right j+F.left i*(v.2 j : A) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.span {F.linkage}).add_mem
  · exact F.ideals_product (Ideal.mul_mem_mul (v.1 i).property (F.right_mem j))
  · exact F.ideals_product (Ideal.mul_mem_mul (F.left_mem i) (v.2 j).property)

def factorValue (v : FactorDomain F) : Matrix (Fin 3) (Fin 3) A :=
  fun i j => Classical.choose (numerator_divisible F v i j)

theorem linkage_factorValue (v : FactorDomain F) (i j : Fin 3) :
    F.linkage*factorValue F v i j=(v.1 i : A)*F.right j+F.left i*(v.2 j : A) :=
  (Classical.choose_spec (numerator_divisible F v i j)).symm

def factorMap : FactorDomain F →ₗ[A] Matrix (Fin 3) (Fin 3) A where
  toFun := factorValue F
  map_add' v w := by
    funext i j
    apply F.regular
    change F.linkage*factorValue F (v+w) i j=
      F.linkage*(factorValue F v i j+factorValue F w i j)
    rw [mul_add,linkage_factorValue,linkage_factorValue,linkage_factorValue]
    change ((v.1 i:A)+(w.1 i:A))*F.right j+F.left i*((v.2 j:A)+(w.2 j:A))=
      ((v.1 i:A)*F.right j+F.left i*(v.2 j:A))+
      ((w.1 i:A)*F.right j+F.left i*(w.2 j:A))
    ring
  map_smul' c v := by
    funext i j
    apply F.regular
    change F.linkage*factorValue F (c • v) i j=F.linkage*(c*factorValue F v i j)
    rw [show F.linkage*(c*factorValue F v i j)=c*(F.linkage*factorValue F v i j) by ring]
    rw [linkage_factorValue,linkage_factorValue]
    change (c*(v.1 i:A))*F.right j+F.left i*(c*(v.2 j:A))=
      c*((v.1 i:A)*F.right j+F.left i*(v.2 j:A))
    ring

theorem linkage_factorMap (v : FactorDomain F) (i j : Fin 3) :
    F.linkage*factorMap F v i j=(v.1 i:A)*F.right j+F.left i*(v.2 j:A) :=
  linkage_factorValue F v i j

def gaugeMap : A →ₗ[A] FactorDomain F where
  toFun c := (fun i => ⟨c*F.left i,F.leftIdeal.mul_mem_left c (F.left_mem i)⟩,
    fun j => ⟨-(c*F.right j),F.rightIdeal.neg_mem
      (F.rightIdeal.mul_mem_left c (F.right_mem j))⟩)
  map_add' c d := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      change (c+d)*F.left i=c*F.left i+d*F.left i
      ring
    · funext j
      apply Subtype.ext
      change -((c+d)*F.right j)=-(c*F.right j)+-(d*F.right j)
      ring
  map_smul' c d := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      change (c*d)*F.left i=c*(d*F.left i)
      ring
    · funext j
      apply Subtype.ext
      change -((c*d)*F.right j)=c*(-(d*F.right j))
      ring

theorem factorMap_gaugeMap (c : A) : factorMap F (gaugeMap F c)=0 := by
  funext i j
  change factorMap F (gaugeMap F c) i j=0
  apply F.regular
  calc
    F.linkage*factorMap F (gaugeMap F c) i j =
        ((gaugeMap F c).1 i:A)*F.right j+F.left i*((gaugeMap F c).2 j:A) :=
      linkage_factorMap F (gaugeMap F c) i j
    _ = F.linkage*0 := by
      change (c*F.left i)*F.right j+F.left i*(-(c*F.right j))=F.linkage*0
      ring

theorem gaugeMap_injective : Function.Injective (gaugeMap F) := by
  intro c d h
  apply gauge_scalar_unique F.linkage F.regular F.matrix F.left F.right
    F.product F.entries_generate c d
  intro i
  exact congrArg (fun v : FactorDomain F => (v.1 i : A)) h

theorem ker_factorMap_eq_range_gaugeMap :
    LinearMap.ker (factorMap F)=LinearMap.range (gaugeMap F) := by
  apply le_antisymm
  · intro v hv
    have hz : ∀ i j, (v.1 i:A)*F.right j+F.left i*(v.2 j:A)=0 := by
      intro i j
      have hh := linkage_factorMap F v i j
      have he : factorMap F v=0 := hv
      have hij : factorMap F v i j=0 :=
        congrArg (fun N : Matrix (Fin 3) (Fin 3) A => N i j) he
      rw [hij,mul_zero] at hh
      exact hh.symm
    obtain ⟨c,hc,hc'⟩ := factor_gauge F.leftIdeal F.rightIdeal F.linkage F.regular
      F.matrix F.left F.right (fun i => (v.1 i:A)) (fun j => (v.2 j:A))
      F.right_mem (fun i => (v.1 i).property) F.product F.ideals_product
      F.entries_generate hz
    refine ⟨c,?_⟩
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact (hc i).symm
    · funext j
      apply Subtype.ext
      exact (hc' j).symm
  · rintro v ⟨c,rfl⟩
    exact factorMap_gaugeMap F c

theorem range_factorMap_eq_ker_differential :
    LinearMap.range (factorMap F)=LinearMap.ker (cofactorDifferentialLinear F.matrix) := by
  apply le_antisymm
  · rintro N ⟨v,rfl⟩
    apply factor_lift_in_kernel F.linkage F.regular F.matrix (factorMap F v)
      F.left F.right (fun i => (v.1 i:A)) (fun j => (v.2 j:A)) F.product
    intro i j
    exact (linkage_factorMap F v i j).symm
  · intro N hN
    obtain ⟨v,w,hv,hw,he⟩ := exists_factor_lift F.leftIdeal F.rightIdeal F.linkage
      F.matrix N F.left F.right F.left_mem F.right_mem F.product
      F.cofactors_zero hN F.entries_generate
    let V : FactorDomain F := (fun i => ⟨v i,hv i⟩,fun j => ⟨w j,hw j⟩)
    refine ⟨V,?_⟩
    funext i j
    apply F.regular
    calc
      F.linkage*factorMap F V i j = (V.1 i:A)*F.right j+F.left i*(V.2 j:A) :=
        linkage_factorMap F V i j
      _ = F.linkage*N i j := he i j

end CycleQ2SegreFactorSequence

#print axioms CycleQ2SegreFactorSequence.gaugeMap_injective
#print axioms CycleQ2SegreFactorSequence.ker_factorMap_eq_range_gaugeMap
#print axioms CycleQ2SegreFactorSequence.range_factorMap_eq_ker_differential
end
end


/- Component: continuation_3/SegreModularActionSemantics.lean -/
section
/-! # Modular detector products are the actual incidence normal forms

The executable action tables are compared in the actual seed quotient,
and their checked standard support makes that comparison an equality of
the unique normal representatives. This binds each computed dot product
to the original polynomial and its original coefficient functional.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularActionSemantics

open MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceGaussianArithmetic CycleQ2SegreGaussianActionData

def actionTable : Fin 3 → Fin 3 → ℕ → ℕ → Towers :=
  ![![action00,action01,action02],![action10,action11,action12],![action20,action21,action22]]

theorem action_standard (i j a b : Fin 3) :
    standardPolynomial (flattenTowersData (actionTable i j a b))=true := by
  fin_cases i <;> fin_cases j
  · exact action00_standard a b
  · exact action01_standard a b
  · exact action02_standard a b
  · exact action10_standard a b
  · exact action11_standard a b
  · exact action12_standard a b
  · exact action20_standard a b
  · exact action21_standard a b
  · exact action22_standard a b

theorem flatten_action_value (i j : Fin 3) (a b : ℕ) :
    eval CycleQ2SegreModularGaussianBinding.coeffHom (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      (flattenTowersData (actionTable i j a b))=CycleQ2SegreModularGaussianBinding.value (actionTable i j a b) := by
  rw [flattenTowersData_eq,eval_flattenTowers]
  rfl

theorem quotient_action_value (i j : Fin 3) (a b : ℕ) :
    CycleQ2SegreModularGaussianBinding.quotientMap (CycleQ2SegreModularGaussianBinding.value (actionTable i j a b))=
      CycleQ2SegreModularGaussianBinding.quotientMap (rawSeedMatrix (57:F109) i j)*
        CycleQ2SegreModularGaussianBinding.quotientVariables 0^a*CycleQ2SegreModularGaussianBinding.quotientVariables 4^b := by
  rw [CycleQ2SegreModularGaussianBinding.map_value,←CycleQ2SegreModularGaussianBinding.value_rawMatrix,CycleQ2SegreModularGaussianBinding.map_value]
  fin_cases i <;> fin_cases j
  · exact eval_action00 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action01 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action02 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action10 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action11 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action12 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action20 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action21 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b
  · exact eval_action22 CycleQ2SegreModularGaussianBinding.quotientCoeffHom CycleQ2SegreModularGaussianBinding.quotientVariables (CycleQ2SegreModularGaussianBinding.quotientVariables 4)
      (CycleQ2SegreModularGaussianBinding.quotientVariables 0) (CycleQ2SegreModularGaussianBinding.quotientVariables 1) CycleQ2SegreModularGaussianBinding.quotient_z_relation CycleQ2SegreModularGaussianBinding.quotient_w_relation a b

theorem monomial_split (a b u v c : ℕ) :
    (MvPolynomial.monomial (tupleExponent (a,u,v,c,b)) 1 : CycleQ2SegreModularGaussianBinding.P)=
      MvPolynomial.monomial (tupleExponent (0,u,v,c,0)) 1*MvPolynomial.X 0^a*MvPolynomial.X 4^b := by
  rw [←monomial_variables,←monomial_variables]
  simp only [CycleQ2SparseGaussianPolynomial.monomial,pow_zero,one_mul,mul_one]
  ring

theorem nf_action_product (i j a b : Fin 3) (u v c : ℕ) :
    CycleQ2GenericEntryCoefficientBinding.nf (57:F109) 33
      (rawSeedMatrix (57:F109) i j*MvPolynomial.monomial
        (tupleExponent (a.val,u,v,c,b.val)) 1)=
      MvPolynomial.monomial (tupleExponent (0,u,v,c,0)) 1*CycleQ2SegreModularGaussianBinding.value (actionTable i j a b) := by
  apply CycleQ2GenericEntryCoefficientBinding.nf_eq_of_standard_and_quotient (57:F109) 33
  · rw [←flatten_action_value]
    exact standardPolynomial_free_product reduction u v c
      (flattenTowersData (actionTable i j a b)) (action_standard i j a b)
  · rw [←CycleQ2SegreModularGaussianBinding.pointIdeal_eq_equationsIdeal]
    change CycleQ2SegreModularGaussianBinding.quotientMap (rawSeedMatrix (57:F109) i j*
      MvPolynomial.monomial (tupleExponent (a.val,u,v,c,b.val)) 1)=
      CycleQ2SegreModularGaussianBinding.quotientMap (MvPolynomial.monomial (tupleExponent (0,u,v,c,0)) 1*
        CycleQ2SegreModularGaussianBinding.value (actionTable i j a b))
    rw [monomial_split]
    simp only [map_mul,map_pow,quotient_action_value,CycleQ2SegreModularGaussianBinding.quotientVariables]
    ring

/-- An actual sparse dot-product check is a check of the coefficient
functional on the original seed-matrix product normal form. -/
theorem dot_flat_action_eq_nf (W : WeightData) (r s i j a b : Fin 3) (u v : ℕ) :
    (dot W r s (0,u,v,14-(a.val+u+v+2*b.val),0)
      (flattenTowersData (actionTable i j a b)) : F109)=
      functional W r s
        (CycleQ2GenericEntryCoefficientBinding.nf (57:F109) 33
          (rawSeedMatrix (57:F109) i j*MvPolynomial.monomial
            (tupleExponent (a.val,u,v,14-(a.val+u+v+2*b.val),b.val)) 1)) := by
  rw [cast_dot_product,nf_action_product]
  exact congrArg (fun p : CycleQ2SegreModularGaussianBinding.P =>
    functional W r s (MvPolynomial.monomial
      (tupleExponent (0,u,v,14-(a.val+u+v+2*b.val),0)) 1*p))
    (flatten_action_value i j a b)

end CycleQ2SegreModularActionSemantics

#print axioms CycleQ2SegreModularActionSemantics.nf_action_product
#print axioms CycleQ2SegreModularActionSemantics.dot_flat_action_eq_nf
end
end


/- Component: continuation_3/SegreModularCubicPairingChecks0.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing0_0 : cubicDot weights0 0=cubicPairing 0 0 := by
  decide +kernel

theorem pairing0_1 : cubicDot weights0 1=cubicPairing 0 1 := by
  decide +kernel

theorem pairing0_2 : cubicDot weights0 2=cubicPairing 0 2 := by
  decide +kernel

theorem pairing0_3 : cubicDot weights0 3=cubicPairing 0 3 := by
  decide +kernel

theorem pairing0_4 : cubicDot weights0 4=cubicPairing 0 4 := by
  decide +kernel

theorem pairing0_5 : cubicDot weights0 5=cubicPairing 0 5 := by
  decide +kernel

theorem pairing0_6 : cubicDot weights0 6=cubicPairing 0 6 := by
  decide +kernel

theorem pairing0_7 : cubicDot weights0 7=cubicPairing 0 7 := by
  decide +kernel

theorem pairing0_8 : cubicDot weights0 8=cubicPairing 0 8 := by
  decide +kernel

theorem pairing0 (c : Fin 9) : cubicDot weights0 c=cubicPairing 0 c := by
  fin_cases c
  · exact pairing0_0
  · exact pairing0_1
  · exact pairing0_2
  · exact pairing0_3
  · exact pairing0_4
  · exact pairing0_5
  · exact pairing0_6
  · exact pairing0_7
  · exact pairing0_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing0
end


/- Component: continuation_3/SegreModularCubicPairingChecks1.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing1_0 : cubicDot weights1 0=cubicPairing 1 0 := by
  decide +kernel

theorem pairing1_1 : cubicDot weights1 1=cubicPairing 1 1 := by
  decide +kernel

theorem pairing1_2 : cubicDot weights1 2=cubicPairing 1 2 := by
  decide +kernel

theorem pairing1_3 : cubicDot weights1 3=cubicPairing 1 3 := by
  decide +kernel

theorem pairing1_4 : cubicDot weights1 4=cubicPairing 1 4 := by
  decide +kernel

theorem pairing1_5 : cubicDot weights1 5=cubicPairing 1 5 := by
  decide +kernel

theorem pairing1_6 : cubicDot weights1 6=cubicPairing 1 6 := by
  decide +kernel

theorem pairing1_7 : cubicDot weights1 7=cubicPairing 1 7 := by
  decide +kernel

theorem pairing1_8 : cubicDot weights1 8=cubicPairing 1 8 := by
  decide +kernel

theorem pairing1 (c : Fin 9) : cubicDot weights1 c=cubicPairing 1 c := by
  fin_cases c
  · exact pairing1_0
  · exact pairing1_1
  · exact pairing1_2
  · exact pairing1_3
  · exact pairing1_4
  · exact pairing1_5
  · exact pairing1_6
  · exact pairing1_7
  · exact pairing1_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing1
end


/- Component: continuation_3/SegreModularCubicPairingChecks2.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing2_0 : cubicDot weights2 0=cubicPairing 2 0 := by
  decide +kernel

theorem pairing2_1 : cubicDot weights2 1=cubicPairing 2 1 := by
  decide +kernel

theorem pairing2_2 : cubicDot weights2 2=cubicPairing 2 2 := by
  decide +kernel

theorem pairing2_3 : cubicDot weights2 3=cubicPairing 2 3 := by
  decide +kernel

theorem pairing2_4 : cubicDot weights2 4=cubicPairing 2 4 := by
  decide +kernel

theorem pairing2_5 : cubicDot weights2 5=cubicPairing 2 5 := by
  decide +kernel

theorem pairing2_6 : cubicDot weights2 6=cubicPairing 2 6 := by
  decide +kernel

theorem pairing2_7 : cubicDot weights2 7=cubicPairing 2 7 := by
  decide +kernel

theorem pairing2_8 : cubicDot weights2 8=cubicPairing 2 8 := by
  decide +kernel

theorem pairing2 (c : Fin 9) : cubicDot weights2 c=cubicPairing 2 c := by
  fin_cases c
  · exact pairing2_0
  · exact pairing2_1
  · exact pairing2_2
  · exact pairing2_3
  · exact pairing2_4
  · exact pairing2_5
  · exact pairing2_6
  · exact pairing2_7
  · exact pairing2_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing2
end


/- Component: continuation_3/SegreModularCubicPairingChecks3.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing3_0 : cubicDot weights3 0=cubicPairing 3 0 := by
  decide +kernel

theorem pairing3_1 : cubicDot weights3 1=cubicPairing 3 1 := by
  decide +kernel

theorem pairing3_2 : cubicDot weights3 2=cubicPairing 3 2 := by
  decide +kernel

theorem pairing3_3 : cubicDot weights3 3=cubicPairing 3 3 := by
  decide +kernel

theorem pairing3_4 : cubicDot weights3 4=cubicPairing 3 4 := by
  decide +kernel

theorem pairing3_5 : cubicDot weights3 5=cubicPairing 3 5 := by
  decide +kernel

theorem pairing3_6 : cubicDot weights3 6=cubicPairing 3 6 := by
  decide +kernel

theorem pairing3_7 : cubicDot weights3 7=cubicPairing 3 7 := by
  decide +kernel

theorem pairing3_8 : cubicDot weights3 8=cubicPairing 3 8 := by
  decide +kernel

theorem pairing3 (c : Fin 9) : cubicDot weights3 c=cubicPairing 3 c := by
  fin_cases c
  · exact pairing3_0
  · exact pairing3_1
  · exact pairing3_2
  · exact pairing3_3
  · exact pairing3_4
  · exact pairing3_5
  · exact pairing3_6
  · exact pairing3_7
  · exact pairing3_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing3
end


/- Component: continuation_3/SegreModularCubicPairingChecks4.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing4_0 : cubicDot weights4 0=cubicPairing 4 0 := by
  decide +kernel

theorem pairing4_1 : cubicDot weights4 1=cubicPairing 4 1 := by
  decide +kernel

theorem pairing4_2 : cubicDot weights4 2=cubicPairing 4 2 := by
  decide +kernel

theorem pairing4_3 : cubicDot weights4 3=cubicPairing 4 3 := by
  decide +kernel

theorem pairing4_4 : cubicDot weights4 4=cubicPairing 4 4 := by
  decide +kernel

theorem pairing4_5 : cubicDot weights4 5=cubicPairing 4 5 := by
  decide +kernel

theorem pairing4_6 : cubicDot weights4 6=cubicPairing 4 6 := by
  decide +kernel

theorem pairing4_7 : cubicDot weights4 7=cubicPairing 4 7 := by
  decide +kernel

theorem pairing4_8 : cubicDot weights4 8=cubicPairing 4 8 := by
  decide +kernel

theorem pairing4 (c : Fin 9) : cubicDot weights4 c=cubicPairing 4 c := by
  fin_cases c
  · exact pairing4_0
  · exact pairing4_1
  · exact pairing4_2
  · exact pairing4_3
  · exact pairing4_4
  · exact pairing4_5
  · exact pairing4_6
  · exact pairing4_7
  · exact pairing4_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing4
end


/- Component: continuation_3/SegreModularCubicPairingChecks5.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing5_0 : cubicDot weights5 0=cubicPairing 5 0 := by
  decide +kernel

theorem pairing5_1 : cubicDot weights5 1=cubicPairing 5 1 := by
  decide +kernel

theorem pairing5_2 : cubicDot weights5 2=cubicPairing 5 2 := by
  decide +kernel

theorem pairing5_3 : cubicDot weights5 3=cubicPairing 5 3 := by
  decide +kernel

theorem pairing5_4 : cubicDot weights5 4=cubicPairing 5 4 := by
  decide +kernel

theorem pairing5_5 : cubicDot weights5 5=cubicPairing 5 5 := by
  decide +kernel

theorem pairing5_6 : cubicDot weights5 6=cubicPairing 5 6 := by
  decide +kernel

theorem pairing5_7 : cubicDot weights5 7=cubicPairing 5 7 := by
  decide +kernel

theorem pairing5_8 : cubicDot weights5 8=cubicPairing 5 8 := by
  decide +kernel

theorem pairing5 (c : Fin 9) : cubicDot weights5 c=cubicPairing 5 c := by
  fin_cases c
  · exact pairing5_0
  · exact pairing5_1
  · exact pairing5_2
  · exact pairing5_3
  · exact pairing5_4
  · exact pairing5_5
  · exact pairing5_6
  · exact pairing5_7
  · exact pairing5_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing5
end


/- Component: continuation_3/SegreModularCubicPairingChecks6.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem pairing6_0 : cubicDot weights6 0=cubicPairing 6 0 := by
  decide +kernel

theorem pairing6_1 : cubicDot weights6 1=cubicPairing 6 1 := by
  decide +kernel

theorem pairing6_2 : cubicDot weights6 2=cubicPairing 6 2 := by
  decide +kernel

theorem pairing6_3 : cubicDot weights6 3=cubicPairing 6 3 := by
  decide +kernel

theorem pairing6_4 : cubicDot weights6 4=cubicPairing 6 4 := by
  decide +kernel

theorem pairing6_5 : cubicDot weights6 5=cubicPairing 6 5 := by
  decide +kernel

theorem pairing6_6 : cubicDot weights6 6=cubicPairing 6 6 := by
  decide +kernel

theorem pairing6_7 : cubicDot weights6 7=cubicPairing 6 7 := by
  decide +kernel

theorem pairing6_8 : cubicDot weights6 8=cubicPairing 6 8 := by
  decide +kernel

theorem pairing6 (c : Fin 9) : cubicDot weights6 c=cubicPairing 6 c := by
  fin_cases c
  · exact pairing6_0
  · exact pairing6_1
  · exact pairing6_2
  · exact pairing6_3
  · exact pairing6_4
  · exact pairing6_5
  · exact pairing6_6
  · exact pairing6_7
  · exact pairing6_8

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.pairing6
end


/- Component: continuation_3/SegreModularCubicSemantics.lean -/
section
/-! # The computed cubic table is the actual cofactor-quotient normal form

The checked table identities hold in the actual seed quotient. Standardness
then identifies each value with the unique incidence normal representative.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularCubicSemantics

open Matrix MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceGaussianArithmetic CycleQ2GenericEntryCoefficientBinding
  CycleQ2SegreModularCubicData CycleQ2SegreModularCubicStandard
  CycleQ2SegreModularCubicMonomialBinding CycleQ2SegreModularGaussianBinding
  CycleQ2SegreModularDetectorData CycleQ2SegreModularDetectorMatrixBinding

theorem literalQ_eq (s : Fin 3) : literalQ s=quotientTowers 0 s := by
  fin_cases s <;> rfl

theorem cubicTable_standard (s : Fin 3) (q : Fin 9) :
    FullStandard (value (cubicTable s q)) :=
  (goodTowers_evaluation reduction 28 (cubicTable s q) (cubicTable_good s q)).1

theorem quotient_cubic_value (s : Fin 3) (q : Fin 9) :
    quotientMap (value (cubicTable s q))=
      quotientMap (MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109)*
        smoothK 33*rawCofactorQuotient 57 0 s) := by
  have h := eval_cubicTable quotientCoeffHom quotientVariables (quotientVariables 4)
    (quotientVariables 0) (quotientVariables 1) quotient_z_relation quotient_w_relation s q
  change quotientValue (cubicTable s q)=quotientValue (monomialCubic q)*
    quotientValue CycleQ2SegreGaussianTangentData.k*quotientValue (literalQ s) at h
  rw [←map_value,←map_value,←map_value,←map_value] at h
  rw [value_monomialCubic,value_k,literalQ_eq,value_rawQuotient] at h
  simpa only [map_mul] using h

theorem nf_cubic_product (s : Fin 3) (q : Fin 9) :
    nf (57:F109) 33
      (MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109)*
        smoothK 33*rawCofactorQuotient 57 0 s)=value (cubicTable s q) := by
  apply nf_eq_of_standard_and_quotient (57:F109) 33 (cubicTable_standard s q)
  rw [←pointIdeal_eq_equationsIdeal]
  exact (quotient_cubic_value s q).symm

theorem dot_cubic_eq_nf (W : WeightData) (s : Fin 3) (q : Fin 9) :
    (dot W 0 s (0,0,0,0,0) (flattenTowersData (cubicTable s q)) : F109)=
      functional W 0 s
        (nf (57:F109) 33
          (MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109)*
            smoothK 33*rawCofactorQuotient 57 0 s)) := by
  have hm : (MvPolynomial.monomial (tupleExponent (0,0,0,0,0)) (1:F109) :
      CycleQ2SegreModularGaussianBinding.P)=1 := by
    rw [←monomial_variables]
    simp only [CycleQ2SparseGaussianPolynomial.monomial,pow_zero,mul_one]
  rw [cast_dot_product,hm,one_mul,nf_cubic_product]
  exact congrArg (fun p : CycleQ2SegreModularGaussianBinding.P => functional W 0 s p)
    (flatten_value (cubicTable s q))

theorem detector_cubic_numeric (k : Fin 7) (q : Fin 9) :
    (detectorMatrix*selectedCubicBlock) k q=
      ∑s : Fin 3,(dot (weights k) 0 s (0,0,0,0,0)
        (flattenTowersData (cubicTable s q)) : F109) := by
  rw [detector_cubic_column]
  apply Finset.sum_congr rfl
  intro s _
  exact (dot_cubic_eq_nf (weights k) s q).symm

end CycleQ2SegreModularCubicSemantics

#print axioms CycleQ2SegreModularCubicSemantics.nf_cubic_product
#print axioms CycleQ2SegreModularCubicSemantics.detector_cubic_numeric
end
end


/- Component: continuation_3/SegreModularDetectorCheckSoundness.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularDetectorExpressions
open CycleQ2SparseModularFunctional

def SignedInput := Fin 3 → Fin 3 → Fin 3 → F

def signed00 (f : SignedInput) : F := 0

def signed01 (f : SignedInput) : F := 0

def signed02 (f : SignedInput) : F := 0

def signed10 (f : SignedInput) : F := -(f 1 2 2) + f 2 2 1

def signed11 (f : SignedInput) : F := f 0 2 2 + -(f 2 2 0)

def signed12 (f : SignedInput) : F := -(f 0 2 1) + f 1 2 0

def signed20 (f : SignedInput) : F := f 1 1 2 + -(f 2 1 1)

def signed21 (f : SignedInput) : F := -(f 0 1 2) + f 2 1 0

def signed22 (f : SignedInput) : F := f 0 1 1 + -(f 1 1 0)

def signedEntry : Fin 3 → Fin 3 → SignedInput → F :=
  ![![signed00, signed01, signed02], ![signed10, signed11, signed12], ![signed20, signed21, signed22]]

theorem cast_entryDot00 (W : WeightData) (a b u v : ℕ) :
    (entryDot00 W a b u v : F)=signed00
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  rfl

theorem cast_entryDot01 (W : WeightData) (a b u v : ℕ) :
    (entryDot01 W a b u v : F)=signed01
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  rfl

theorem cast_entryDot02 (W : WeightData) (a b u v : ℕ) :
    (entryDot02 W a b u v : F)=signed02
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  rfl

theorem cast_entryDot10 (W : WeightData) (a b u v : ℕ) :
    (entryDot10 W a b u v : F)=signed10
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot10,signed10,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot11 (W : WeightData) (a b u v : ℕ) :
    (entryDot11 W a b u v : F)=signed11
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot11,signed11,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot12 (W : WeightData) (a b u v : ℕ) :
    (entryDot12 W a b u v : F)=signed12
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot12,signed12,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot20 (W : WeightData) (a b u v : ℕ) :
    (entryDot20 W a b u v : F)=signed20
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot20,signed20,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot21 (W : WeightData) (a b u v : ℕ) :
    (entryDot21 W a b u v : F)=signed21
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot21,signed21,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot22 (W : WeightData) (a b u v : ℕ) :
    (entryDot22 W a b u v : F)=signed22
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  simp only [entryDot22,signed22,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (108 : F)= -1 by decide]
  ring

theorem cast_entryDot (i j : Fin 3) (W : WeightData) (a b u v : ℕ) :
    (entryDot i j W a b u v : F)=signedEntry i j
      (fun s k l => (dotAction W 0 s k l a b u v : F)) := by
  fin_cases i <;> fin_cases j
  · exact cast_entryDot00 W a b u v
  · exact cast_entryDot01 W a b u v
  · exact cast_entryDot02 W a b u v
  · exact cast_entryDot10 W a b u v
  · exact cast_entryDot11 W a b u v
  · exact cast_entryDot12 W a b u v
  · exact cast_entryDot20 W a b u v
  · exact cast_entryDot21 W a b u v
  · exact cast_entryDot22 W a b u v

 theorem entryDot_zero_of_block_check (W : WeightData) (i j : Fin 3) (a b : ℕ)
    (hc : checkEntryBlock W i j a b=true) (u v : ℕ) (hu : u<15) (hv : v<15)
    (ha : a+u+v+2*b≤14 ∧ (2*a+2*u+v)%3=0) : entryDot i j W a b u v=0 := by
  have h := List.all_eq_true.mp hc u (List.mem_range.mpr hu)
  have h := List.all_eq_true.mp h v (List.mem_range.mpr hv)
  have ht : allowed14 a b u v=true := by exact decide_eq_true ha
  simpa only [ht,ite_true,beq_iff_eq] using h

 theorem entryDot_zero_of_check (W : WeightData) (i j : Fin 3)
    (hc : checkEntry W i j=true) (a b u v : ℕ) (ha : a<3) (hb : b<3)
    (hu : u<15) (hv : v<15)
    (hvld : a+u+v+2*b≤14 ∧ (2*a+2*u+v)%3=0) : entryDot i j W a b u v=0 := by
  have h := List.all_eq_true.mp hc a (List.mem_range.mpr ha)
  have h := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  exact entryDot_zero_of_block_check W i j a b h u v hu hv hvld

end CycleQ2SegreModularDetectorExpressions
#print axioms CycleQ2SegreModularDetectorExpressions.cast_entryDot
#print axioms CycleQ2SegreModularDetectorExpressions.entryDot_zero_of_check
end


/- Component: continuation_3/SegreModularFastExpressions.lean -/
section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2SegreModularFastExpressions
open CycleQ2SparseModularFastDot CycleQ2SegreModularFastActions
  CycleQ2SegreModularDetectorExpressions CycleQ2SparseModularFunctional

def fastActionTable : Fin 3 → Fin 3 → Fin 3 → Fin 3 → List FastBlock :=
  ![![fun _ _ => [], fun _ _ => [], fun _ _ => []], ![fast10, fast11, fast12], ![fast20, fast21, fast22]]

theorem fastActionTable_1_eq (j a b : Fin 3) :
    flattenGrouped (fastActionTable 1 j a b)=encode (flatActionTable 1 j a b) := by
  fin_cases j <;> fin_cases a <;> fin_cases b
  · exact fast10_00_eq
  · exact fast10_01_eq
  · exact fast10_02_eq
  · exact fast10_10_eq
  · exact fast10_11_eq
  · exact fast10_12_eq
  · exact fast10_20_eq
  · exact fast10_21_eq
  · exact fast10_22_eq
  · exact fast11_00_eq
  · exact fast11_01_eq
  · exact fast11_02_eq
  · exact fast11_10_eq
  · exact fast11_11_eq
  · exact fast11_12_eq
  · exact fast11_20_eq
  · exact fast11_21_eq
  · exact fast11_22_eq
  · exact fast12_00_eq
  · exact fast12_01_eq
  · exact fast12_02_eq
  · exact fast12_10_eq
  · exact fast12_11_eq
  · exact fast12_12_eq
  · exact fast12_20_eq
  · exact fast12_21_eq
  · exact fast12_22_eq

theorem fastActionTable_2_eq (j a b : Fin 3) :
    flattenGrouped (fastActionTable 2 j a b)=encode (flatActionTable 2 j a b) := by
  fin_cases j <;> fin_cases a <;> fin_cases b
  · exact fast20_00_eq
  · exact fast20_01_eq
  · exact fast20_02_eq
  · exact fast20_10_eq
  · exact fast20_11_eq
  · exact fast20_12_eq
  · exact fast20_20_eq
  · exact fast20_21_eq
  · exact fast20_22_eq
  · exact fast21_00_eq
  · exact fast21_01_eq
  · exact fast21_02_eq
  · exact fast21_10_eq
  · exact fast21_11_eq
  · exact fast21_12_eq
  · exact fast21_20_eq
  · exact fast21_21_eq
  · exact fast21_22_eq
  · exact fast22_00_eq
  · exact fast22_01_eq
  · exact fast22_02_eq
  · exact fast22_10_eq
  · exact fast22_11_eq
  · exact fast22_12_eq
  · exact fast22_20_eq
  · exact fast22_21_eq
  · exact fast22_22_eq

def fastDotAction (W : WeightData) (r s i j a b : Fin 3) (u v : ℕ) : ℕ :=
  groupedDot W r s (u+29*v) (fastActionTable i j a b)

theorem fastDotAction_1_eq (W : WeightData) (r s j a b : Fin 3) (u v : ℕ) :
    fastDotAction W r s 1 j a b u v=dotAction W r s 1 j a b u v := by
  rw [fastDotAction,groupedDot_eq,fastActionTable_1_eq]
  exact fastDot_encode W r s u v (14-(a.val+u+v+2*b.val)) _

theorem fastDotAction_2_eq (W : WeightData) (r s j a b : Fin 3) (u v : ℕ) :
    fastDotAction W r s 2 j a b u v=dotAction W r s 2 j a b u v := by
  rw [fastDotAction,groupedDot_eq,fastActionTable_2_eq]
  exact fastDot_encode W r s u v (14-(a.val+u+v+2*b.val)) _

def fastEntry00 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (0)%109

def fastEntry01 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (0)%109

def fastEntry02 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (0)%109

def fastEntry10 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (108*fastDotAction W 0 1 2 2 a b u v + fastDotAction W 0 2 2 1 a b u v)%109

def fastEntry11 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (fastDotAction W 0 0 2 2 a b u v + 108*fastDotAction W 0 2 2 0 a b u v)%109

def fastEntry12 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (108*fastDotAction W 0 0 2 1 a b u v + fastDotAction W 0 1 2 0 a b u v)%109

def fastEntry20 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (fastDotAction W 0 1 1 2 a b u v + 108*fastDotAction W 0 2 1 1 a b u v)%109

def fastEntry21 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (108*fastDotAction W 0 0 1 2 a b u v + fastDotAction W 0 2 1 0 a b u v)%109

def fastEntry22 (W : WeightData) (a b : Fin 3) (u v : ℕ) : ℕ :=
  (fastDotAction W 0 0 1 1 a b u v + 108*fastDotAction W 0 1 1 0 a b u v)%109

def fastEntry : Fin 3 → Fin 3 → WeightData → Fin 3 → Fin 3 → ℕ → ℕ → ℕ :=
  ![![fastEntry00, fastEntry01, fastEntry02], ![fastEntry10, fastEntry11, fastEntry12], ![fastEntry20, fastEntry21, fastEntry22]]

theorem fastEntry_eq (i j : Fin 3) (W : WeightData) (a b : Fin 3) (u v : ℕ) :
    fastEntry i j W a b u v=entryDot i j W a b u v := by
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · change fastEntry10 W a b u v=entryDot10 W a b u v
    simp only [fastEntry10,entryDot10,fastDotAction_2_eq]
  · change fastEntry11 W a b u v=entryDot11 W a b u v
    simp only [fastEntry11,entryDot11,fastDotAction_2_eq]
  · change fastEntry12 W a b u v=entryDot12 W a b u v
    simp only [fastEntry12,entryDot12,fastDotAction_2_eq]
  · change fastEntry20 W a b u v=entryDot20 W a b u v
    simp only [fastEntry20,entryDot20,fastDotAction_1_eq]
  · change fastEntry21 W a b u v=entryDot21 W a b u v
    simp only [fastEntry21,entryDot21,fastDotAction_1_eq]
  · change fastEntry22 W a b u v=entryDot22 W a b u v
    simp only [fastEntry22,entryDot22,fastDotAction_1_eq]

def fastCheckRow (W : WeightData) (i j a b : Fin 3) (u : ℕ) : Bool :=
  (List.range 15).all (fun v => if allowed14 a b u v then fastEntry i j W a b u v == 0 else true)

theorem fastCheckRow_eq (W : WeightData) (i j a b : Fin 3) (u : ℕ) :
    fastCheckRow W i j a b u=checkEntryRow W i j a b u := by
  simp only [fastCheckRow,checkEntryRow,fastEntry_eq]

theorem checkEntryRow_of_fast (W : WeightData) (i j a b : Fin 3) (u : ℕ)
    (h : fastCheckRow W i j a b u=true) : checkEntryRow W i j a b u=true := by
  rwa [fastCheckRow_eq] at h

end CycleQ2SegreModularFastExpressions
#print axioms CycleQ2SegreModularFastExpressions.checkEntryRow_of_fast
end


/- Component: continuation_3/CurveRestrictionCoordinates.lean -/
section
/-! The right normal-form chart is an explicit coordinate algebra equivalence
of the original complete-intersection curve, not merely a parametrization. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction
open MvPolynomial CycleQ2IncidenceEquations

abbrev CP := CurvePoly ℂ

def originalCubic (ι : ℂ) : CP :=
  X 0^3+X 2^3+X 1*X 2*X 3+X 0*X 2*X 3+X 0*X 1^2+
    C (1-ι)*X 3^3-C ι*X 1^3

def originalQuadric (s : Side) (r : ℂ) : CP :=
  match s with
  | .left => X 0^2-C r*X 1*X 3
  | .right => X 0^2+X 2^2

def originalCurveIdeal (s : Side) (r ι : ℂ) : Ideal CP :=
  Ideal.span {originalQuadric s r,originalCubic ι}

def coordinateValues (s : Side) : Fin 4 → CP :=
  match s with
  | .left => X
  | .right => ![X 0+X 2,2*X 1,X 0-X 2,2*X 3]

def inverseCoordinateValues (s : Side) : Fin 4 → CP :=
  match s with
  | .left => X
  | .right => ![C ((2:ℂ)⁻¹)*(X 0+X 2),C ((2:ℂ)⁻¹)*X 1,
      C ((2:ℂ)⁻¹)*(X 0-X 2),C ((2:ℂ)⁻¹)*X 3]

def coordinateMap (s : Side) : CP →ₐ[ℂ] CP := aeval (coordinateValues s)
def inverseCoordinateMap (s : Side) : CP →ₐ[ℂ] CP := aeval (inverseCoordinateValues s)

private theorem half_relation : (C ((2:ℂ)⁻¹) : CP)*2=1 := by
  rw [←map_ofNat (C : ℂ →+* CP) 2,←map_mul]
  norm_num

theorem coordinateMap_inverse (s : Side) :
    (coordinateMap s).comp (inverseCoordinateMap s)=AlgHom.id ℂ CP := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s
  · simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues]
  · fin_cases i <;>
      simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues,
        Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat]
    · linear_combination (X 0:CP)*half_relation
    · linear_combination (X 1:CP)*half_relation
    · linear_combination (X 2:CP)*half_relation
    · linear_combination (X 3:CP)*half_relation

theorem inverse_coordinateMap (s : Side) :
    (inverseCoordinateMap s).comp (coordinateMap s)=AlgHom.id ℂ CP := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s
  · simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues]
  · fin_cases i <;>
      simp [coordinateMap,inverseCoordinateMap,coordinateValues,inverseCoordinateValues,
        Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat]
    · linear_combination (X 0:CP)*half_relation
    · linear_combination (X 1:CP)*half_relation
    · linear_combination (X 2:CP)*half_relation
    · linear_combination (X 3:CP)*half_relation

def coordinateEquiv (s : Side) : CP ≃ₐ[ℂ] CP :=
  AlgEquiv.ofAlgHom (coordinateMap s) (inverseCoordinateMap s)
    (coordinateMap_inverse s) (inverse_coordinateMap s)

theorem coordinateMap_originalQuadric_left (r : ℂ) :
    coordinateMap .left (originalQuadric .left r)=quadric .left r := by
  simp [coordinateMap,coordinateValues,originalQuadric,quadric]

theorem coordinateMap_originalQuadric_right (r : ℂ) :
    coordinateMap .right (originalQuadric .right r)=2*quadric .right r := by
  simp [coordinateMap,coordinateValues,originalQuadric,quadric,
    Matrix.cons_val_succ,Fin.reduceSucc]
  ring

theorem coordinateMap_originalCubic_left (r ι : ℂ) :
    coordinateMap .left (originalCubic ι)=cubic .left r ι+X 0*quadric .left r := by
  simp [coordinateMap,coordinateValues,originalCubic,cubic,quadric]
  ring

theorem coordinateMap_originalCubic_right (r ι : ℂ) :
    coordinateMap .right (originalCubic ι)=
      -4*cubic .right r ι+(6*X 0-2*X 3)*quadric .right r := by
  simp [coordinateMap,coordinateValues,originalCubic,cubic,quadric,map_ofNat,
    Matrix.cons_val_succ,Fin.reduceSucc]
  ring

private theorem span_pair_scale_first {A : Type*} [CommRing A]
    (q h u : A) (hu : IsUnit u) : Ideal.span {u*q,h}=Ideal.span {q,h} := by
  rw [Ideal.span_insert,Ideal.span_singleton_mul_left_unit hu,←Ideal.span_insert]

private theorem span_pair_scale_second {A : Type*} [CommRing A]
    (q h u : A) (hu : IsUnit u) : Ideal.span {q,u*h}=Ideal.span {q,h} := by
  rw [Ideal.span_pair_comm,span_pair_scale_first _ _ _ hu,Ideal.span_pair_comm]

theorem originalCurveIdeal_map (s : Side) (r ι : ℂ) :
    curveIdeal s r ι=(originalCurveIdeal s r ι).map (coordinateEquiv s).toRingHom := by
  simp only [originalCurveIdeal,Ideal.map_span,Set.image_insert_eq,Set.image_singleton]
  change Ideal.span {quadric s r,cubic s r ι}=
    Ideal.span {coordinateMap s (originalQuadric s r),coordinateMap s (originalCubic ι)}
  cases s
  · rw [coordinateMap_originalQuadric_left,coordinateMap_originalCubic_left,
      Ideal.span_pair_add_mul_left]
  · rw [coordinateMap_originalQuadric_right,coordinateMap_originalCubic_right]
    have htwo : IsUnit (2:CP) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℂ)≠0)).map (C : ℂ →+* CP)
    have hfour : IsUnit (-4:CP) := by
      simpa only [map_neg,map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (-4:ℂ)≠0)).map (C : ℂ →+* CP)
    rw [span_pair_scale_first _ _ _ htwo,Ideal.span_pair_add_mul_left,
      span_pair_scale_second _ _ _ hfour]

/-- An explicit algebra equivalence with the original curve quotient. -/
def originalCurveEquiv (s : Side) (r ι : ℂ) :
    (CP ⧸ originalCurveIdeal s r ι) ≃ₐ[ℂ] CurveRing s r ι :=
  Ideal.quotientEquivAlg _ _ (coordinateEquiv s) (originalCurveIdeal_map s r ι)

theorem originalCurveEquiv_mk (s : Side) (r ι : ℂ) (p : CP) :
    originalCurveEquiv s r ι (Ideal.Quotient.mk (originalCurveIdeal s r ι) p)=
      Ideal.Quotient.mk (curveIdeal s r ι) (coordinateMap s p) := rfl

def originalRestrictionValues (s : Side) (r : ℂ) : Fin 5 → CP :=
  match s with
  | .left => ![X 0,X 1,X 2,X 3,-X 2^2]
  | .right => ![X 0,X 1,X 2,X 3,C r*X 1*X 3]

def originalSubstitution (s : Side) (r : ℂ) : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] CP :=
  aeval (originalRestrictionValues s r)

theorem coordinateMap_substitution (s : Side) (r : ℂ) :
    (coordinateMap s).comp (originalSubstitution s r)=substitution s r := by
  apply MvPolynomial.algHom_ext
  intro i
  cases s <;> fin_cases i <;>
    simp [coordinateMap,coordinateValues,originalSubstitution,originalRestrictionValues,
      substitution,restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat] <;> ring

theorem originalSubstitution_h (s : Side) (r ι : ℂ) :
    originalSubstitution s r (smoothH ι)=originalCubic ι := by
  cases s <;>
    simp [originalSubstitution,originalRestrictionValues,smoothH,smoothB,smoothA,
      originalCubic,Matrix.cons_val_succ,Fin.reduceSucc] <;> ring

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.originalCurveEquiv
#print axioms CycleQ2CurveRestriction.coordinateMap_substitution
end
end


/- Component: continuation_3/GenericSexticGradient.lean -/
section
/-! The actual generic invariant sextic has no nonzero common gradient
zero. A finite homogeneous multiplication map is surjective at the Fermat
specialization. Its proved determinant open is nonzero in the independent
coefficient ring, hence remains a unit over its fraction field and every
field extension. This proves the algebraic gradient condition; it does not
silently invoke a geometric smoothness or cohomology comparison theorem. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2GenericSexticGradient
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2HomogeneousIdealArithmetic

abbrev CoeffRing := MvPolynomial (FullInvariantIndex 6) ℂ

def universalF : Poly CoeffRing := fullInvariantPolynomial 6 X
def generators : Fin 5 → Poly CoeffRing := fun j => X j * pderiv j universalF
def degree : Fin 5 → ℕ := fun _ => 6
def purePower : Fin 5 → ℕ := ![6,6,6,6,3]
def coordinatePower : Fin 5 → ℕ := ![30,30,30,30,15]

theorem euler_homogeneous {R : Type*} [CommRing R] {p : Poly R}
    {d : Grade} (hp : HG p d) (j : Fin 5) : HG (X j * pderiv j p) d := by
  classical
  rw [p.as_sum]
  simp only [map_sum,Finset.mul_sum,X_mul_pderiv_monomial]
  apply (weightedHomogeneousSubmodule R fullGrading d).sum_mem
  intro e he
  apply (weightedHomogeneousSubmodule R fullGrading d).nsmul_mem
  exact isWeightedHomogeneous_monomial fullGrading _ _ (hp (mem_support_iff.mp he))

theorem generators_homogeneous (j : Fin 5) : HG (generators j) (degree j,0) :=
  euler_homogeneous (fullInvariantPolynomial_homogeneous 6 X) j

theorem purePower_homogeneous (j : Fin 5) :
    HG ((X j : Poly ℂ)^purePower j) (6,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem fermat_homogeneous : HG CycleQ2FermatJacobian.fermat (6,0) :=
  ((((purePower_homogeneous 0).add (purePower_homogeneous 1)).add
    (purePower_homogeneous 2)).add (purePower_homogeneous 3)).add
    (purePower_homogeneous 4)

def fermatCoefficients : FullInvariantIndex 6 → ℂ :=
  fun e => CycleQ2FermatJacobian.fermat.coeff (fullExponentOf e.val)
def seedEvaluation : CoeffRing →+* ℂ := eval fermatCoefficients

theorem universalF_seed : MvPolynomial.map seedEvaluation universalF =
    CycleQ2FermatJacobian.fermat := by
  rw [universalF,map_fullInvariantPolynomial]
  have h : seedEvaluation ∘ (X : FullInvariantIndex 6 → CoeffRing)=fermatCoefficients := by
    funext e
    simp only [Function.comp_apply,seedEvaluation,eval_X]
  rw [h]
  exact fullInvariantPolynomial_of_homogeneous fermat_homogeneous

theorem generators_seed (j : Fin 5) :
    MvPolynomial.map seedEvaluation (generators j) =
      C (CycleQ2FermatJacobian.derivativeScalar j) * X j ^ purePower j := by
  rw [generators,map_mul,map_X,←pderiv_map,universalF_seed,
    CycleQ2FermatJacobian.derivative_eq]
  have hp : purePower j=CycleQ2FermatJacobian.cutoff j+1 := by
    fin_cases j <;> rfl
  rw [hp,pow_succ]
  unfold CycleQ2FermatJacobian.generator
  ring

theorem purePower_seed_mem (j : Fin 5) :
    (X j : Poly ℂ)^purePower j ∈
      generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  have h := Ideal.subset_span (Set.mem_range_self
    (f := fun j => MvPolynomial.map seedEvaluation (generators j)) j)
  change MvPolynomial.map seedEvaluation (generators j) ∈
    generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) at h
  have hh := Ideal.mul_mem_left _ (C ((CycleQ2FermatJacobian.derivativeScalar j)⁻¹)) h
  rwa [generators_seed,←mul_assoc,←map_mul,
    inv_mul_cancel₀ (CycleQ2FermatJacobian.derivativeScalar_ne_zero j),map_one,one_mul] at hh

theorem degree30_divisible (e : FullInvariantIndex 30) :
    ∃ j : Fin 5, purePower j ≤ fullExponentOf e.val j := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have hd := e.property.1
  rw [fullExponentOf_apply,show purePower 0=6 by decide] at h0
  rw [fullExponentOf_apply,show purePower 1=6 by decide] at h1
  rw [fullExponentOf_apply,show purePower 2=6 by decide] at h2
  rw [fullExponentOf_apply,show purePower 3=6 by decide] at h3
  rw [fullExponentOf_apply,show purePower 4=3 by decide] at h4
  simp only [fullDegree] at hd
  omega

theorem seed_monomial_mem (e : FullInvariantIndex 30) :
    (monomial (fullExponentOf e.val) 1 : Poly ℂ) ∈
      generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  obtain ⟨j,hj⟩ := degree30_divisible e
  have he : Finsupp.single j (purePower j) ≤ fullExponentOf e.val :=
    Finsupp.single_le_iff.mpr hj
  have hm : (monomial (fullExponentOf e.val) 1 : Poly ℂ) =
      X j^purePower j * monomial (fullExponentOf e.val-Finsupp.single j (purePower j)) 1 := by
    rw [X_pow_eq_monomial,monomial_mul,one_mul,add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (purePower_seed_mem j)

theorem seed_homogeneous_mem (p : Poly ℂ) (hp : HG p (30,0)) :
    p ∈ generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  rw [←fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial,mul_one] using
    Ideal.mul_mem_left (generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)))
      (C (p.coeff (fullExponentOf e.val))) (seed_monomial_mem e)

theorem degree_le (j : Fin 5) : degree j ≤ 30 := by
  change 6≤30
  decide

def coefficientMatrix : Matrix (FullInvariantIndex 30) (Column 30 degree) CoeffRing :=
  multiplicationMatrix generators degree 30

theorem seed_surjective : Function.Surjective (coefficientMatrix.map seedEvaluation).mulVec := by
  rw [coefficientMatrix,multiplicationMatrix_map]
  exact multiplication_surjective_of_membership _ degree
    (fun j => homogeneous_map _ (generators_homogeneous j)) 30 degree_le seed_homogeneous_mem

theorem exists_gradient_open : ∃ s : CoeffRing, seedEvaluation s=1 ∧
    ∀ (S : Type) [CommRing S] (φ : CoeffRing →+* S), IsUnit (φ s) →
      Function.Surjective (coefficientMatrix.map φ).mulVec := by
  exact CycleQ2HomogeneousIdealOpen.exists_multiplication_open seedEvaluation
    (C : ℂ →+* CoeffRing) (fun x => by simp only [seedEvaluation,eval_C]) generators degree
    generators_homogeneous 30 degree_le seed_homogeneous_mem

def gradientOpen : CoeffRing := Classical.choose exists_gradient_open

theorem gradientOpen_seed : seedEvaluation gradientOpen=1 :=
  (Classical.choose_spec exists_gradient_open).1

theorem gradientOpen_ne_zero : gradientOpen ≠ 0 := by
  intro hz
  have h := gradientOpen_seed
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem homogeneous_mem_of_open {S : Type} [CommRing S]
    (φ : CoeffRing →+* S) (hs : IsUnit (φ gradientOpen))
    (p : Poly S) (hp : HG p (30,0)) :
    p ∈ generatorIdeal (fun j => MvPolynomial.map φ (generators j)) := by
  have h := (Classical.choose_spec exists_gradient_open).2 S φ hs
  rw [coefficientMatrix,multiplicationMatrix_map] at h
  exact membership_of_multiplication_surjective _ degree
    (fun j => homogeneous_map _ (generators_homogeneous j)) 30 degree_le h p hp

theorem coordinatePower_homogeneous {S : Type*} [CommRing S] (j : Fin 5) :
    HG ((X j : Poly S)^coordinatePower j) (30,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem coordinate_power_mem {S : Type} [CommRing S]
    (φ : CoeffRing →+* S) (hs : IsUnit (φ gradientOpen)) (j : Fin 5) :
    (X j : Poly S)^coordinatePower j ∈
      generatorIdeal (fun j => MvPolynomial.map φ (generators j)) :=
  homogeneous_mem_of_open φ hs _ (coordinatePower_homogeneous j)

/-- Every faithful coefficient specialization, including the actual generic
field and its field extensions, has no nonzero common zero of all five
partial derivatives. The polynomial is the complete invariant sextic. -/
theorem nonzero_gradient_of_injective {K : Type} [Field K]
    (φ : CoeffRing →+* K) (hφ : Function.Injective φ) (x : Fin 5 → K)
    (hx : ∃ j, x j ≠ 0) :
    ∃ j, eval x (pderiv j (MvPolynomial.map φ universalF)) ≠ 0 := by
  have hs : IsUnit (φ gradientOpen) := isUnit_iff_ne_zero.mpr
    (fun hz => gradientOpen_ne_zero (hφ (hz.trans (map_zero φ).symm)))
  by_contra! hzero
  have hle : generatorIdeal (fun j => MvPolynomial.map φ (generators j)) ≤
      RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change eval x (MvPolynomial.map φ (generators j))=0
    rw [generators,map_mul,map_X,←pderiv_map,map_mul,eval_X,hzero j,mul_zero]
  obtain ⟨j,hj⟩ := hx
  have hz := hle (coordinate_power_mem φ hs j)
  change eval x ((X j)^coordinatePower j)=0 at hz
  rw [map_pow,eval_X] at hz
  exact (pow_ne_zero _ hj) hz

/-- The preceding condition holds over every field extension of the actual
independent-coefficient fraction field. In particular, passing to a finite
field that carries an incidence solution introduces no new smoothness
assumption about the sextic. -/
theorem nonzero_gradient_over_fraction_extension {K : Type} [Field K]
    [Algebra (FractionRing CoeffRing) K] (x : Fin 5 → K)
    (hx : ∃ j, x j ≠ 0) :
    ∃ j, eval x (pderiv j (MvPolynomial.map
      ((algebraMap (FractionRing CoeffRing) K).comp
        (algebraMap CoeffRing (FractionRing CoeffRing))) universalF)) ≠ 0 :=
  nonzero_gradient_of_injective _
    ((algebraMap (FractionRing CoeffRing) K).injective.comp
      (IsFractionRing.injective CoeffRing (FractionRing CoeffRing))) x hx

end CycleQ2GenericSexticGradient

#print axioms CycleQ2GenericSexticGradient.gradientOpen_seed
#print axioms CycleQ2GenericSexticGradient.nonzero_gradient_of_injective
#print axioms CycleQ2GenericSexticGradient.nonzero_gradient_over_fraction_extension
end
end


/- Component: continuation_3/IncidenceBasepointOpen.lean -/
section
/-! # A genuine polynomial open with no projective matrix basepoints

The complete degree120 multiplication matrix is formed from the actual
moving matrix entries, cubic, and sextic. A seed right inverse determines
a polynomial whose seed value is one. On its principal open, the original
coordinate powers lie in the matrix-entry ideal modulo the moving cubic
and sextic. No list of maximal minors or geometric openness premise occurs.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceBasepointOpen

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2HomogeneousIdealArithmetic
open CycleQ2SegreComplexBasepoint (generatorDegree generatorDegree_le coordinatePower)

abbrev Coeff := ParameterPolynomial ℂ

def rawCubicCoefficient (e : FullInvariantIndex 3) : Coeff := X (Sum.inl e)
def rawSexticCoefficient (e : FullInvariantIndex 6) : Coeff := X (Sum.inr (Sum.inl e))
def rawMatrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : Coeff :=
  X (Sum.inr (Sum.inr ((i,j),e)))

def familyH : Poly Coeff := fullInvariantPolynomial 3 rawCubicCoefficient
def familyF : Poly Coeff := fullInvariantPolynomial 6 rawSexticCoefficient
def familyMatrix : Matrix (Fin 3) (Fin 3) (Poly Coeff) :=
  incidenceMatrix 57 rawMatrixCoefficient

def generators {R : Type*} [CommRing R] (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) : Fin 11 → Poly R :=
  ![incidenceMatrix r δ 0 0,incidenceMatrix r δ 0 1,incidenceMatrix r δ 0 2,
    incidenceMatrix r δ 1 0,incidenceMatrix r δ 1 1,incidenceMatrix r δ 1 2,
    incidenceMatrix r δ 2 0,incidenceMatrix r δ 2 1,incidenceMatrix r δ 2 2,
    fullInvariantPolynomial 3 hc,fullInvariantPolynomial 6 Fc]

def universalGenerators : Fin 11 → Poly Coeff :=
  generators 57 rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient

theorem generators_homogeneous {R : Type*} [CommRing R] (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (j : Fin 11) :
    HG (generators r hc Fc δ j) (generatorDegree j,0) := by
  fin_cases j
  · exact incidenceMatrix_homogeneous r δ 0 0
  · exact incidenceMatrix_homogeneous r δ 0 1
  · exact incidenceMatrix_homogeneous r δ 0 2
  · exact incidenceMatrix_homogeneous r δ 1 0
  · exact incidenceMatrix_homogeneous r δ 1 1
  · exact incidenceMatrix_homogeneous r δ 1 2
  · exact incidenceMatrix_homogeneous r δ 2 0
  · exact incidenceMatrix_homogeneous r δ 2 1
  · exact incidenceMatrix_homogeneous r δ 2 2
  · exact fullInvariantPolynomial_homogeneous 3 hc
  · exact fullInvariantPolynomial_homogeneous 6 Fc

theorem generators_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (fun j => map φ (generators r hc Fc δ j))=
      generators (φ r) (φ ∘ hc) (φ ∘ Fc) (fun i j e => φ (δ i j e)) := by
  have hm (i j : Fin 3) : map φ (incidenceMatrix r δ i j)=
      incidenceMatrix (φ r) (fun i j e => φ (δ i j e)) i j := by
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly S) => M i j)
        (map_incidenceMatrix φ r δ)
  funext j
  fin_cases j
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · exact map_fullInvariantPolynomial φ 3 hc
  · exact map_fullInvariantPolynomial φ 6 Fc

def seedEvaluation : Coeff →+* ℂ :=
  (polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0)).toRingHom

theorem seedEvaluation_constant (c : ℂ) : seedEvaluation (C c)=c :=
  (polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0)).commutes c

def seedFamilyGenerators : Fin 11 → Poly ℂ :=
  ![rawSeedMatrix 57 0 0,rawSeedMatrix 57 0 1,rawSeedMatrix 57 0 2,
    rawSeedMatrix 57 1 0,rawSeedMatrix 57 1 1,rawSeedMatrix 57 1 2,
    rawSeedMatrix 57 2 0,rawSeedMatrix 57 2 1,rawSeedMatrix 57 2 2,
    smoothH Complex.I,smoothF 57 Complex.I]

theorem seed_universalGenerators :
    (fun j => map seedEvaluation (universalGenerators j))=seedFamilyGenerators := by
  have hh : seedEvaluation ∘ rawCubicCoefficient=seedCubicCoefficients Complex.I := by
    funext e
    simp [seedEvaluation,rawCubicCoefficient,polynomialSpecialization,coefficientPoint]
  have hF : seedEvaluation ∘ rawSexticCoefficient=seedSexticCoefficients (57:ℂ) Complex.I := by
    funext e
    simp [seedEvaluation,rawSexticCoefficient,polynomialSpecialization,coefficientPoint]
  have hδ : (fun i j e => seedEvaluation (rawMatrixCoefficient i j e))=
      (fun _ _ _ => (0:ℂ)) := by
    funext i j e
    simp [seedEvaluation,rawMatrixCoefficient,polynomialSpecialization,coefficientPoint]
  rw [universalGenerators,generators_map,hh,hF,hδ,map_ofNat]
  simp only [generators,incidenceMatrix_zero,seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial,seedFamilyGenerators]

private theorem eleven_span_replace {A : Type*} [CommRing A]
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 h g k : A) :
    Ideal.span (Set.range ![a0,a1,a2,a3,a4,a5,a6,a7,a8,h,g])≤
      Ideal.span (Set.range ![a0,a1,a2,a3,a4,a5,a6,a7,a8,h,g+h*k]) := by
  have ht : (Ideal.span {h} : Ideal A) ⊔ Ideal.span {g+h*k}=
      Ideal.span {h} ⊔ Ideal.span {g} := by
    rw [←Ideal.span_union,←Ideal.span_union]
    simpa only [Set.singleton_union] using Ideal.span_pair_add_left_mul h g k
  simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty,
    Ideal.span_union,ht,le_refl]

theorem seed_ideal_le :
    generatorIdeal (CycleQ2SegreComplexBasepoint.seedGenerators (57:ℂ) Complex.I)≤
      generatorIdeal seedFamilyGenerators := by
  simpa only [generatorIdeal,CycleQ2SegreComplexBasepoint.seedGenerators,
    seedFamilyGenerators,smoothF] using
    eleven_span_replace
      (rawSeedMatrix (57:ℂ) 0 0) (rawSeedMatrix (57:ℂ) 0 1) (rawSeedMatrix (57:ℂ) 0 2)
      (rawSeedMatrix (57:ℂ) 1 0) (rawSeedMatrix (57:ℂ) 1 1) (rawSeedMatrix (57:ℂ) 1 2)
      (rawSeedMatrix (57:ℂ) 2 0) (rawSeedMatrix (57:ℂ) 2 1) (rawSeedMatrix (57:ℂ) 2 2)
      (smoothH Complex.I) (seedG (57:ℂ)) (smoothK Complex.I)

theorem seed_homogeneous_mem (p : Poly ℂ) (hp : HG p (120,0)) :
    p∈generatorIdeal seedFamilyGenerators :=
  seed_ideal_le (CycleQ2SegreComplexBasepoint.complex_homogeneous_mem p hp)

def familyMultiplicationMatrix :
    Matrix (FullInvariantIndex 120) (Column 120 generatorDegree) Coeff :=
  multiplicationMatrix universalGenerators generatorDegree 120

theorem seed_multiplication_surjective :
    Function.Surjective (familyMultiplicationMatrix.map seedEvaluation).mulVec := by
  rw [familyMultiplicationMatrix,multiplicationMatrix_map,seed_universalGenerators]
  have hg (j : Fin 11) : HG (seedFamilyGenerators j) (generatorDegree j,0) := by
    rw [←congrFun seed_universalGenerators j]
    exact homogeneous_map seedEvaluation
      (generators_homogeneous (57:Coeff) rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient j)
  exact multiplication_surjective_of_membership seedFamilyGenerators generatorDegree hg
    120 generatorDegree_le seed_homogeneous_mem

/-- A genuine polynomial, nonzero at the seed, controls basepoint freeness
over arbitrary commutative coefficient rings on its principal open. -/
theorem exists_basepoint_polynomial :
    ∃s : Coeff,seedEvaluation s=1 ∧
      ∀ (S : Type) [CommRing S] (g : Coeff →+* S),IsUnit (g s) →
        ∀p : Poly S,HG p (120,0) →
          p∈generatorIdeal (fun j => map g (universalGenerators j)) := by
  have hseed (p : Poly ℂ) (hp : HG p (120,0)) :
      p∈generatorIdeal (fun j => map seedEvaluation (universalGenerators j)) := by
    rw [seed_universalGenerators]
    exact seed_homogeneous_mem p hp
  exact CycleQ2HomogeneousIdealOpen.exists_homogeneous_open
    seedEvaluation (C : ℂ →+* Coeff) seedEvaluation_constant
    universalGenerators generatorDegree
    (generators_homogeneous (57:Coeff) rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient)
    120 generatorDegree_le hseed

def basepointPolynomial : Coeff := exists_basepoint_polynomial.choose

theorem seed_basepointPolynomial : seedEvaluation basepointPolynomial=1 :=
  exists_basepoint_polynomial.choose_spec.1

theorem basepointPolynomial_ne_zero : basepointPolynomial≠0 := by
  intro hz
  have h := seed_basepointPolynomial
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem specialized_homogeneous_mem {S : Type} [CommRing S]
    (g : Coeff →+* S) (hs : IsUnit (g basepointPolynomial))
    (p : Poly S) (hp : HG p (120,0)) :
    p∈generatorIdeal (fun j => map g (universalGenerators j)) :=
  exists_basepoint_polynomial.choose_spec.2 S g hs p hp

theorem coordinate_power_homogeneous {S : Type*} [CommRing S] (j : Fin 5) :
    HG ((X j : Poly S)^coordinatePower j) (120,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

section SpecializedQuotient

variable {S : Type} [CommRing S] (g : Coeff →+* S)

abbrev CurveRing := Poly S ⧸ equationsIdeal (map g familyH) (map g familyF)
def curveQuotient : Poly S →+* CurveRing g := Ideal.Quotient.mk _
def curveCoordinate (j : Fin 5) : CurveRing g := curveQuotient g (X j)
def curveMatrix : Matrix (Fin 3) (Fin 3) (CurveRing g) :=
  fun i j => curveQuotient g (map g (familyMatrix i j))
def entryIdeal : Ideal (CurveRing g) :=
  Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => curveMatrix g ij.1 ij.2))

theorem quotient_h : curveQuotient g (map g familyH)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem quotient_F : curveQuotient g (map g familyF)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem generator_quotient_mem (t : Fin 11) :
    curveQuotient g (map g (universalGenerators t))∈entryIdeal g := by
  have hm (i j : Fin 3) : curveMatrix g i j∈entryIdeal g :=
    Ideal.subset_span (Set.mem_range_self (i,j))
  fin_cases t
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · change curveQuotient g (map g familyH)∈_
    rw [quotient_h]
    exact Ideal.zero_mem _
  · change curveQuotient g (map g familyF)∈_
    rw [quotient_F]
    exact Ideal.zero_mem _

theorem specialized_coordinate_power_mem (hs : IsUnit (g basepointPolynomial)) (j : Fin 5) :
    curveCoordinate g j^coordinatePower j∈entryIdeal g := by
  have hle : generatorIdeal (fun t => map g (universalGenerators t))≤
      (entryIdeal g).comap (curveQuotient g) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact generator_quotient_mem g t
  have h := hle (specialized_homogeneous_mem g hs _ (coordinate_power_homogeneous (S:=S) j))
  change curveQuotient g ((X j : Poly S)^coordinatePower j)∈entryIdeal g at h
  simpa only [map_pow,curveCoordinate] using h

theorem specialized_prime_pivot_cover (hs : IsUnit (g basepointPolynomial))
    (P : Ideal (CurveRing g)) [P.IsPrime]
    (hx : ∃j,curveCoordinate g j∉P) : ∃i j,curveMatrix g i j∉P := by
  classical
  by_contra! hzero
  have hle : entryIdeal g≤P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨ij,rfl⟩
    exact hzero ij.1 ij.2
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (specialized_coordinate_power_mem g hs j)))

theorem entries_generate_if_coordinate_unit (hs : IsUnit (g basepointPolynomial))
    {T : Type*} [CommRing T] (φ : CurveRing g →+* T) (j : Fin 5)
    (hu : IsUnit (φ (curveCoordinate g j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (curveMatrix g ij.1 ij.2)))=⊤ := by
  have hm := Ideal.mem_map_of_mem φ (specialized_coordinate_power_mem g hs j)
  have hunit : IsUnit (φ (curveCoordinate g j^coordinatePower j)) := by
    rw [map_pow]
    exact hu.pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hunit
  simpa only [entryIdeal,Ideal.map_span,←Set.range_comp,Function.comp_def] using ht

end SpecializedQuotient

end CycleQ2IncidenceBasepointOpen

#print axioms CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial
#print axioms CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
#print axioms CycleQ2IncidenceBasepointOpen.entries_generate_if_coordinate_unit
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceCubicCechTrace.lean -/
section
/-! Every invariant cubic coefficient vector has the actual nine-column
Čech residue formula.  This is independent of any saved tangent matrix:
the chosen nonconstructive tangent can be substituted directly. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceCubicCechTrace
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2SeedTrace
  CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2SegreModularDetectorData

theorem cubic_expansion (η : FullInvariantIndex 3 → ℂ) :
    fullInvariantPolynomial 3 η=
      ∑ j : Fin 9, MvPolynomial.monomial
        (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) (η (cubicIndex j)) := by
  rw [fullInvariantPolynomial,←cubicEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  change MvPolynomial.monomial (fullExponentOf (cubicIndex j).val) (η (cubicIndex j))=_
  rw [cubicIndex_exponent]

theorem substitute_column (j : Fin 9) (c : ℂ) :
    substitute (MvPolynomial.monomial
      (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) c)=C c*cubicColumn j := by
  rw [show MvPolynomial.monomial
      (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) c=
      C c*MvPolynomial.monomial
        (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) (1:ℂ) by
      rw [C_mul_monomial,mul_one]]
  rw [map_mul,show substitute (C c)=C c by simp [substitute],
    ←CycleQ2SparseGaussianPolynomial.monomial_variables]
  fin_cases j <;>
    simp [cubicExponents,CycleQ2SparseGaussianPolynomial.monomial,substitute,cubicColumn,
      mon,Fin.reduceFinMk] <;> ring_nf <;> simp

theorem substitute_cubic (η : FullInvariantIndex 3 → ℂ) :
    substitute (fullInvariantPolynomial 3 η)=cubicDeformation (fun j => η (cubicIndex j)) := by
  rw [cubic_expansion,map_sum]
  simp only [substitute_column,cubicDeformation]

def unscaledTrace (η : FullInvariantIndex 3 → ℂ) : ℂ :=
  Complex.I*η (cubicIndex 1)-(1+Complex.I)*η (cubicIndex 8)

theorem derivativeTrace_eq (η : FullInvariantIndex 3 → ℂ) :
    derivativeTrace 1 (fun j => η (cubicIndex j))=unscaledTrace η/6 :=
  smooth_derivativeTrace_explicit _

theorem cubic_residue (r : ℂ) (η : FullInvariantIndex 3 → ℂ) :
    cechResidue r 1 (derivativeNumerator (substitute (fullInvariantPolynomial 3 η))) 2 4=
      (3*r)*(unscaledTrace η/6) := by
  rw [substitute_cubic,deformation_residue,derivativeTrace_eq]

theorem cubic_trace_one_not_boundary (r : ℂ) (hr : r≠0)
    (η : FullInvariantIndex 3 → ℂ) (hη : unscaledTrace η=6) :
    ¬ CechBoundary r 1 (derivativeNumerator (substitute (fullInvariantPolynomial 3 η))) 2 4 := by
  rw [substitute_cubic]
  apply nonboundary_of_derivativeTrace_ne_zero r 1 hr
  rw [derivativeTrace_eq,hη]
  norm_num

theorem cubic_trace_one_normal_trace (r : ℂ) (hr : r≠0)
    (η : FullInvariantIndex 3 → ℂ) (hη : unscaledTrace η=6) :
    pairedNormalTrace r 1 hr (substitute (fullInvariantPolynomial 3 η))=-(3*r)⁻¹ := by
  rw [substitute_cubic,pairedNormalTrace_deformation,derivativeTrace_eq,hη]
  norm_num

end CycleQ2IncidenceCubicCechTrace

#print axioms CycleQ2IncidenceCubicCechTrace.substitute_cubic
#print axioms CycleQ2IncidenceCubicCechTrace.cubic_trace_one_not_boundary
#print axioms CycleQ2IncidenceCubicCechTrace.cubic_trace_one_normal_trace
end
end


/- Component: continuation_3/LinkageComponentDecomposition.lean -/
section
/-! Elementary decomposition of the literal linkage ideal into its three
cubic-root components on the open where their common vertex is absent. -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinkageComponentDecomposition

open CycleQ2SegreSeed
variable {R : Type*} [CommRing R]

def leftIdeal (a b c d : R) : Ideal R := Ideal.span (Set.range (linkageE a b c d))

def rootValues (ζ : R) : Fin 3 → R := ![1,ζ,ζ^2]

def componentGenerator (z a b c d : R) : Fin 2 → R := ![a-z*b,c+z^2*d]

def componentIdeal (z a b c d : R) : Ideal R :=
  Ideal.span (Set.range (componentGenerator z a b c d))

theorem leftGenerator_mem (a b c d : R) (j : Fin 5) :
    linkageE a b c d j ∈ leftIdeal a b c d := Ideal.subset_span ⟨j,rfl⟩

theorem componentGenerator_mem (z a b c d : R) (j : Fin 2) :
    componentGenerator z a b c d j ∈ componentIdeal z a b c d := Ideal.subset_span ⟨j,rfl⟩

theorem cube_eq_one (ζ : R) (hζ : ζ^2+ζ+1=0) : ζ^3=1 := by
  linear_combination (ζ-1)*hζ

theorem rootValues_cube (ζ : R) (hζ : ζ^2+ζ+1=0) (i : Fin 3) : rootValues ζ i^3=1 := by
  have h3 := cube_eq_one ζ hζ
  fin_cases i
  · simp [rootValues]
  · exact h3
  · change (ζ^2)^3=1
    calc
      (ζ^2)^3=(ζ^3)^2 := by ring
      _=1 := by rw [h3]; ring

theorem substituted_linkageE_zero (z b d : R) (hz : z^3=1) (j : Fin 5) :
    linkageE (z*b) b (-(z^2*d)) d j=0 := by
  have hz4 : z^4=z := by
    calc
      z^4=z^3*z := by ring
      _=z := by rw [hz]; ring
  have hz6 : z^6=1 := by
    calc
      z^6=(z^3)^2 := by ring
      _=1 := by rw [hz]; ring
  fin_cases j
  · change z*b*(-(z^2*d))+b*d=0
    ring_nf
    rw [hz]
    ring
  · change (z*b)^3-b^3=0
    ring_nf
    rw [hz]
    ring
  · change (z*b)^2*d+b^2*(-(z^2*d))=0
    ring
  · change z*b*d^2-b*(-(z^2*d))^2=0
    ring_nf
    rw [hz4]
    ring
  · change (-(z^2*d))^3+d^3=0
    ring_nf
    rw [hz6]
    ring

theorem leftIdeal_le_component (z a b c d : R) (hz : z^3=1) :
    leftIdeal a b c d ≤ componentIdeal z a b c d := by
  apply Ideal.span_le.mpr
  rintro x ⟨j,rfl⟩
  let J := componentIdeal z a b c d
  let f := Ideal.Quotient.mk J
  have ha : f a=f z*f b := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (componentGenerator_mem z a b c d 0)
    change f (a-z*b)=0 at h
    exact sub_eq_zero.mp (by simpa only [map_sub,map_mul] using h)
  have hc : f c= -(f z^2*f d) := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (componentGenerator_mem z a b c d 1)
    change f (c+z^2*d)=0 at h
    exact eq_neg_of_add_eq_zero_left (by simpa only [map_add,map_mul,map_pow] using h)
  have hz' : f z^3=1 := by simpa only [map_pow,map_one] using congrArg f hz
  have hm : f (linkageE a b c d j)=linkageE (f a) (f b) (f c) (f d) j := by
    fin_cases j <;> simp [linkageE,linkageP]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (linkageE a b c d j)=0
  rw [hm,ha,hc]
  exact substituted_linkageE_zero (f z) (f b) (f d) hz' j

def productCombination (ζ a b c d : R) : Fin 2 → Fin 2 → Fin 2 → R :=
  ![![![linkageE a b c d 1,
       (a+(-ζ-1)*b)*linkageP a b c d+ζ*linkageE a b c d 2],
      ![(a+ζ*b)*linkageP a b c d+(-ζ-1)*linkageE a b c d 2,
       (c-d)*linkageP a b c d+linkageE a b c d 3]],
    ![![(a+b)*linkageP a b c d+linkageE a b c d 2,
       (c+(ζ+1)*d)*linkageP a b c d+ζ*linkageE a b c d 3],
      ![(c-ζ*d)*linkageP a b c d+(-ζ-1)*linkageE a b c d 3,
       linkageE a b c d 4]]]

theorem componentProduct_identity (ζ a b c d : R) (hζ : ζ^2+ζ+1=0)
    (i j k : Fin 2) :
    componentGenerator 1 a b c d i*componentGenerator ζ a b c d j*
      componentGenerator (ζ^2) a b c d k=productCombination ζ a b c d i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [componentGenerator,one_pow,one_mul]
  · change (a-b)*(a-ζ*b)*(a-ζ^2*b)=a^3-b^3
    linear_combination b*(a-b)*(-a+b*ζ-b)*hζ
  · change (a-b)*(a-ζ*b)*(c+(ζ^2)^2*d)=
      (a+(-ζ-1)*b)*(a*c+b*d)+ζ*(a^2*d+b^2*c)
    linear_combination -d*(a-b)*(-a*ζ^2+a*ζ+b*ζ^3-b*ζ^2+b)*hζ
  · change (a-b)*(c+ζ^2*d)*(a-ζ^2*b)=
      (a+ζ*b)*(a*c+b*d)+(-ζ-1)*(a^2*d+b^2*c)
    linear_combination -(a-b)*(-a*d+b*c+b*d*ζ^2-b*d*ζ)*hζ
  · change (a-b)*(c+ζ^2*d)*(c+(ζ^2)^2*d)=(c-d)*(a*c+b*d)+(a*d^2-b*c^2)
    linear_combination d*(a-b)*(c+d*ζ^2-d)*(ζ^2-ζ+1)*hζ
  · change (c+d)*(a-ζ*b)*(a-ζ^2*b)=(a+b)*(a*c+b*d)+(a^2*d+b^2*c)
    linear_combination b*(c+d)*(-a+b*ζ-b)*hζ
  · change (c+d)*(a-ζ*b)*(c+(ζ^2)^2*d)=
      (c+(ζ+1)*d)*(a*c+b*d)+ζ*(a*d^2-b*c^2)
    linear_combination -d*(c+d)*(-a*ζ^2+a*ζ+b*ζ^3-b*ζ^2+b)*hζ
  · change (c+d)*(c+ζ^2*d)*(a-ζ^2*b)=(c-ζ*d)*(a*c+b*d)+(-ζ-1)*(a*d^2-b*c^2)
    linear_combination -(c+d)*(-a*d+b*c+b*d*ζ^2-b*d*ζ)*hζ
  · change (c+d)*(c+ζ^2*d)*(c+(ζ^2)^2*d)=c^3+d^3
    linear_combination d*(c+d)*(c+d*ζ^2-d)*(ζ^2-ζ+1)*hζ

theorem productCombination_mem (ζ a b c d : R) (i j k : Fin 2) :
    productCombination ζ a b c d i j k ∈ leftIdeal a b c d := by
  have hP : linkageP a b c d ∈ leftIdeal a b c d := leftGenerator_mem a b c d 0
  have hA := leftGenerator_mem a b c d 1
  have hB := leftGenerator_mem a b c d 2
  have hC := leftGenerator_mem a b c d 3
  have hD := leftGenerator_mem a b c d 4
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [productCombination,Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact hA
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hB)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hB)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP) hC
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP) hB
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hC)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hC)
  · exact hD

theorem component_product_le (ζ a b c d : R) (hζ : ζ^2+ζ+1=0) :
    componentIdeal 1 a b c d*componentIdeal ζ a b c d*componentIdeal (ζ^2) a b c d ≤
      leftIdeal a b c d := by
  unfold componentIdeal
  rw [Ideal.span_mul_span',Ideal.span_mul_span']
  apply Ideal.span_le.mpr
  rintro x ⟨y,⟨u,⟨i,rfl⟩,v,⟨j,rfl⟩,rfl⟩,w,⟨k,rfl⟩,rfl⟩
  change componentGenerator 1 a b c d i*componentGenerator ζ a b c d j*
    componentGenerator (ζ^2) a b c d k ∈ leftIdeal a b c d
  rw [componentProduct_identity ζ a b c d hζ]
  exact productCombination_mem ζ a b c d i j k

theorem components_sup_top (z w a b c d : R) (hz : z^3=1) (hw : w^3=1)
    (hzw : IsUnit (z-w)) (hzw2 : IsUnit (z^2-w^2))
    (hcover : leftIdeal a b c d ⊔ Ideal.span {b,d}=⊤) :
    componentIdeal z a b c d ⊔ componentIdeal w a b c d=⊤ := by
  let J := componentIdeal z a b c d ⊔ componentIdeal w a b c d
  have hb : b ∈ J := by
    apply (Ideal.unit_mul_mem_iff_mem J hzw).mp
    have h := J.sub_mem
      (show componentGenerator w a b c d 0 ∈ J from (le_sup_right : componentIdeal w a b c d ≤ J) (componentGenerator_mem w a b c d 0))
      (show componentGenerator z a b c d 0 ∈ J from (le_sup_left : componentIdeal z a b c d ≤ J) (componentGenerator_mem z a b c d 0))
    convert h using 1 <;> simp [componentGenerator] <;> ring
  have hd : d ∈ J := by
    apply (Ideal.unit_mul_mem_iff_mem J hzw2).mp
    have h := J.sub_mem
      (show componentGenerator z a b c d 1 ∈ J from (le_sup_left : componentIdeal z a b c d ≤ J) (componentGenerator_mem z a b c d 1))
      (show componentGenerator w a b c d 1 ∈ J from (le_sup_right : componentIdeal w a b c d ≤ J) (componentGenerator_mem w a b c d 1))
    convert h using 1 <;> simp [componentGenerator] <;> ring
  have hle : leftIdeal a b c d ⊔ Ideal.span {b,d} ≤ J := by
    apply sup_le
    · exact (leftIdeal_le_component z a b c d hz).trans le_sup_left
    · exact Ideal.span_le.mpr (by intro x hx; rcases hx with rfl | ⟨rfl⟩ <;> assumption)
  rw [hcover] at hle
  exact top_unique hle

theorem leftIdeal_eq_components (ζ a b c d : R) (hζ : ζ^2+ζ+1=0)
    (hunits : ∀ i j : Fin 3, i≠j → IsUnit (rootValues ζ i-rootValues ζ j) ∧
      IsUnit (rootValues ζ i^2-rootValues ζ j^2))
    (hcover : leftIdeal a b c d ⊔ Ideal.span {b,d}=⊤) :
    leftIdeal a b c d=
      (componentIdeal 1 a b c d ⊓ componentIdeal ζ a b c d) ⊓ componentIdeal (ζ^2) a b c d := by
  have h01 := components_sup_top (rootValues ζ 0) (rootValues ζ 1) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 1)
    (hunits 0 1 (by decide)).1 (hunits 0 1 (by decide)).2 hcover
  have h02 := components_sup_top (rootValues ζ 0) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 2)
    (hunits 0 2 (by decide)).1 (hunits 0 2 (by decide)).2 hcover
  have h12 := components_sup_top (rootValues ζ 1) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 1) (rootValues_cube ζ hζ 2)
    (hunits 1 2 (by decide)).1 (hunits 1 2 (by decide)).2 hcover
  change componentIdeal 1 a b c d ⊔ componentIdeal ζ a b c d=⊤ at h01
  change componentIdeal 1 a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ at h02
  change componentIdeal ζ a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ at h12
  have hprod : componentIdeal 1 a b c d*componentIdeal ζ a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ := by
    rw [Ideal.mul_sup_eq_of_coprime_left h02,h12]
  apply le_antisymm
  · exact le_inf (le_inf (leftIdeal_le_component 1 a b c d (by simp))
      (leftIdeal_le_component ζ a b c d (cube_eq_one ζ hζ)))
      (leftIdeal_le_component (ζ^2) a b c d (rootValues_cube ζ hζ 2))
  · rw [←Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr h01),
      ←Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hprod)]
    exact component_product_le ζ a b c d hζ

end CycleQ2LinkageComponentDecomposition

#print axioms CycleQ2LinkageComponentDecomposition.component_product_le
#print axioms CycleQ2LinkageComponentDecomposition.leftIdeal_eq_components
end
end


/- Component: continuation_3/SeedCechActualTop.lean -/
section
/-! # The seven-dimensional quotient of the actual seed localization complex -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechActualTop

open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates CycleQ2SeedCechTopCohomology

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Degree-zero, character-zero sections inside the actual coordinate localization. -/
def gradedLocal (r ι : R) (s : Finset (Fin 3)) : Submodule R (SeedLocal R r ι s) :=
  (gradedFamilies R).comap (linearCoordinates R r ι s)

def gradedCoordinates (r ι : R) (s : Finset (Fin 3)) :
    gradedLocal R r ι s →ₗ[R] gradedFamilies R where
  toFun p := ⟨linearCoordinates R r ι s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R r ι s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R r ι s) c p.val

@[simp] theorem gradedCoordinates_apply (r ι : R) (s : Finset (Fin 3))
    (p : gradedLocal R r ι s) :
    (gradedCoordinates R r ι s p).val = localizedCoordinates R r ι s p.val := rfl

theorem gradedCoordinates_injective (r ι : R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R r ι s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R r ι s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (r ι : R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R r ι s) = poleSubmodule R s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R r ι s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R r ι s p.val).mpr hp
    have hqg : q ∈ gradedLocal R r ι s := by
      change linearCoordinates R r ι s q ∈ gradedFamilies R
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (r ι : R) : gradedLocal R r ι Finset.univ ≃ₗ[R] gradedFamilies R :=
  LinearEquiv.ofBijective (gradedCoordinates R r ι Finset.univ)
    ⟨gradedCoordinates_injective R r ι Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R r ι Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (r ι : R) (p : gradedLocal R r ι Finset.univ) :
    totalEquiv R r ι p = gradedCoordinates R r ι Finset.univ p := rfl

def gradedRestriction (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R r ι s →ₗ[R] gradedLocal R r ι t where
  toFun p := ⟨restrictionLinear R r ι hst p.val, by
    intro ab
    change HasGrade ab 0 (localizedCoordinates R r ι t (restriction R r ι hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R r ι hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R r ι hst) c p.val

theorem gradedCoordinates_restriction (r ι : R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R r ι t).comp (gradedRestriction R r ι hst) =
      gradedCoordinates R r ι s := by
  ext p ab e
  change (localizedCoordinates R r ι t (restriction R r ι hst p.val) ab).coeff e =
    (localizedCoordinates R r ι s p.val ab).coeff e
  rw [coordinates_restriction]

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (r ι : R) : Submodule R (gradedLocal R r ι Finset.univ) :=
  LinearMap.range (gradedRestriction R r ι (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R r ι (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R r ι (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

theorem map_actualBoundary (r ι : R) :
    (actualBoundary R r ι).map (totalEquiv R r ι).toLinearMap = topBoundary R := by
  change (actualBoundary R r ι).map (gradedCoordinates R r ι Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]

abbrev ActualTopCechQuotient (r ι : R) :=
  gradedLocal R r ι Finset.univ ⧸ actualBoundary R r ι

def actualTopEquiv (r ι : R) : ActualTopCechQuotient R r ι ≃ₗ[R] TopCechQuotient R :=
  Submodule.Quotient.equiv _ _ (totalEquiv R r ι) (map_actualBoundary R r ι)

def actualTopBasis (r ι : R) : Module.Basis TopIndex R (ActualTopCechQuotient R r ι) :=
  (topCechBasis R).map (actualTopEquiv R r ι).symm

@[simp] theorem actualTopBasis_apply (r ι : R) (q : TopIndex) :
    actualTopEquiv R r ι (actualTopBasis R r ι q) =
      Submodule.Quotient.mk (basisSection R q) := by
  simp [actualTopBasis]

theorem actualTop_rank_seven (r ι : R) :
    Module.finrank R (ActualTopCechQuotient R r ι) = 7 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R r ι), topIndex_count]

end CycleQ2SeedCechActualTop

#print axioms CycleQ2SeedCechActualTop.actualTop_rank_seven
end
end


/- Component: continuation_3/cylinder_bridge/SeedFactorHomogeneous.lean -/
section
/-! # Original grading of the selected factor sections

These are the literal chosen sections of the incidence seed, with their
weighted degrees and cubic characters. The final projection identity is
applied before passing to the actual smooth quotient.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedFactorHomogeneous

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedLinkageIdeals CycleQ2WeightedComponent

variable {R : Type*} [CommRing R]

private theorem regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a=b) : HG p b := h ▸ hp

private lemma hx0 : HG (X 0 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 0
private lemma hx1 : HG (X 1 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 1
private lemma hx2 : HG (X 2 : Poly R) (1, 1) := isWeightedHomogeneous_X R fullGrading 2
private lemma hx3 : HG (X 3 : Poly R) (1, 0) := isWeightedHomogeneous_X R fullGrading 3
private lemma hw : HG (X 4 : Poly R) (2, 0) := isWeightedHomogeneous_X R fullGrading 4

private theorem leftCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (6, 2) := by
  fin_cases i
  · exact (regrade (((hw.pow 2).neg.mul hx1).mul hx3) (by decide)).add
      (regrade ((hx1.pow 2).mul (hx2.pow 4)) (by decide))
  · exact ((regrade (hw.neg.mul (hx1.pow 4)) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 4)) (by decide))).add
      (regrade ((hx1.mul (hx2.pow 3)).mul (hx3.pow 2)) (by decide))
  · exact ((regrade (((hw.pow 2).neg.mul hx0).mul hx3) (by decide)).add
      (regrade ((hx1.pow 4).mul (hx3.pow 2)) (by decide))).add
      (regrade ((hx2.pow 2).mul (hx3.pow 4)) (by decide))

private theorem leftCoeff1_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff1 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · exact (regrade ((hx0.mul hx1).mul (hx2.pow 2)) (by decide)).sub
      (regrade ((hx0.mul hx2).mul (hx3.pow 2)) (by decide))
  · exact regrade (hx3.pow 4) (by decide)
  · exact regrade (hx3.pow 4) (by decide)

private theorem rightCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · change HG (2 * (X 4 : Poly R) ^ 2 + 2 * X 4 * X 3 ^ 2) (4, 0)
    have h0 : HG ((C (2 : R)) * X 4 ^ 2) (4, 0) := regrade ((hw.pow 2).C_mul 2) (by decide)
    have h1 : HG ((C (2 : R)) * X 4 * X 3 ^ 2) (4, 0) :=
      regrade ((hw.C_mul 2).mul (hx3.pow 2)) (by decide)
    simpa only [map_ofNat] using h0.add h1
  · exact (regrade ((hw.mul hx0).mul hx2) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 2)) (by decide))
  · exact (((regrade ((hx0.mul (hx1.pow 2)).mul hx3) (by decide)).add
      (regrade ((hx1.mul hx2).mul (hx3.pow 2)) (by decide))).sub
      (regrade ((hx2.pow 3).mul hx3) (by decide))).add
      (regrade (hx3.pow 4) (by decide))

private theorem rightCoeff2_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff2 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 0) := by
  fin_cases i
  · exact hw.add (regrade (hx3.pow 2) (by decide))
  · exact hw
  · exact isWeightedHomogeneous_zero _ _ _

private theorem rightCoeff3_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff3 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 2) := by
  fin_cases i
  · exact isWeightedHomogeneous_zero _ _ _
  · exact regrade (hx0.mul hx3) (by decide)
  · exact isWeightedHomogeneous_zero _ _ _

private theorem baseRow0_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow0 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (8, 1) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.mul hw) (by decide : ((2,1) : Grade)+(2,0)=(4,1))).add
    (regrade (hb.mul hd) (by decide))
  have hQ := (regrade ((ha.pow 2).mul hb) (by decide : 2 • ((2,1) : Grade)+(2,2)=(6,1))).sub
    (regrade (hw.mul (hd.pow 2)) (by decide))
  have hT := (regrade (ha.mul (hb.pow 2)) (by decide : ((2,1) : Grade)+2 • (2,2)=(6,2))).add
    (regrade ((hw.pow 2).mul hd) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))


def polynomialLeft (r : R) (i : Fin 3) : Poly R :=
  CycleQ2SegreSeed.leftSection (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i

def polynomialRight (r : R) (j : Fin 3) : Poly R :=
  CycleQ2SegreSeed.rightSectionNumerator (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j

def polynomialLinkage (r : R) : Poly R :=
  CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

theorem polynomialLinkage_homogeneous (r : R) : HG (polynomialLinkage r) (4,1) :=
  linkageGenerator_homogeneous .left r 0

theorem polynomialLeft_homogeneous (r : R) (i : Fin 3) :
    HG (polynomialLeft r i) (10,0) := by
  have hP := polynomialLinkage_homogeneous r
  have hQ : HG ((X 0^2)^3-(C r*X 1*X 3)^3) (6,0) :=
    linkageGenerator_homogeneous .left r 1
  exact (regrade ((leftCoeff0_homogeneous i).mul hP) (by decide)).add
    (regrade ((leftCoeff1_homogeneous i).mul hQ) (by decide))

theorem polynomialRight_homogeneous (r : R) (j : Fin 3) :
    HG (polynomialRight r j) (8,1) := baseRow0_homogeneous r j

/-- Homogeneous projection of the literal factor numerator selects exactly
its degree-10 and degree-8 factor components, with the original characters. -/
theorem numerator_component (r : R) (V W : Fin 3 → Poly R) (d : Grade) (i j : Fin 3) :
    weightedHomogeneousComponent fullGrading (d+(18,1))
      (V i*polynomialRight r j+polynomialLeft r i*W j)=
      weightedHomogeneousComponent fullGrading (d+(10,0)) (V i)*polynomialRight r j+
      polynomialLeft r i*weightedHomogeneousComponent fullGrading (d+(8,1)) (W j) := by
  rw [map_add]
  have he : d+(18,1)=(d+(10,0))+(8,1) := by
    apply Prod.ext
    · change d.1+18=(d.1+10)+8
      omega
    · change d.2+1=(d.2+0)+1
      simp
  have he' : d+(18,1)=(10,0)+(d+(8,1)) := by
    apply Prod.ext
    · change d.1+18=10+(d.1+8)
      omega
    · change d.2+1=0+(d.2+1)
      simp
  rw [he,component_mul fullGrading (V i) (polynomialRight r j)
    (d+(10,0)) (8,1) (polynomialRight_homogeneous r j)]
  rw [← he,he',component_mul_left fullGrading (polynomialLeft r i) (W j)
    (10,0) (d+(8,1)) (polynomialLeft_homogeneous r i)]

end CycleQ2SeedFactorHomogeneous

#print axioms CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous
#print axioms CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous
#print axioms CycleQ2SeedFactorHomogeneous.numerator_component
end
end


/- Component: continuation_3/SeedLinkagePrincipal.lean -/
section
/-!
# Actual linkage pairings and principal factor ideals on pivot charts

All ideals and sections are the literal seed definitions. Local
principality uses the checked regularity of the actual denominator.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkagePrincipal

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2SegreTangentLocal CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageRegular
  CycleQ2CurveRestriction CycleQ2SeedQuotientFiniteFree

variable {R : Type*} [CommRing R]

def quotientMap (r ι : R) : Poly R →+* SeedRing r ι := Ideal.Quotient.mk _

def leftSection (r ι : R) (i : Fin 3) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.leftSection (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i)

def rightSection (r ι : R) (j : Fin 3) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.rightSectionNumerator (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j)

def linkage (r ι : R) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4))

theorem quotient_seedG (r ι : R) : quotientMap r ι (seedG r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (smoothSeed_mem_iff_linkage r ι).mpr ⟨0,1,by simp⟩

theorem leftSection_mem (r ι : R) (i : Fin 3) :
    leftSection r ι i ∈ linkageIdeal .left r ι := by
  have h0 := linkageGenerator_mem .left r ι 0
  have h1 := linkageGenerator_mem .left r ι 1
  change quotientMap r ι (CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)) ∈ _ at h0
  change quotientMap r ι ((X 0^2)^3-(C r*X 1*X 3)^3) ∈ _ at h1
  unfold leftSection CycleQ2SegreSeed.leftSection
  rw [map_add,map_mul,map_mul]
  exact (linkageIdeal .left r ι).add_mem
    ((linkageIdeal .left r ι).mul_mem_left _ h0)
    ((linkageIdeal .left r ι).mul_mem_left _ h1)

theorem rightSection_mem (r ι : R) (j : Fin 3) :
    rightSection r ι j ∈ linkageIdeal .right r ι := by
  have h0 := linkageGenerator_mem .right r ι 0
  have h2 := linkageGenerator_mem .right r ι 2
  have h3 := linkageGenerator_mem .right r ι 3
  change quotientMap r ι (CycleQ2SegreSeed.linkageP (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)) ∈ _ at h0
  change quotientMap r ι ((X 0^2)^2*(C r*X 1*X 3)-X 4*(X 2^2)^2) ∈ _ at h2
  change quotientMap r ι ((X 0^2)*(C r*X 1*X 3)^2+(X 4)^2*(X 2^2)) ∈ _ at h3
  unfold rightSection CycleQ2SegreSeed.rightSectionNumerator CycleQ2SegreSeed.baseRow0
    CycleQ2SegreSeed.coreRight0
  rw [map_add,map_add,map_mul,map_mul,map_mul]
  exact (linkageIdeal .right r ι).add_mem
    ((linkageIdeal .right r ι).add_mem
      ((linkageIdeal .right r ι).mul_mem_right _ h0)
      ((linkageIdeal .right r ι).mul_mem_right _ h2))
    ((linkageIdeal .right r ι).mul_mem_right _ h3)

theorem generator_pairing (r ι : R) (i j : Fin 5) :
    quotientMap r ι (linkageGenerator .left r i) *
      quotientMap r ι (linkageGenerator .right r j) =
      linkage r ι * quotientMap r ι
        (CycleQ2SegreSeed.linkageQ (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) i j) := by
  change quotientMap r ι (CycleQ2SegreSeed.linkageE _ _ _ _ i)*
    quotientMap r ι (CycleQ2SegreSeed.linkageEprime _ _ _ _ j)=_
  rw [← map_mul,CycleQ2SegreSeed.linkage_pairing,map_add,map_mul,map_mul]
  change _+quotientMap r ι (seedG r)*_=_
  rw [quotient_seedG,zero_mul,add_zero]
  rfl

theorem ideals_pairing (r ι : R) :
    linkageIdeal .left r ι * linkageIdeal .right r ι ≤ Ideal.span {linkage r ι} := by
  unfold linkageIdeal
  rw [Ideal.span_mul_span']
  apply Ideal.span_le.mpr
  rintro x ⟨y,⟨i,rfl⟩,z,⟨j,rfl⟩,rfl⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨quotientMap r ι
    (CycleQ2SegreSeed.linkageQ (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) i j), ?_⟩
  exact generator_pairing r ι i j

theorem selected_product (r ι : R) (i j : Fin 3) :
    leftSection r ι i*rightSection r ι j=linkage r ι*seedQuotientMatrix r ι i j := by
  unfold leftSection rightSection
  rw [← map_mul,CycleQ2SegreSeed.selected_product_identity,map_add,map_mul,map_mul]
  change _+quotientMap r ι (seedG r)*_=_
  rw [quotient_seedG,zero_mul,add_zero]
  rfl

section Maps
variable {S : Type*} [CommRing S]

theorem mapped_ideals_pairing (r ι : R) (φ : SeedRing r ι →+* S) :
    (linkageIdeal .left r ι).map φ * (linkageIdeal .right r ι).map φ ≤
      Ideal.span {φ (linkage r ι)} := by
  rw [← Ideal.map_mul]
  have h := Ideal.map_mono (f:=φ) (ideals_pairing r ι)
  simpa only [Ideal.map_span,Set.image_singleton] using h

theorem mapped_ideals_principal (r ι : R) (φ : SeedRing r ι →+* S)
    (hp : Function.Injective (fun x : S => φ (linkage r ι)*x))
    (i j : Fin 3) (hunit : IsUnit (φ (seedQuotientMatrix r ι i j))) :
    (linkageIdeal .left r ι).map φ=Ideal.span {φ (leftSection r ι i)} ∧
      (linkageIdeal .right r ι).map φ=Ideal.span {φ (rightSection r ι j)} := by
  apply CycleQ2LinkageIdealPrincipal.ideals_principal _ _ (φ (linkage r ι))
    (φ (leftSection r ι i)) (φ (rightSection r ι j))
    (φ (seedQuotientMatrix r ι i j)) hp hunit
    (Ideal.mem_map_of_mem φ (leftSection_mem r ι i))
    (Ideal.mem_map_of_mem φ (rightSection_mem r ι j))
  · simpa only [map_mul] using congrArg φ (selected_product r ι i j)
  · intro x hx y hy
    exact Ideal.mem_span_singleton.mp
      (mapped_ideals_pairing r ι φ (Ideal.mul_mem_mul hx hy))
end Maps

/-- On every localization chart with a unit literal matrix entry, both
actual factor ideals are generated by the corresponding chosen sections.
No regularity premise remains for the seed over a field. -/
theorem localized_ideals_principal {K : Type*} [Field K] (r ι : K) (hι : ι≠1)
    (M : Submonoid (SeedRing r ι)) (S : Type*) [CommRing S]
    [Algebra (SeedRing r ι) S] [IsLocalization M S]
    (i j : Fin 3) (hu : IsUnit (algebraMap (SeedRing r ι) S (seedQuotientMatrix r ι i j))) :
    (linkageIdeal .left r ι).map (algebraMap (SeedRing r ι) S)=
      Ideal.span {algebraMap (SeedRing r ι) S (leftSection r ι i)} ∧
    (linkageIdeal .right r ι).map (algebraMap (SeedRing r ι) S)=
      Ideal.span {algebraMap (SeedRing r ι) S (rightSection r ι j)} := by
  apply mapped_ideals_principal r ι (algebraMap (SeedRing r ι) S) _ i j hu
  exact CycleQ2LinkageIdealPrincipal.localization_mul_injective M S _
    (linkage_mul_injective r ι hι)

end CycleQ2SeedLinkagePrincipal

#print axioms CycleQ2SeedLinkagePrincipal.ideals_pairing
#print axioms CycleQ2SeedLinkagePrincipal.localized_ideals_principal
end
end


/- Component: continuation_3/SeedLinkageReflection.lean -/
section
/-! Sound sparse checks for actual five-variable normal forms of the literal
linkage sections.  Polynomial equality is proved over every ring of
characteristic109; finite computations do not assume any matrix rank. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageReflection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobian CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection
  CycleQ2SeedLinkageIdeals CycleQ2SparseModularPolynomial

def fullCoefficient (e : SourceTuple) : Sparse → ℕ
  | [] => 0
  | a::p => ((if a.1=e then a.2 else 0)+fullCoefficient e p)%109

def fullGood (d ch : ℕ) (p : Sparse) : Bool := p.all (fun a => sourceGood d ch a.1)

noncomputable section
variable {R : Type*} [CommRing R]

def fullValue [CharP R 109] (p : Sparse) : Poly R :=
  CycleQ2SparseModularPolynomial.eval (fun i : Fin 5 => X i) p

@[simp] theorem fullValue_nil [CharP R 109] : fullValue (R:=R) []=0 := rfl

@[simp] theorem fullValue_cons [CharP R 109] (a : Term) (p : Sparse) :
    fullValue (R:=R) (a::p)=termValue (fun i : Fin 5 => (X i : Poly R)) a+fullValue p := rfl

theorem sourceTupleExponent_injective : Function.Injective sourceTupleExponent := by
  intro e f h
  have h0 := congrArg (fun q : FullExponent => q 0) h
  have h1 := congrArg (fun q : FullExponent => q 1) h
  have h2 := congrArg (fun q : FullExponent => q 2) h
  have h3 := congrArg (fun q : FullExponent => q 3) h
  have h4 := congrArg (fun q : FullExponent => q 4) h
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

theorem termValue_variables [CharP R 109] (a : Term) :
    termValue (fun i : Fin 5 => (X i : Poly R)) a =
      MvPolynomial.monomial (sourceTupleExponent a.1) (a.2:R) := by
  change (a.2 : Poly R)*sourceMonomial a.1=_
  rw [sourceMonomial_eq_monomial]
  rw [←map_natCast (C : R →+* Poly R) a.2,C_mul_monomial,mul_one]

theorem fullValue_coefficient [CharP R 109] (e : SourceTuple) (p : Sparse) :
    (fullValue (R:=R) p).coeff (sourceTupleExponent e)=(fullCoefficient e p:R) := by
  induction p with
  | nil => simp [fullCoefficient]
  | cons a p ih =>
    rw [fullValue_cons,coeff_add,termValue_variables,coeff_monomial,ih]
    by_cases he : a.1=e
    · simp [fullCoefficient,he,←CharP.cast_eq_mod R 109,Nat.cast_add]
    · have he' : sourceTupleExponent a.1≠sourceTupleExponent e :=
        fun h => he (sourceTupleExponent_injective h)
      simp only [fullCoefficient,if_neg he,if_neg he',←CharP.cast_eq_mod R 109,Nat.cast_add,Nat.cast_zero]

theorem fullGood_term [CharP R 109] (d ch : ℕ) (a : Term)
    (ha : sourceGood d ch a.1=true) :
    FullStandard (termValue (fun i : Fin 5 => (X i : Poly R)) a) ∧
      HG (termValue (fun i : Fin 5 => (X i : Poly R)) a) (d,(ch:ZMod 3)) := by
  have hm : termValue (fun i : Fin 5 => (X i : Poly R)) a=C (a.2:R)*sourceMonomial a.1 := by
    rw [termValue_variables,sourceMonomial_eq_monomial,C_mul_monomial,mul_one]
  rw [hm]
  have h := sourceGood_evaluation (R:=R) d ch a.1 ha
  exact ⟨fullStandard_C_mul h.1 _,h.2.C_mul _⟩

theorem fullGood_value [CharP R 109] (d ch : ℕ) (p : Sparse)
    (hp : fullGood d ch p=true) :
    FullStandard (fullValue (R:=R) p) ∧ HG (fullValue (R:=R) p) (d,(ch:ZMod 3)) := by
  induction p with
  | nil => exact ⟨by simp [FullStandard],(weightedHomogeneousSubmodule R fullGrading (d,(ch:ZMod 3))).zero_mem⟩
  | cons a p ih =>
    simp only [fullGood,List.all_cons,Bool.and_eq_true] at hp
    have ha := fullGood_term (R:=R) d ch a hp.1
    have hb := ih hp.2
    rw [fullValue_cons]
    exact ⟨fullStandard_add ha.1 hb.1,ha.2.add hb.2⟩

theorem checked_seedNormal [CharP R 109] [Nontrivial R]
    (r ι : R) (d ch : ℕ) (p n a b h g : Sparse)
    (hh : fullValue (R:=R) h=smoothH ι) (hg : fullValue (R:=R) g=seedG r)
    (hn : fullGood d ch n=true) (hc : checkZero (CycleQ2CurveRestrictionReflection.residual p n a b h g)=true) :
    seedNormal r ι (fullValue p)=fullValue n := by
  have hz := eval_eq_zero_of_check (fun i : Fin 5 => (X i : Poly R)) _ hc
  simp only [CycleQ2CurveRestrictionReflection.residual,CycleQ2SparseModularPolynomial.eval_add,
    CycleQ2SparseModularPolynomial.eval_neg,CycleQ2SparseModularPolynomial.eval_mul] at hz
  change fullValue p+ -(fullValue n+(fullValue a*fullValue h+fullValue b*fullValue g))=0 at hz
  rw [hh,hg] at hz
  symm
  apply seedNormal_unique r ι (fullValue p) (fullValue n) (fullValue a) (fullValue b)
  · exact (fullGood_value d ch n hn).1
  · linear_combination hz

end
end CycleQ2SeedLinkageReflection

#print axioms CycleQ2SeedLinkageReflection.checked_seedNormal
#print axioms CycleQ2SeedLinkageReflection.fullValue_coefficient
end


/- Component: continuation_3/SeedLinkageSections.lean -/
section
/-! Homogeneous monomial multiples of the literal linkage generators, and
the exact finite-minor criterion for their independence in the seed quotient. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageSections

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection CycleQ2SeedLinkageIdeals

abbrev SectionColumn := Fin 5 × SourceTuple

def tupleDegree (e : SourceTuple) : ℕ :=
  e.1+e.2.1+e.2.2.1+e.2.2.2.1+2*e.2.2.2.2

def tupleCharacter (e : SourceTuple) : ℕ := 2*e.1+2*e.2.1+e.2.2.1

def sectionGood (d ch : ℕ) (c : SectionColumn) : Bool :=
  decide (tupleDegree c.2+generatorDegree c.1=d ∧
    (tupleCharacter c.2+generatorCharacter c.1)%3=ch)

noncomputable section
variable {R : Type*} [CommRing R]

def sectionPolynomial (s : Side) (r : R) (c : SectionColumn) : Poly R :=
  sourceMonomial c.2*linkageGenerator s r c.1

@[simp] theorem map_sectionPolynomial {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (c : SectionColumn) :
    MvPolynomial.map φ (sectionPolynomial s r c)=sectionPolynomial s (φ r) c := by
  simp only [sectionPolynomial,map_mul,map_sourceMonomial,map_linkageGenerator]

theorem sourceMonomial_grade (e : SourceTuple) :
    HG (sourceMonomial e : Poly R) (tupleDegree e,(tupleCharacter e:ZMod 3)) := by
  rw [sourceMonomial_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [fullGrading_weight]
  rfl

theorem sectionPolynomial_homogeneous (s : Side) (r : R) (d ch : ℕ)
    (c : SectionColumn) (hc : sectionGood d ch c=true) :
    HG (sectionPolynomial s r c) (d,(ch:ZMod 3)) := by
  have h : tupleDegree c.2+generatorDegree c.1=d ∧
      (tupleCharacter c.2+generatorCharacter c.1)%3=ch := of_decide_eq_true hc
  have hg := (sourceMonomial_grade (R:=R) c.2).mul (linkageGenerator_homogeneous s r c.1)
  have he : (tupleDegree c.2,(tupleCharacter c.2:ZMod 3))+
      (generatorDegree c.1,(generatorCharacter c.1:ZMod 3))=(d,(ch:ZMod 3)) := by
    apply Prod.ext
    · exact h.1
    · have hh := congrArg (fun n : ℕ => (n:ZMod 3)) h.2
      simpa using hh
  exact he ▸ hg

def sectionClass (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : SeedPiece r ι d ch :=
  ⟨Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (sectionPolynomial s r c),
    Submodule.mem_map.mpr ⟨sectionPolynomial s r c,sectionPolynomial_homogeneous s r d ch c hc,rfl⟩⟩

def idealSection (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : linkagePiece s r ι d ch :=
  ⟨sectionClass s r ι d ch c hc,by
    change Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (sectionPolynomial s r c) ∈ linkageIdeal s r ι
    rw [sectionPolynomial,map_mul]
    exact Ideal.mul_mem_left _ _ (linkageGenerator_mem s r ι c.1)⟩

def sectionCoefficient [Nontrivial R] (s : Side) (r ι : R)
    (row : SourceTuple) (c : SectionColumn) : R :=
  (seedNormal r ι (sectionPolynomial s r c)).coeff (sourceTupleExponent row)

theorem sectionCoefficient_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (row : SourceTuple) (c : SectionColumn) :
    φ (sectionCoefficient s r ι row c)=sectionCoefficient s (φ r) (φ ι) row c := by
  unfold sectionCoefficient
  rw [←coeff_map,seedNormal_map,map_sectionPolynomial]

section Field
variable {K : Type*} [Field K]

theorem idealSections_independent_of_minor (s : Side) (r ι : K) (d ch n : ℕ)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    LinearIndependent K (fun j => idealSection s r ι d ch (columns j) (hcolumns j)) := by
  classical
  let A : Matrix (Fin n) (Fin n) K := fun i j => sectionCoefficient s r ι (rows i) (columns j)
  have hA : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (A.isUnit_iff_isUnit_det.mpr ((isUnit_iff_ne_zero).mpr hdet))
  refine (Fintype.linearIndependent_iff (R:=K)
    (v:=fun j => idealSection s r ι d ch (columns j) (hcolumns j))).mpr ?_
  intro v hv j
  let P : Poly K := ∑ k, v k • sectionPolynomial s r (columns k)
  have hz : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) P=0 := by
    have h := congrArg (fun q : linkagePiece s r ι d ch => q.val.val) hv
    change (Ideal.Quotient.mkₐ K (equationsIdeal (smoothH ι) (smoothF r ι))) P=0
    simp only [P,map_sum,map_smul]
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,
      idealSection,sectionClass,Ideal.Quotient.mkₐ_eq_mk] using h
  have hn : seedNormal r ι P=0 :=
    (seedNormal_eq_zero_iff r ι P).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hAv : A.mulVec v=0 := by
    funext i
    have hcoeff := congrArg (fun p : Poly K => p.coeff (sourceTupleExponent (rows i))) hn
    have hsum : (seedNormal r ι P).coeff (sourceTupleExponent (rows i))=A.mulVec v i := by
      simp only [P,map_sum,map_smul,coeff_sum,coeff_smul,RingHom.id_apply,
        Matrix.mulVec,dotProduct,A,sectionCoefficient]
      apply Finset.sum_congr rfl
      intro k hk
      exact mul_comm _ _
    rw [hsum,coeff_zero] at hcoeff
    exact hcoeff
  have hv0 : v=0 := hA (by simpa using hAv)
  exact congrFun hv0 j

theorem linkagePiece_rank_lower_bound (s : Side) (r ι : K) (d ch n : ℕ) (hch : ch<3)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    n ≤ Module.finrank K (linkagePiece s r ι d ch) := by
  letI : FiniteDimensional K (SeedPiece r ι d ch) :=
    Module.Finite.of_basis (seedPieceBasis r ι d ch hch)
  simpa using (idealSections_independent_of_minor s r ι d ch n rows columns hcolumns hdet).fintype_card_le_finrank

end Field
end
end CycleQ2SeedLinkageSections

#print axioms CycleQ2SeedLinkageSections.idealSections_independent_of_minor
#print axioms CycleQ2SeedLinkageSections.linkagePiece_rank_lower_bound
end


/- Component: continuation_3/SeedQuotientGrading.lean -/
section
/-! # Agreement of the coordinate grading with the polynomial grading -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedQuotientGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R]

def mergeExponent (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) : FullExponent :=
  Finsupp.equivFunOnFinite.symm ![e 0, d 0, d 1, d 2, e 1]

lemma coeff_curry (p : AddMonoidAlgebra R ((Fin 2 →₀ ℕ) × (Fin 3 →₀ ℕ)))
    (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((AddMonoidAlgebra.curryAlgEquiv R p).coeff e).coeff d = p.coeff (e, d) := rfl

lemma regroup_coeff_coeff (p : Poly R) (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d = p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d = _
  rw [coeff_curry, AddMonoidAlgebra.coeff_domCongr]
  have heq : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, d) =
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j, rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [heq]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

def outerExponent (ab : ShiftIndex) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val

lemma regroup_standard {p : Poly R} (hp : FullStandard p) : Standard (regroup R p) := by
  intro e he
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero (MvPolynomial.mem_support_iff.mp he)
  rw [regroup_coeff_coeff] at hd
  have hb := hp (mergeExponent e d) (MvPolynomial.mem_support_iff.mpr hd)
  exact ⟨hb.1, hb.2⟩

lemma nested_reduced [Nontrivial R] (r ι : R) {p : Nested R} (hp : Standard p) :
    Reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p := by
  intro e he
  rw [(nestedH_leading R ι).1, (nestedG_leading R r).1,
    single_three_le_iff, single_three_le_iff]
  exact ⟨Nat.not_le_of_lt (hp e he).1, Nat.not_le_of_lt (hp e he).2⟩

lemma quotientBasis_repr_reduced {A σ : Type*} [CommRing A]
    (m : MonomialOrder σ) (h F p : MvPolynomial σ A)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (d : reducedExponents m h F) :
    (quotientBasis m h F hh hF hcop).repr (Ideal.Quotient.mk (equationsIdeal h F) p) d =
      p.coeff d.val := by
  let E := reducedQuotientEquiv m h F hh hF hcop
  have he : E ⟨p, hp⟩ = Ideal.Quotient.mk (equationsIdeal h F) p := rfl
  change (MvPolynomial.basisRestrictSupport A (reducedExponents m h F)).repr
    (E.symm (Ideal.Quotient.mk (equationsIdeal h F) p)) d = _
  rw [← he, LinearEquiv.symm_apply_apply]
  rfl

lemma nestedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Nested R)
    (hp : Standard p) (ab : ShiftIndex) :
    (nestedBasis R r ι).repr (Ideal.Quotient.mk (nestedIdeal R r ι) p) ab =
      p.coeff (outerExponent ab) := by
  unfold nestedBasis
  erw [Module.Basis.repr_reindex_apply,
    quotientBasis_repr_reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p
      (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
      (nested_reduced R r ι hp)]
  rfl

lemma seedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) :
    (seedBasis R r ι).repr (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab =
      (regroup R p).coeff (outerExponent ab) := by
  change (nestedBasis R r ι).repr
    (Ideal.Quotient.mk (nestedIdeal R r ι) (regroup R p)) ab = _
  exact nestedBasis_repr_standard R r ι (regroup R p) (regroup_standard R hp) ab

lemma seedBasis_repr_standard_coeff [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d =
        p.coeff (mergeExponent (outerExponent ab) d) := by
  rw [seedBasis_repr_standard R r ι p hp, regroup_coeff_coeff]

def signedGrade (g : Grade) : LaurentGrade := ((g.1 : ℤ), g.2)

theorem mergeExponent_grade (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    signedGrade (Finsupp.weight fullGrading (mergeExponent (outerExponent ab) d)) =
      shiftedGrade ab (castExponent d) := by
  rw [fullGrading_weight]
  apply Prod.ext <;>
    simp [signedGrade, fullDegree, mergeExponent, outerExponent, shiftedGrade,
      Fin.sum_univ_succ, castExponent] <;> ring

@[simp] theorem baseToLaurent_coeff_cast (p : Base R) (d : Fin 3 →₀ ℕ) :
    (baseToLaurent R p).coeff (castExponent d) = p.coeff d :=
  Finsupp.mapDomain_apply castExponent_injective _ _

lemma standard_seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hs : FullStandard p) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  intro e he
  by_contra hne
  have hpos : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨d, rfl⟩ := (mem_range_castExponent e).mpr hpos
  rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hne
  have hh := congrArg signedGrade (hp hne)
  rw [mergeExponent_grade] at hh
  exact he hh

/-- Original five-variable homogeneity gives exactly the declared shifts in
all nine canonical quotient coordinates. -/
theorem seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  have hNg : HG N g := fullRemainder_preserves_grading
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) hp
  rw [hQ]
  exact standard_seedCoordinates_homogeneous R r ι N g hN hNg ab

theorem localized_polynomial_homogeneous [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (localizedCoordinates R r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)) ab) := by
  rw [localizedCoordinates_algebraMap]
  exact seedCoordinates_homogeneous R r ι p g hp ab

theorem signedGrade_injective : Function.Injective signedGrade := by
  intro a b hab
  apply Prod.ext
  · exact Nat.cast_injective (congrArg Prod.fst hab)
  · exact congrArg (fun g : LaurentGrade ↦ g.2) hab

/-- The original polynomial grading, allowing a signed target degree. -/
def SignedHomogeneous (p : Poly R) (g : LaurentGrade) : Prop :=
  ∀ e, p.coeff e ≠ 0 → signedGrade (Finsupp.weight fullGrading e) = g

theorem signedHomogeneous_iff (p : Poly R) (g : Grade) :
    SignedHomogeneous R p (signedGrade g) ↔ HG p g := by
  constructor
  · intro hp e he
    exact signedGrade_injective (hp e he)
  · intro hp e he
    exact congrArg signedGrade (hp he)

theorem seedCoordinates_signedHomogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hp : SignedHomogeneous R p g) (ab : ShiftIndex) :
    HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  by_cases hz : p = 0
  · subst p
    intro e he
    simp
  · obtain ⟨e, he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : HG p (Finsupp.weight fullGrading e) := by
      apply (signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    exact hg ▸ seedCoordinates_homogeneous R r ι p _ hh ab

/-- The standard normal form is homogeneous exactly when all nine
canonical coefficient polynomials have the corresponding shifted grades. -/
theorem standard_signedHomogeneous_iff_coordinates [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hs : FullStandard p) :
    SignedHomogeneous R p g ↔
      ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  constructor
  · intro hp ab
    exact seedCoordinates_signedHomogeneous R r ι p g hp ab
  · intro hc e he
    have hb := hs e (MvPolynomial.mem_support_iff.mpr he)
    let ab : ShiftIndex := (⟨e 0, hb.1⟩, ⟨e 4, hb.2⟩)
    let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1, e 2, e 3]
    have heq : mergeExponent (outerExponent ab) d = e := by
      ext i
      fin_cases i <;> simp [mergeExponent, outerExponent, ab, d]
    rw [← heq, mergeExponent_grade]
    by_contra hg
    have hz := hc ab (castExponent d) hg
    rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hz
    exact he (heq ▸ hz)

/-- Every homogeneous quotient class has a genuinely homogeneous polynomial
representative, with no grading assumption on a chosen initial lift. -/
theorem exists_signed_homogeneous_representative [Nontrivial R] (r ι : R)
    (q : SeedRing r ι) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr q ab))) :
    ∃ p : Poly R, FullStandard p ∧ SignedHomogeneous R p g ∧
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p = q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  refine ⟨N, hN, ?_, hQ.symm⟩
  apply (standard_signedHomogeneous_iff_coordinates R r ι N g hN).mpr
  rw [← hQ]
  exact hq

/-- Signed degree and cubic character of a Laurent monomial in the base variables. -/
def baseGrade : LaurentExponent →+ LaurentGrade where
  toFun e := (∑ i, e i, (2 * e 0 + e 1 : ℤ))
  map_zero' := by simp
  map_add' e f := by
    apply Prod.ext <;> simp [Finset.sum_add_distrib] <;> ring

theorem shiftedGrade_add (ab : ShiftIndex) (e f : LaurentExponent) :
    shiftedGrade ab (e + f) = shiftedGrade ab e + baseGrade f := by
  apply Prod.ext <;> simp [shiftedGrade, baseGrade, Finset.sum_add_distrib] <;> ring

theorem hasGrade_mul_T (ab : ShiftIndex) (g : LaurentGrade) (e : LaurentExponent)
    (p : Laurent (R := R)) (hp : HasGrade ab g p) :
    HasGrade ab (g + baseGrade e) (p * T R e) := by
  intro f hf
  rw [coeff_mul_T]
  apply hp
  intro hh
  apply hf
  calc
    shiftedGrade ab f = shiftedGrade ab ((f - e) + e) := by rw [sub_add_cancel]
    _ = shiftedGrade ab (f - e) + baseGrade e := shiftedGrade_add ab _ _
    _ = g + baseGrade e := by rw [hh]

theorem coordinates_fraction [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (q : SeedLocal R r ι s) (num : SeedRing r ι) (n : ℕ)
    (h : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) num) (ab : ShiftIndex) :
    baseToLaurent R ((seedBasis R r ι).repr num ab) =
      localizedCoordinates R r ι s q ab * T R (n • openExponent s) := by
  have hh := congrArg (fun z ↦ localizedCoordinates R r ι s z ab) h
  rw [coordinates_mul_base, localizedCoordinates_algebraMap] at hh
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

/-- The coordinate definition of a graded local section agrees with an
actual fraction having a polynomial numerator of the required original grade. -/
theorem localized_homogeneous_iff_fraction [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (q : SeedLocal R r ι s) (g : LaurentGrade) :
    (∀ ab, HasGrade ab g (localizedCoordinates R r ι s q ab)) ↔
      ∃ (n : ℕ) (p : Poly R),
        SignedHomogeneous R p (g + baseGrade (n • openExponent s)) ∧
        q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
          (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
          algebraMap (SeedRing r ι) (SeedLocal R r ι s)
            (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) := by
  constructor
  · intro hq
    obtain ⟨n, num, hn⟩ := IsLocalization.Away.surj
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) q
    have hn' : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
        algebraMap (SeedRing r ι) (SeedLocal R r ι s) num := by
      simpa only [map_pow] using hn
    have hnum (ab : ShiftIndex) :
        HasGrade ab (g + baseGrade (n • openExponent s))
          (baseToLaurent R ((seedBasis R r ι).repr num ab)) := by
      rw [coordinates_fraction R r ι s q num n hn' ab]
      exact hasGrade_mul_T R ab g _ _ (hq ab)
    obtain ⟨p, _, hp, hpn⟩ := exists_signed_homogeneous_representative R r ι num _ hnum
    refine ⟨n, p, hp, ?_⟩
    simpa only [hpn] using hn'
  · rintro ⟨n, p, hp, hfrac⟩ ab
    have hh := coordinates_fraction R r ι s q
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) n hfrac ab
    have hnum := seedCoordinates_signedHomogeneous R r ι p _ hp ab
    have hrep : localizedCoordinates R r ι s q ab =
        baseToLaurent R ((seedBasis R r ι).repr
          (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab) *
          T R (-(n • openExponent s)) := by
      have hm := congrArg (fun z ↦ z * T R (-(n • openExponent s))) hh
      simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm.symm
    rw [hrep]
    have hz := hasGrade_mul_T R ab _ (-(n • openExponent s)) _ hnum
    simpa only [map_neg, add_neg_cancel_right] using hz

end CycleQ2SeedQuotientGrading

#print axioms CycleQ2SeedQuotientGrading.localized_polynomial_homogeneous

#print axioms CycleQ2SeedQuotientGrading.localized_homogeneous_iff_fraction
end
end


/- Component: continuation_3/SegreComplexChartExact.lean -/
section
/-! # Actual complex Segre exactness on the coordinate Čech cover -/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreComplexChartExact

open MvPolynomial Matrix CycleQ2SegreComplexBasepoint CycleQ2SegreTangentLocal
  CycleQ2IncidenceFirstOrder CycleQ2SegreRelationsLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

abbrev Chart (s : Finset (Fin 3)) := SeedLocal ℂ 57 Complex.I s

theorem coordinate_remaining (j : Fin 3) :
    coordinate (remainingIndex j) = algebraMap (Base ℂ) ComplexSeedRing (X j) := by
  change Ideal.Quotient.mk _ (X (remainingIndex j)) =
    Ideal.Quotient.mk _ (remainingInclusion ℂ (X j))
  simp [remainingInclusion]

theorem base_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (Base ℂ) (coordinateLocalization ℂ s) (X j)) := by
  have hd : (X j : Base ℂ) ∣ baseProduct ℂ s := Finset.dvd_prod_of_mem X hj
  exact isUnit_of_dvd_unit ((algebraMap (Base ℂ) (coordinateLocalization ℂ s)).map_dvd hd)
    (IsLocalization.Away.algebraMap_isUnit (S := coordinateLocalization ℂ s) _)

theorem seed_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap ComplexSeedRing (Chart s) (coordinate (remainingIndex j))) := by
  rw [coordinate_remaining, ← IsScalarTower.algebraMap_apply (Base ℂ) ComplexSeedRing (Chart s)]
  rw [IsScalarTower.algebraMap_apply (Base ℂ) (coordinateLocalization ℂ s) (Chart s)]
  exact (base_coordinate_unit s j hj).map
    (algebraMap (coordinateLocalization ℂ s) (Chart s))

def chartMatrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Chart s) :=
  (algebraMap ComplexSeedRing (Chart s)).mapMatrix matrix

theorem chartMatrix_cofactors (s : Finset (Fin 3)) :
    CycleQ2SegreLocal.cofactors (chartMatrix s) = 0 := by
  rw [chartMatrix, ← map_cofactors]
  change (algebraMap ComplexSeedRing (Chart s)).mapMatrix
    (CycleQ2SegreLocal.cofactors (seedQuotientMatrix (57 : ℂ) Complex.I)) = 0
  rw [seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap ComplexSeedRing (Chart s) 0 = 0
  exact map_zero _

theorem chartMatrix_entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => chartMatrix s ij.1 ij.2)) = ⊤ := by
  obtain ⟨j,hj⟩ := hs
  let φ := algebraMap ComplexSeedRing (Chart s)
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem (remainingIndex j))
  have hu : IsUnit (φ (coordinate (remainingIndex j)^coordinatePower (remainingIndex j))) := by
    rw [map_pow]
    exact (seed_coordinate_unit s j hj).pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hu
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def, φ,
    chartMatrix, RingHom.mapMatrix_apply, Matrix.map_apply] using ht

/-- Actual complex local exactness with its basepoint-freeness premise
discharged by the nonconstructive arithmetic argument. -/
theorem coordinate_chart_relations_exact (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (Chart s)) :
    CycleQ2SegreRelations.relations (chartMatrix s) *ᵥ vector C = 0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (Chart s), cofactorDifferential (chartMatrix s) N = C :=
  entry_ideal_relations_exact _ _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

theorem coordinate_chart_ker_eq_range (s : Finset (Fin 3)) (hs : s.Nonempty) :
    LinearMap.ker (relationsLinear (chartMatrix s)) =
      LinearMap.range (cofactorDifferentialLinear (chartMatrix s)) :=
  entry_ideal_ker_eq_range _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

end CycleQ2SegreComplexChartExact

#print axioms CycleQ2SegreComplexChartExact.chartMatrix_entries_generate
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_relations_exact
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_ker_eq_range
end
end


/- Component: continuation_3/cylinder_bridge/SegreLinkageDuality.lean -/
section
/-! The literal regular linkage pairing is perfect wherever the actual
matrix entries generate the unit ideal.  The inverse is an explicit finite
sum coming from that unit-ideal identity; no duality or invertibility of
the two factor ideals is assumed. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreLinkageDuality
open Matrix CycleQ2SegreFactorSequence

variable {A : Type*} [CommRing A] (F : FactorData A)

def leftElement (i : Fin 3) : F.leftIdeal := ⟨F.left i,F.left_mem i⟩
def rightElement (j : Fin 3) : F.rightIdeal := ⟨F.right j,F.right_mem j⟩

theorem pair_divisible (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage ∣ (x:A)*(y:A) :=
  Ideal.mem_span_singleton.mp (F.ideals_product (Ideal.mul_mem_mul x.property y.property))

def pairValue (x : F.leftIdeal) (y : F.rightIdeal) : A := (pair_divisible F x y).choose

theorem linkage_pair (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage*pairValue F x y=(x:A)*(y:A) :=
  (pair_divisible F x y).choose_spec.symm

def pairing : F.rightIdeal →ₗ[A] (F.leftIdeal →ₗ[A] A) where
  toFun y :=
    { toFun := fun x => pairValue F x y
      map_add' x z := by
        apply F.regular
        change F.linkage*pairValue F (x+z) y=F.linkage*(pairValue F x y+pairValue F z y)
        rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
        change ((x:A)+(z:A))*(y:A)=(x:A)*(y:A)+(z:A)*(y:A)
        ring
      map_smul' c x := by
        apply F.regular
        change F.linkage*pairValue F (c • x) y=F.linkage*(c*pairValue F x y)
        rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
          linkage_pair,linkage_pair]
        change (c*(x:A))*(y:A)=c*((x:A)*(y:A))
        ring }
  map_add' y z := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (y+z)=F.linkage*(pairValue F x y+pairValue F x z)
    rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
    change (x:A)*((y:A)+(z:A))=(x:A)*(y:A)+(x:A)*(z:A)
    ring
  map_smul' c y := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (c • y)=F.linkage*(c*pairValue F x y)
    rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
      linkage_pair,linkage_pair]
    change (x:A)*(c*(y:A))=c*((x:A)*(y:A))
    ring

theorem pairing_selected (i j : Fin 3) :
    pairing F (rightElement F j) (leftElement F i)=F.matrix i j := by
  apply F.regular
  exact (linkage_pair F (leftElement F i) (rightElement F j)).trans (F.product i j)

theorem exists_weights :
    ∃ ξ : Fin 3 × Fin 3 → A, ∑ q, ξ q*F.matrix q.1 q.2=1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [F.entries_generate]
  exact Submodule.mem_top

def weights : Fin 3 × Fin 3 → A := (exists_weights F).choose

theorem weights_sum : ∑ q, weights F q*F.matrix q.1 q.2=1 :=
  (exists_weights F).choose_spec

theorem left_reconstruction (x : F.leftIdeal) :
    (x:A)=∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1 := by
  apply F.regular
  calc
    F.linkage*(x:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F (rightElement F q.2) x)*F.left q.1) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F x (rightElement F q.2)
      change F.linkage*pairing F (rightElement F q.2) x=(x:A)*F.right q.2 at hpair
      linear_combination
        -weights F q*(x:A)*(F.product q.1 q.2)-weights F q*F.left q.1*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1) :=
      (Finset.mul_sum ..).symm

theorem right_reconstruction (y : F.rightIdeal) :
    (y:A)=∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2 := by
  apply F.regular
  calc
    F.linkage*(y:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F y (leftElement F q.1))*F.right q.2) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F (leftElement F q.1) y
      change F.linkage*pairing F y (leftElement F q.1)=F.left q.1*(y:A) at hpair
      linear_combination
        -weights F q*(y:A)*(F.product q.1 q.2)-weights F q*F.right q.2*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2) :=
      (Finset.mul_sum ..).symm

theorem pairing_injective : Function.Injective (pairing F) := by
  intro y z hyz
  apply Subtype.ext
  rw [right_reconstruction F y,right_reconstruction F z]
  apply Finset.sum_congr rfl
  intro q _
  rw [show pairing F y (leftElement F q.1)=pairing F z (leftElement F q.1) from
    congrArg (fun f : F.leftIdeal →ₗ[A] A => f (leftElement F q.1)) hyz]

def dualInverse (φ : F.leftIdeal →ₗ[A] A) : F.rightIdeal :=
  ∑ q, (weights F q*φ (leftElement F q.1)) • rightElement F q.2

theorem pairing_dualInverse (φ : F.leftIdeal →ₗ[A] A) :
    pairing F (dualInverse F φ)=φ := by
  ext x
  have hx : x=∑ q, (weights F q*pairing F (rightElement F q.2) x) • leftElement F q.1 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul,leftElement] using
      left_reconstruction F x
  have hφ := congrArg φ hx
  simp only [map_sum,map_smul,smul_eq_mul] at hφ
  rw [dualInverse,map_sum,LinearMap.sum_apply]
  calc
    _=∑ q, (weights F q*φ (leftElement F q.1))*pairing F (rightElement F q.2) x := by
      apply Finset.sum_congr rfl
      intro q _
      rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
    _=φ x := by
      rw [hφ]
      apply Finset.sum_congr rfl
      intro q _
      ring

def rightEquivLeftDual : F.rightIdeal ≃ₗ[A] (F.leftIdeal →ₗ[A] A) :=
  LinearEquiv.ofBijective (pairing F)
    ⟨pairing_injective F,fun φ => ⟨dualInverse F φ,pairing_dualInverse F φ⟩⟩

end CycleQ2SegreLinkageDuality

#print axioms CycleQ2SegreLinkageDuality.pairing_selected
#print axioms CycleQ2SegreLinkageDuality.rightEquivLeftDual
end
end


