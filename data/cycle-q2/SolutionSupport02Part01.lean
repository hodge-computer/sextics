import Proposal.GeometricSurfaceCoordinates
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
import Proposal.GeometricTarget11Part04
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs04
import Proposal.Normalization09Part02
import Proposal.SolutionSupport01Part07
import Proposal.GeometricSeedNormalIdeals

/-! Components extracted from SolutionSupport02.lean, in their original order.
See solution.md for the mathematical and verification status. -/

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


