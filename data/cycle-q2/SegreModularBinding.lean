import Proposal.GeometricSurfaceBindings
import Proposal.GeometricIncidenceCechTrace
import Proposal.SegreCubicPairing

/-!
# Binding the modular Segre model

The literal modular tangent and relations, Gaussian interpretation, and correlation of the sparse polynomials.
-/

set_option Elab.async false

/- Component: continuation_3/SegreModularDataBinding.lean -/
section
/-! Literal finite-field seed data, bound to the actual raw matrix,
cofactor quotients, cubic, and sextic used by the basepoint proof.
The actual characteristic-zero trace-one tangent is proved separately. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace CycleQ2SegreModularTangent

open MvPolynomial CycleQ2SparseModularPolynomial CycleQ2IncidenceNormalForm
  CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceJacobian CycleQ2IncidenceCoefficientRelations

variable {R : Type*} [CommRing R] [CharP R 109]
abbrev P (R : Type*) [CommRing R] := MvPolynomial (Fin 5) R

def value (p : Blocks) : P R := evalBlocks X (X 0) (X 4) p

theorem value_add (p q : Blocks) :
    value (R := R) (addBlocks p q) = value p + value q :=
  eval_addBlocks X (X 0) (X 4) p q

theorem value_mul (p q : Blocks) :
    value (R := R) (mulBlocks p q) = value p * value q :=
  eval_mulBlocks X (X 0) (X 4) p q

theorem value_neg (p : Blocks) : value (R := R) (negBlocks p) = -value p :=
  eval_negBlocks X (X 0) (X 4) p

def matrixBlocks : Matrix (Fin 3) (Fin 3) Blocks :=
  ![
    ![CycleQ2SegreModularTangentData.m00, CycleQ2SegreModularTangentData.m01, CycleQ2SegreModularTangentData.m02],
    ![CycleQ2SegreModularTangentData.m10, CycleQ2SegreModularTangentData.m11, CycleQ2SegreModularTangentData.m12],
    ![CycleQ2SegreModularTangentData.m20, CycleQ2SegreModularTangentData.m21, CycleQ2SegreModularTangentData.m22]]

def quotientBlocks : Matrix (Fin 3) (Fin 3) Blocks :=
  ![
    ![CycleQ2SegreModularTangentData.q00, CycleQ2SegreModularTangentData.q01, CycleQ2SegreModularTangentData.q02],
    ![CycleQ2SegreModularTangentData.q10, CycleQ2SegreModularTangentData.q11, CycleQ2SegreModularTangentData.q12],
    ![CycleQ2SegreModularTangentData.q20, CycleQ2SegreModularTangentData.q21, CycleQ2SegreModularTangentData.q22]]

theorem value_rawMatrix (i j : Fin 3) : value (R := R) (matrixBlocks i j) =
    rawSeedMatrix (57 : R) i j := by
  have hc : CharP (P R) 109 := inferInstance
  fin_cases i <;> fin_cases j <;>
    simp only [
      matrixBlocks, CycleQ2SegreModularTangentData.m00, CycleQ2SegreModularTangentData.m01, CycleQ2SegreModularTangentData.m02,
      CycleQ2SegreModularTangentData.m10, CycleQ2SegreModularTangentData.m11, CycleQ2SegreModularTangentData.m12, CycleQ2SegreModularTangentData.m20,
      CycleQ2SegreModularTangentData.m21, CycleQ2SegreModularTangentData.m22, value, evalBlocks,
      evalLayers, CycleQ2SparseModularPolynomial.eval, CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, mul_zero,
      mul_one, zero_mul, zero_add, add_zero,
      rawSeedMatrix, CycleQ2SegreSeed.rawMatrix, CycleQ2SegreSeed.leftCoeff0, CycleQ2SegreSeed.leftCoeff1,
      CycleQ2SegreSeed.baseRow0, CycleQ2SegreSeed.baseRow1, CycleQ2SegreSeed.coreRight0, CycleQ2SegreSeed.coreRight1,
      CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2, CycleQ2SegreSeed.rightCoeff3, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat]
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!

theorem value_rawQuotient (i j : Fin 3) : value (R := R) (quotientBlocks i j) =
    CycleQ2IncidenceFirstOrder.rawCofactorQuotient (57 : R) i j := by
  have hc : CharP (P R) 109 := inferInstance
  fin_cases i <;> fin_cases j <;>
    simp only [
      quotientBlocks, CycleQ2SegreModularTangentData.q00, CycleQ2SegreModularTangentData.q01, CycleQ2SegreModularTangentData.q02,
      CycleQ2SegreModularTangentData.q10, CycleQ2SegreModularTangentData.q11, CycleQ2SegreModularTangentData.q12, CycleQ2SegreModularTangentData.q20,
      CycleQ2SegreModularTangentData.q21, CycleQ2SegreModularTangentData.q22, value, evalBlocks,
      evalLayers, CycleQ2SparseModularPolynomial.eval, CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, mul_zero,
      mul_one, zero_mul, zero_add, add_zero,
      CycleQ2IncidenceFirstOrder.rawCofactorQuotient, CycleQ2SegreSeed.rawCofactorQuotient, CycleQ2SegreSeed.cross, CycleQ2SegreSeed.leftCoeff0,
      CycleQ2SegreSeed.leftCoeff1, CycleQ2SegreSeed.rightCrossQuotient, CycleQ2SegreSeed.rightMinorQuotient, CycleQ2SegreSeed.coreMinorQuotient,
      CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2, CycleQ2SegreSeed.rightCoeff3, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat]
  all_goals
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!

theorem value_h : value (R := R) CycleQ2SegreModularTangentData.h = smoothH (33 : R) := by
  have hc : CharP (P R) 109 := inferInstance
  simp only [
    CycleQ2SegreModularTangentData.h, value, evalBlocks, evalLayers,
    CycleQ2SparseModularPolynomial.eval, CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_ofNat,
    pow_zero, pow_one, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, smoothH,
    smoothB, smoothA, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_ofNat]
  apply sub_eq_zero.mp
  ring_nf <;> reduce_mod_char!

theorem value_k : value (R := R) CycleQ2SegreModularTangentData.k = smoothK (33 : R) := by
  have hc : CharP (P R) 109 := inferInstance
  simp only [
    CycleQ2SegreModularTangentData.k, value, evalBlocks, evalLayers,
    CycleQ2SparseModularPolynomial.eval, CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_ofNat,
    pow_zero, pow_one, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, smoothK,
    smoothB, smoothA, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_ofNat]
  apply sub_eq_zero.mp
  ring_nf <;> reduce_mod_char!

theorem value_g : value (R := R) CycleQ2SegreModularTangentData.g = seedG (57 : R) := by
  have hc : CharP (P R) 109 := inferInstance
  simp only [
    CycleQ2SegreModularTangentData.g, value, evalBlocks, evalLayers,
    CycleQ2SparseModularPolynomial.eval, CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_ofNat,
    pow_zero, pow_one, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, seedG,
    CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_ofNat]
  apply sub_eq_zero.mp
  ring_nf <;> reduce_mod_char!

end CycleQ2SegreModularTangent

#print axioms CycleQ2SegreModularTangent.value_rawMatrix
#print axioms CycleQ2SegreModularTangent.value_rawQuotient
#print axioms CycleQ2SegreModularTangent.value_h
#print axioms CycleQ2SegreModularTangent.value_g
end
end

/- Component: continuation_3/cylinder_bridge/SegreRelationsExact.lean -/
section
/-! # Every unit-entry Segre chart has the actual cofactor/relations exactness

Even cyclic row and column permutations transport the explicit pivot lift.
Differentiating the universal polynomial relation supplies the reverse
inclusion, and the result is bound to the literal smooth seed quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace CycleQ2SegreRelationsLocal

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The even 3-cycle, so no cofactor sign correction is needed. -/
def cycle : Equiv.Perm (Fin 3) where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv := by decide
  right_inv := by decide

/-- The unique cyclic rotation carrying 0 to the chosen pivot coordinate. -/
def rotation (a : Fin 3) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _,cycle,cycle.trans cycle] a

theorem rotation_zero (a : Fin 3) : rotation a 0=a := by
  fin_cases a <;> rfl

theorem cofactors_rotate_rows (M : Matrix (Fin 3) (Fin 3) R) (a : Fin 3) :
    CycleQ2SegreLocal.cofactors (M.submatrix (rotation a) id)=
      (CycleQ2SegreLocal.cofactors M).submatrix (rotation a) id := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [CycleQ2SegreLocal.cofactors,Matrix.adjugate_fin_three,rotation,cycle,
      Matrix.submatrix_apply,Matrix.transpose_apply,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.reduceFinMk] <;> ring

theorem cofactors_rotate_cols (M : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    CycleQ2SegreLocal.cofactors (M.submatrix id (rotation b))=
      (CycleQ2SegreLocal.cofactors M).submatrix id (rotation b) := by
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [CycleQ2SegreLocal.cofactors,Matrix.adjugate_fin_three,rotation,cycle,
      Matrix.submatrix_apply,Matrix.transpose_apply,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.reduceFinMk] <;> ring

theorem cofactors_rotate (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    CycleQ2SegreLocal.cofactors (M.submatrix (rotation a) (rotation b))=
      (CycleQ2SegreLocal.cofactors M).submatrix (rotation a) (rotation b) := by
  have hh := cofactors_rotate_rows (M.submatrix id (rotation b)) a
  rw [cofactors_rotate_cols] at hh
  simpa only [Matrix.submatrix_submatrix,Function.id_comp,Function.comp_id] using hh

theorem differential_rotate (M N : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    cofactorDifferential (M.submatrix (rotation a) (rotation b))
      (N.submatrix (rotation a) (rotation b))=
      (cofactorDifferential M N).submatrix (rotation a) (rotation b) := by
  unfold cofactorDifferential
  change CycleQ2SegreLocal.cofactors ((M+N).submatrix (rotation a) (rotation b)) -
    CycleQ2SegreLocal.cofactors (M.submatrix (rotation a) (rotation b)) -
    CycleQ2SegreLocal.cofactors (N.submatrix (rotation a) (rotation b)) = _
  rw [cofactors_rotate,cofactors_rotate,cofactors_rotate]
  rfl

theorem leftProduct_submatrix (M C : Matrix (Fin 3) (Fin 3) R)
    (e f : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    leftProduct (M.submatrix e f) (C.submatrix e f) i j=
      leftProduct M C (e i) (e j) := by
  exact Equiv.sum_comp f (fun k => M (e i) k*C (e j) k)

theorem rightProduct_submatrix (M C : Matrix (Fin 3) (Fin 3) R)
    (e f : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    rightProduct (M.submatrix e f) (C.submatrix e f) i j=
      rightProduct M C (f i) (f j) := by
  exact Equiv.sum_comp e (fun k => M k (f i)*C k (f j))

/-- The explicit pivot lift transported to an arbitrary unit-entry chart. -/
def unitChartLift (i0 j0 : Fin 3) (u : Rˣ) (C : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  (pivotLift u (C.submatrix (rotation i0) (rotation j0))).submatrix
    (rotation i0).symm (rotation j0).symm

theorem unitChartLift_differential (M C : Matrix (Fin 3) (Fin 3) R)
    (hl : ∀ i j, leftProduct M C i j=0)
    (hr : ∀ i j, rightProduct M C i j=0)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    cofactorDifferential M (unitChartLift i0 j0 u C)=C := by
  have hL (i j : Fin 3) :
      leftProduct (M.submatrix (rotation i0) (rotation j0))
        (C.submatrix (rotation i0) (rotation j0)) i j=0 := by
    rw [leftProduct_submatrix,hl]
  have hR (i j : Fin 3) :
      rightProduct (M.submatrix (rotation i0) (rotation j0))
        (C.submatrix (rotation i0) (rotation j0)) i j=0 := by
    rw [rightProduct_submatrix,hr]
  have hp : (u : R)=(M.submatrix (rotation i0) (rotation j0)) 0 0 := by
    simpa only [Matrix.submatrix_apply,rotation_zero] using hu
  have hh := pivotLift_differential _ _ hL hR u hp
  have hrot := differential_rotate M (unitChartLift i0 j0 u C) i0 j0
  have hback : (unitChartLift i0 j0 u C).submatrix (rotation i0) (rotation j0)=
      pivotLift u (C.submatrix (rotation i0) (rotation j0)) := by
    ext i j
    simp [unitChartLift]
  rw [hback,hh] at hrot
  ext i j
  have hij := congrArg (fun A : Matrix (Fin 3) (Fin 3) R =>
    A ((rotation i0).symm i) ((rotation j0).symm j)) hrot
  simpa using hij.symm

/-- The polynomial derivative of the sixteen universal relations. -/
theorem relations_differential (M N : Matrix (Fin 3) (Fin 3) R) :
    CycleQ2SegreRelations.relations M *ᵥ vector (cofactorDifferential M N)+
      CycleQ2SegreRelations.relations N *ᵥ vector (CycleQ2SegreLocal.cofactors M)=0 := by
  rw [relations_mul_vector,relations_mul_vector,cofactorDifferential_fin_three]
  funext k
  fin_cases k <;>
    norm_num [leftProduct,rightProduct,Fin.sum_univ_succ,
      CycleQ2SegreLocal.cofactors,Matrix.adjugate_fin_three,Matrix.cons_val_succ,Matrix.cons_val_two,Fin.reduceFinMk] <;> ring

theorem relations_cofactorDifferential (M N : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0) :
    CycleQ2SegreRelations.relations M *ᵥ vector (cofactorDifferential M N)=0 := by
  have hh := relations_differential M N
  have hz : vector (0 : Matrix (Fin 3) (Fin 3) R)=0 := by
    funext k
    fin_cases k <;> rfl
  rw [hM,hz,Matrix.mulVec_zero,add_zero] at hh
  exact hh

/-- Exactness at the nine cofactor-variation coordinates on every unit chart,
with the actual sixteen relation rows and actual cofactor differential. -/
theorem unit_pivot_relations_exact (M C : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M=0)
    (i0 j0 : Fin 3) (u : Rˣ) (hu : (u : R)=M i0 j0) :
    CycleQ2SegreRelations.relations M *ᵥ vector C=0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) R, cofactorDifferential M N=C := by
  constructor
  · intro h
    obtain ⟨hl,hr⟩ := (relations_zero_iff_products_zero M C hM i0 j0 u hu).mp h
    exact ⟨unitChartLift i0 j0 u C,unitChartLift_differential M C hl hr i0 j0 u hu⟩
  · rintro ⟨N,rfl⟩
    exact relations_cofactorDifferential M N hM

/-- The same exactness on the literal smooth seed quotient, whose cofactor
vanishing follows from the checked polynomial seed identity. -/
theorem seed_quotient_relations_exact (r ι : R)
    (C : Matrix (Fin 3) (Fin 3) (SeedRing r ι))
    (i0 j0 : Fin 3) (u : (SeedRing r ι)ˣ)
    (hu : (u : SeedRing r ι)=seedQuotientMatrix r ι i0 j0) :
    CycleQ2SegreRelations.relations (seedQuotientMatrix r ι) *ᵥ vector C=0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (SeedRing r ι),
        cofactorDifferential (seedQuotientMatrix r ι) N=C :=
  unit_pivot_relations_exact _ _ (seedQuotientMatrix_cofactors r ι) i0 j0 u hu

end CycleQ2SegreRelationsLocal

#print axioms CycleQ2SegreRelationsLocal.unit_pivot_relations_exact
#print axioms CycleQ2SegreRelationsLocal.seed_quotient_relations_exact
end
end

/- Component: continuation_3/SparseGaussianActionSemantics.lean -/
section
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
variable (a₀ a₁ b₀ : Layers)
variable (hz : z^3 = evalLayers φ x v a₀ + evalLayers φ x v a₁ * z)
variable (hw : w^3 = evalLayers φ x v b₀ - z^6)
include hz hw

/-- A checked normal-form table entry has the correct evaluation under the
actual monic relations; the table itself is not a trusted computation. -/
theorem evaluation_of_normal_error_check (fuel : ℕ) (p result : Towers)
    (h : checkTowers (addTowers (normalizeTower a₀ a₁ b₀ fuel p)
      (negTowers result)) = true) :
    evalTowers φ x w z v result = evalTowers φ x w z v p := by
  have he := evalTowers_eq_zero_of_checkTowers φ x w z v _ h
  rw [eval_addTowers, eval_negTowers,
    eval_normalizeTower φ x w z v a₀ a₁ b₀ hz hw] at he
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)).symm

theorem monomial_action_of_normal_error_check (fuel : ℕ) (p result : Towers) (a b : ℕ)
    (h : checkTowers (addTowers
      (normalizeTower a₀ a₁ b₀ fuel (mulTowers p (monomialTower oneLayers a b)))
      (negTowers result)) = true) :
    evalTowers φ x w z v result = evalTowers φ x w z v p * z^a * w^b := by
  rw [evaluation_of_normal_error_check φ x w z v a₀ a₁ b₀ hz hw fuel _ result h,
    eval_mulTowers, eval_monomialTower, eval_oneLayers, mul_one]
  ring

end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.monomial_action_of_normal_error_check
end

/- Component: continuation_3/SparseGaussianStandardness.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
namespace CycleQ2SparseGaussianPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceJacobian

def standardTerm (t : Term) : Bool := decide (t.1.1<3 ∧ t.1.2.2.2.2<3)
def standardPolynomial (p : Sparse) : Bool := p.all standardTerm

theorem standardPolynomial_shift_free (u v w : ℕ) (p : Sparse) :
    standardPolynomial (shift (0,u,v,w,0) p)=standardPolynomial p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [shift,List.map_cons,standardPolynomial,List.all_cons] at *
    rw [ih]
    simp only [standardTerm,exponentAdd,Nat.zero_add]

noncomputable section
variable {R : Type*} [CommRing R] (φ : GaussianInt →+* R)

theorem standardTerm_evaluation (t : Term) (h : standardTerm t=true) :
    FullStandard (termValue (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) t) := by
  have ht : t.1.1<3 ∧ t.1.2.2.2.2<3 := of_decide_eq_true h
  rw [termValue_variables]
  intro e he
  have heq : e=tupleExponent t.1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  exact ht

theorem standardPolynomial_evaluation (p : Sparse) (h : standardPolynomial p=true) :
    FullStandard (eval (MvPolynomial.C.comp φ)
      (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) := by
  induction p with
  | nil => simp [FullStandard]
  | cons t p ih =>
    simp only [standardPolynomial,List.all_cons,Bool.and_eq_true] at h
    rw [eval_cons]
    exact fullStandard_add (standardTerm_evaluation φ t h.1) (ih h.2)

theorem standardPolynomial_free_product (u v w : ℕ) (p : Sparse)
    (h : standardPolynomial p=true) :
    FullStandard (MvPolynomial.monomial (tupleExponent (0,u,v,w,0)) 1 *
      eval (MvPolynomial.C.comp φ)
        (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) R) p) := by
  have hs : standardPolynomial (shift (0,u,v,w,0) p)=true := by
    rw [standardPolynomial_shift_free]; exact h
  have he := standardPolynomial_evaluation φ (shift (0,u,v,w,0) p) hs
  rwa [eval_shift,monomial_variables] at he
end
end CycleQ2SparseGaussianPolynomial
#print axioms CycleQ2SparseGaussianPolynomial.standardPolynomial_free_product
end

/- Component: continuation_3/SparseModularCorrelation.lean -/
section
/-! Polynomial correlation for the actual packed coefficient functionals.

This is a proved arithmetic implementation. Packed multiplication computes all
shifts together; the coefficient bound rules out carries between base digits.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularCorrelation
open Polynomial CycleQ2SparseModularFunctional CycleQ2SparseModularFastDot

def pack (B : ℕ) : List WordTerm → ℕ
  | [] => 0
  | t::p => t.2 * CycleQ2BinaryNaturalPower.power B 12 t.1 + pack B p

def reverseWord (B : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | f+1, n, a =>
      if n=0 then a * CycleQ2BinaryNaturalPower.power B 12 (f+1)
      else reverseWord B f (n/256) (a*B+n%256)

def packedDot (B K : ℕ) (W : WeightData) (i j : Fin 3) : List FastBlock → ℕ
  | [] => 0
  | b::p =>
      let n := W i j b.1 b.2.1
      if n=0 then packedDot B K W i j p
      else pack B b.2.2 * reverseWord B (K+1) n 0 + packedDot B K W i j p

def coefficientSum : List WordTerm → ℕ
  | [] => 0
  | t::p => t.2+coefficientSum p

def totalCoefficients : List FastBlock → ℕ
  | [] => 0
  | b::p => coefficientSum b.2.2+totalCoefficients p

def rawWord (n s : ℕ) : List WordTerm → ℕ
  | [] => 0
  | t::p => t.2*slot n (s+t.1)+rawWord n s p

def rawDot (W : WeightData) (i j : Fin 3) (s : ℕ) : List FastBlock → ℕ
  | [] => 0
  | b::p => rawWord (W i j b.1 b.2.1) s b.2.2+rawDot W i j s p

noncomputable def actionPolynomial : List WordTerm → ℕ[X]
  | [] => 0
  | t::p => monomial t.1 t.2+actionPolynomial p

noncomputable def wordPolynomial : ℕ → ℕ → ℕ[X]
  | 0, _ => 0
  | f+1, n => monomial f (n%256)+wordPolynomial f (n/256)

noncomputable def dotPolynomial (K : ℕ) (W : WeightData) (i j : Fin 3) :
    List FastBlock → ℕ[X]
  | [] => 0
  | b::p => actionPolynomial b.2.2 * wordPolynomial (K+1) (W i j b.1 b.2.1)+
      dotPolynomial K W i j p

theorem pack_eq_eval (B : ℕ) (p : List WordTerm) :
    pack B p=(actionPolynomial p).eval B := by
  induction p with
  | nil => simp [pack,actionPolynomial]
  | cons t p ih =>
    simp only [pack,actionPolynomial,eval_add,eval_monomial,
      CycleQ2BinaryNaturalPower.power_eq,ih]

theorem wordPolynomial_zero (f : ℕ) : wordPolynomial f 0=0 := by
  induction f with
  | zero => rfl
  | succ f ih => simp [wordPolynomial,ih]

theorem wordPolynomial_coeff (f n k : ℕ) :
    (wordPolynomial f n).coeff k=
      if k<f then (n/256^(f-1-k))%256 else 0 := by
  induction f generalizing n k with
  | zero => simp [wordPolynomial]
  | succ f ih =>
    rw [wordPolynomial,coeff_add,coeff_monomial,ih]
    by_cases h : f=k
    · subst k
      simp
    · by_cases hk : k<f
      · have hk' : k<f+1 := by omega
        have he : f+1-1-k=(f-1-k)+1 := by omega
        simp only [if_neg h,if_pos hk,if_pos hk',zero_add]
        rw [he,Nat.div_div_eq_div_mul,pow_succ']
      · have hk' : ¬k<f+1 := by omega
        simp only [if_neg h,if_neg hk,if_neg hk',add_zero]

theorem wordPolynomial_bound (f n k : ℕ) : (wordPolynomial f n).coeff k<256 := by
  rw [wordPolynomial_coeff]
  split_ifs
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem reverseWord_eq_eval (B f n a : ℕ) :
    reverseWord B f n a=a*B^f+(wordPolynomial f n).eval B := by
  induction f generalizing n a with
  | zero => simp [reverseWord,wordPolynomial]
  | succ f ih =>
    rw [reverseWord]
    split_ifs with h
    · subst n
      rw [wordPolynomial_zero]
      simp only [eval_zero,add_zero,CycleQ2BinaryNaturalPower.power_eq]
    · rw [ih,wordPolynomial,eval_add,eval_monomial,pow_succ]
      ring

theorem packedDot_eq_eval (B K : ℕ) (W : WeightData) (i j : Fin 3)
    (p : List FastBlock) :
    packedDot B K W i j p=(dotPolynomial K W i j p).eval B := by
  induction p with
  | nil => simp [packedDot,dotPolynomial]
  | cons b p ih =>
    simp only [packedDot,dotPolynomial,eval_add,eval_mul]
    split_ifs with h
    · rw [h,wordPolynomial_zero,eval_zero,mul_zero,zero_add,ih]
    · rw [pack_eq_eval,reverseWord_eq_eval,zero_mul,zero_add,ih]

theorem action_mul_coefficient_bound (f n k : ℕ) (p : List WordTerm) :
    (actionPolynomial p*wordPolynomial f n).coeff k≤255*coefficientSum p := by
  induction p with
  | nil => simp [actionPolynomial,coefficientSum]
  | cons t p ih =>
    rw [actionPolynomial,add_mul,coeff_add,coefficientSum]
    have hm : (monomial t.1 t.2*wordPolynomial f n).coeff k≤255*t.2 := by
      by_cases h : t.1≤k
      · rw [show k=(k-t.1)+t.1 by omega,coeff_monomial_mul]
        calc
          t.2*(wordPolynomial f n).coeff (k-t.1)≤t.2*255 :=
            Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (wordPolynomial_bound f n _))
          _=255*t.2 := Nat.mul_comm _ _
      · rw [←C_mul_X_pow_eq_monomial,mul_assoc,coeff_C_mul,coeff_X_pow_mul',
          if_neg h,mul_zero]
        exact Nat.zero_le _
    calc
      _≤255*t.2+255*coefficientSum p := Nat.add_le_add hm ih
      _=255*(t.2+coefficientSum p) := by ring

theorem dotPolynomial_coefficient_bound (K k : ℕ) (W : WeightData) (i j : Fin 3)
    (p : List FastBlock) :
    (dotPolynomial K W i j p).coeff k≤255*totalCoefficients p := by
  induction p with
  | nil => simp [dotPolynomial,totalCoefficients]
  | cons b p ih =>
    rw [dotPolynomial,coeff_add,totalCoefficients]
    calc
      _≤255*coefficientSum b.2.2+255*totalCoefficients p :=
        Nat.add_le_add (action_mul_coefficient_bound _ _ _ _) ih
      _=255*(coefficientSum b.2.2+totalCoefficients p) := by ring

theorem action_mul_coefficient (K n s : ℕ) (p : List WordTerm)
    (hs : s≤K) (hp : ∀ t∈p,t.1+s≤K) :
    (actionPolynomial p*wordPolynomial (K+1) n).coeff (K-s)=rawWord n s p := by
  induction p with
  | nil => simp [actionPolynomial,rawWord]
  | cons t p ih =>
    have ht := hp t List.mem_cons_self
    have htail : ∀ t∈p,t.1+s≤K := fun t h => hp t (List.mem_cons_of_mem _ h)
    have hm : (monomial t.1 t.2*wordPolynomial (K+1) n).coeff (K-s)=
        t.2*slot n (s+t.1) := by
      rw [show K-s=(K-s-t.1)+t.1 by omega,coeff_monomial_mul]
      have hk : K-s-t.1<K+1 := by omega
      have he : K+1-1-(K-s-t.1)=s+t.1 := by omega
      rw [wordPolynomial_coeff,if_pos hk,he,←slot_eq]
    rw [actionPolynomial,add_mul,coeff_add,hm,ih htail]
    rfl

theorem dotPolynomial_coefficient (K s : ℕ) (W : WeightData) (i j : Fin 3)
    (p : List FastBlock) (hs : s≤K)
    (hp : ∀ b∈p,∀t∈b.2.2,t.1+s≤K) :
    (dotPolynomial K W i j p).coeff (K-s)=rawDot W i j s p := by
  induction p with
  | nil => simp [dotPolynomial,rawDot]
  | cons b p ih =>
    rw [dotPolynomial,coeff_add,action_mul_coefficient K _ s _ hs
      (hp b List.mem_cons_self),ih (fun b h => hp b (List.mem_cons_of_mem _ h))]
    rfl

theorem rawWord_zero (s : ℕ) (p : List WordTerm) : rawWord 0 s p=0 := by
  induction p with
  | nil => rfl
  | cons t p ih => simp [rawWord,slot,ih]

theorem dotWord_lt (n s tail : ℕ) (p : List WordTerm) (ht : tail<109) :
    dotWord n s tail p<109 := by
  induction p with
  | nil => exact ht
  | cons t p ih =>
    simp only [dotWord]
    split_ifs
    · exact ih
    · exact Nat.mod_lt _ (by decide)

theorem dotWord_eq_raw (n s tail : ℕ) (p : List WordTerm) (ht : tail<109) :
    dotWord n s tail p=(rawWord n s p+tail)%109 := by
  induction p with
  | nil => simp only [dotWord,rawWord,zero_add,Nat.mod_eq_of_lt ht]
  | cons t p ih =>
    simp only [dotWord,rawWord]
    split_ifs with h
    · rw [h,mul_zero,zero_add,ih]
    · simp only [ih,Nat.add_mod,Nat.mod_mod,Nat.add_assoc]

theorem groupedDot_lt (W : WeightData) (i j : Fin 3) (s : ℕ)
    (p : List FastBlock) : groupedDot W i j s p<109 := by
  induction p with
  | nil => change 0<109; decide
  | cons b p ih =>
    simp only [groupedDot]
    split_ifs
    · exact ih
    · exact dotWord_lt _ _ _ _ ih

theorem groupedDot_eq_raw (W : WeightData) (i j : Fin 3) (s : ℕ)
    (p : List FastBlock) : groupedDot W i j s p=rawDot W i j s p%109 := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [groupedDot]
    split_ifs with h
    · simp only [rawDot,h,rawWord_zero,zero_add,ih]
    · rw [dotWord_eq_raw _ _ _ _ (groupedDot_lt W i j s p),ih]
      simp only [rawDot,Nat.add_mod,Nat.mod_mod]

theorem packed_pair_coefficient (B K α s : ℕ) (hB : 0<B)
    (W : WeightData) (i j r t : Fin 3) (p q : List FastBlock)
    (hb : 255*(α*totalCoefficients p+totalCoefficients q)<B)
    (hs : s≤K)
    (hp : ∀b∈p,∀u∈b.2.2,u.1+s≤K)
    (hq : ∀b∈q,∀u∈b.2.2,u.1+s≤K) :
    (((α*packedDot B K W i j p+packedDot B K W r t q)/B^(K-s))%B)%109=
      (α*groupedDot W i j s p+groupedDot W r t s q)%109 := by
  let e : ℕ[X] := C α*dotPolynomial K W i j p+dotPolynomial K W r t q
  have hc (k : ℕ) : e.coeff k<B := by
    apply lt_of_le_of_lt _ hb
    dsimp [e]
    rw [coeff_add,coeff_C_mul]
    calc
      _≤α*(255*totalCoefficients p)+255*totalCoefficients q :=
        Nat.add_le_add (Nat.mul_le_mul_left _
          (dotPolynomial_coefficient_bound K k W i j p))
          (dotPolynomial_coefficient_bound K k W r t q)
      _=255*(α*totalCoefficients p+totalCoefficients q) := by ring
  have hd := CycleQ2NaturalPolynomialDigits.coefficient B hB e hc (K-s)
  have he : e.eval B=α*packedDot B K W i j p+packedDot B K W r t q := by
    simp only [e,eval_add,eval_mul,eval_C,packedDot_eq_eval]
  rw [he] at hd
  rw [←hd]
  change ((C α*dotPolynomial K W i j p+dotPolynomial K W r t q).coeff (K-s))%109=_
  rw [coeff_add,coeff_C_mul,dotPolynomial_coefficient K s W i j p hs hp,
    dotPolynomial_coefficient K s W r t q hs hq,
    groupedDot_eq_raw,groupedDot_eq_raw]
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod]

end CycleQ2SparseModularCorrelation

#print axioms CycleQ2SparseModularCorrelation.dotPolynomial_coefficient

#print axioms CycleQ2SparseModularCorrelation.packed_pair_coefficient
end
