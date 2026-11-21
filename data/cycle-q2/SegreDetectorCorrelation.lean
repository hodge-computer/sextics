import Proposal.SegreCubicPairingVerification

/-!
# Correlation identities for the seven Segre detector functionals
-/

set_option Elab.async false

/- Component: continuation_3/SegreModularCorrelationExpressions.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationExpressions
open CycleQ2SparseModularFunctional CycleQ2SparseModularFastDot
  CycleQ2SparseModularCorrelation CycleQ2SegreModularFastActions
  CycleQ2SegreModularFastExpressions CycleQ2SegreModularDetectorExpressions

def base : ℕ := 1099511627776
def extent : ℕ := 840

def negativeSlot : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,0,0],![1,2,0],![2,0,1]]

def positiveSlot : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,0,0],![2,0,1],![1,2,0]]

def emptyTable (_ _ : Fin 3) : List FastBlock := []

def negativeTable : Fin 3 → Fin 3 → Fin 3 → Fin 3 → List FastBlock :=
  ![![emptyTable,emptyTable,emptyTable],![fast22,fast20,fast21],![fast11,fast12,fast10]]

def positiveTable : Fin 3 → Fin 3 → Fin 3 → Fin 3 → List FastBlock :=
  ![![emptyTable,emptyTable,emptyTable],![fast21,fast22,fast20],![fast12,fast10,fast11]]

def pairFast (W : WeightData) (i j a b : Fin 3) (u v : ℕ) : ℕ :=
  (108*groupedDot W 0 (negativeSlot i j) (u+29*v) (negativeTable i j a b)+
    groupedDot W 0 (positiveSlot i j) (u+29*v) (positiveTable i j a b))%109

theorem fastEntry_eq_pair (W : WeightData) (i j a b : Fin 3) (u v : ℕ) :
    fastEntry i j W a b u v=pairFast W i j a b u v := by
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)

def packedEntry (W : WeightData) (i j a b : Fin 3) : ℕ :=
  108*packedDot base extent W 0 (negativeSlot i j) (negativeTable i j a b)+
    packedDot base extent W 0 (positiveSlot i j) (positiveTable i j a b)

def digit (n s : ℕ) : ℕ :=
  ((n/CycleQ2BinaryNaturalPower.power base 12 (extent-s))%base)%109

def codeBound (a b : Fin 3) : ℕ := extent-29*(14-a.val-2*b.val)

def codeCheck (a b : Fin 3) (p : List FastBlock) : Bool :=
  p.all (fun c => c.2.2.all (fun t => decide (t.1≤codeBound a b)))

def boundCheck (i j a b : Fin 3) : Bool :=
  decide (255*(108*totalCoefficients (negativeTable i j a b)+
    totalCoefficients (positiveTable i j a b))<base) &&
    (codeCheck a b (negativeTable i j a b) && codeCheck a b (positiveTable i j a b))

def checkBlock (W : WeightData) (i j a b : Fin 3) : Bool :=
  boundCheck i j a b &&
    (List.range 15).all (fun u => (List.range 15).all (fun v =>
      if allowed14 a b u v then digit (packedEntry W i j a b) (u+29*v)==0 else true))

theorem code_le_of_check (a b : Fin 3) (p : List FastBlock)
    (h : codeCheck a b p=true) (c : FastBlock) (hc : c∈p)
    (t : WordTerm) (ht : t∈c.2.2) : t.1≤codeBound a b := by
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h c hc) t ht)

theorem digit_eq_entryDot (W : WeightData) (i j a b : Fin 3) (u v : ℕ)
    (ha : allowed14 a b u v=true) (hb : boundCheck i j a b=true) :
    digit (packedEntry W i j a b) (u+29*v)=entryDot i j W a b u v := by
  have hav : a.val+u+v+2*b.val≤14 ∧ (2*a.val+2*u+v)%3=0 := of_decide_eq_true ha
  have hshift : u+29*v≤29*(14-a.val-2*b.val) := by omega
  have hlimit : 29*(14-a.val-2*b.val)≤extent := by unfold extent; omega
  have hs : u+29*v≤extent := hshift.trans hlimit
  have hh := Bool.and_eq_true_iff.mp hb
  have hco : 255*(108*totalCoefficients (negativeTable i j a b)+
      totalCoefficients (positiveTable i j a b))<base := of_decide_eq_true hh.1
  have hc := Bool.and_eq_true_iff.mp hh.2
  have hp : ∀ c∈negativeTable i j a b,∀t∈c.2.2,t.1+(u+29*v)≤extent := by
    intro c hcm t htm
    have h := code_le_of_check a b _ hc.1 c hcm t htm
    unfold codeBound at h
    omega
  have hq : ∀ c∈positiveTable i j a b,∀t∈c.2.2,t.1+(u+29*v)≤extent := by
    intro c hcm t htm
    have h := code_le_of_check a b _ hc.2 c hcm t htm
    unfold codeBound at h
    omega
  rw [←fastEntry_eq,fastEntry_eq_pair]
  unfold digit packedEntry pairFast
  rw [CycleQ2BinaryNaturalPower.power_eq]
  exact packed_pair_coefficient base extent 108 (u+29*v) (by decide)
    W 0 (negativeSlot i j) 0 (positiveSlot i j)
    (negativeTable i j a b) (positiveTable i j a b) hco hs hp hq

theorem checkEntryBlock_of_correlation (W : WeightData) (i j a b : Fin 3)
    (h : checkBlock W i j a b=true) : checkEntryBlock W i j a b=true := by
  have hb := (Bool.and_eq_true_iff.mp h).1
  have hn := (Bool.and_eq_true_iff.mp h).2
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro v hv
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hn u hu) v hv
  by_cases ha : allowed14 a b u v=true
  · simpa only [ha,ite_true,digit_eq_entryDot W i j a b u v ha hb] using hc
  · simp [ha]

end CycleQ2SegreModularCorrelationExpressions

#print axioms CycleQ2SegreModularCorrelationExpressions.checkEntryBlock_of_correlation
end

/- Component: continuation_3/SegreModularDetectorDifferential.lean -/
section
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularDetectorExpressions
open MvPolynomial CycleQ2SparseModularFunctional CycleQ2IncidenceFirstOrder

def basisMatrix (i j : Fin 3) (p : P) : Matrix (Fin 3) (Fin 3) P :=
  fun r s => if r=i ∧ s=j then p else 0

theorem firstRow_basisDifferential (M : Matrix (Fin 3) (Fin 3) P) (p : P)
    (L : Fin 3 → P →ₗ[F] F) (i j : Fin 3) :
    (∑ c, L c (cofactorDifferential M (basisMatrix i j p) 0 c)) =
      signedEntry i j (fun s k l => L s (M k l*p)) := by
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix,cofactorDifferential_fin_three,Fin.sum_univ_three,
      signedEntry,signed00,signed01,signed02,signed10,signed11,signed12,
      signed20,signed21,signed22,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,mul_comm] <;> abel

end CycleQ2SegreModularDetectorExpressions
#print axioms CycleQ2SegreModularDetectorExpressions.firstRow_basisDifferential
end
end

section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationChecks

open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2SegreModularCorrelationExpressions CycleQ2SegreModularDetectorExpressions

private theorem checkEntry_of_blocks {W : WeightData} {i j : Fin 3}
    (h : ∀ a b : Fin 3, checkBlock W i j a b = true) : checkEntry W i j = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation W i j
    ⟨a, List.mem_range.mp ha⟩ ⟨b, List.mem_range.mp hb⟩ (h _ _)


/-! The six nontrivial entries for detector 0. -/

theorem numeric0_10 : ∀a b : Fin 3,checkBlock weights0 1 0 a b=true := by
  decide +kernel
theorem entry0_10 : checkEntry weights0 1 0=true :=
  checkEntry_of_blocks numeric0_10

theorem numeric0_11 : ∀a b : Fin 3,checkBlock weights0 1 1 a b=true := by
  decide +kernel
theorem entry0_11 : checkEntry weights0 1 1=true :=
  checkEntry_of_blocks numeric0_11

theorem numeric0_12 : ∀a b : Fin 3,checkBlock weights0 1 2 a b=true := by
  decide +kernel
theorem entry0_12 : checkEntry weights0 1 2=true :=
  checkEntry_of_blocks numeric0_12

theorem numeric0_20 : ∀a b : Fin 3,checkBlock weights0 2 0 a b=true := by
  decide +kernel
theorem entry0_20 : checkEntry weights0 2 0=true :=
  checkEntry_of_blocks numeric0_20

theorem numeric0_21 : ∀a b : Fin 3,checkBlock weights0 2 1 a b=true := by
  decide +kernel
theorem entry0_21 : checkEntry weights0 2 1=true :=
  checkEntry_of_blocks numeric0_21

theorem numeric0_22 : ∀a b : Fin 3,checkBlock weights0 2 2 a b=true := by
  decide +kernel
theorem entry0_22 : checkEntry weights0 2 2=true :=
  checkEntry_of_blocks numeric0_22

/-! The six nontrivial entries for detector 1. -/

theorem numeric1_10 : ∀a b : Fin 3,checkBlock weights1 1 0 a b=true := by
  decide +kernel
theorem entry1_10 : checkEntry weights1 1 0=true :=
  checkEntry_of_blocks numeric1_10

theorem numeric1_11 : ∀a b : Fin 3,checkBlock weights1 1 1 a b=true := by
  decide +kernel
theorem entry1_11 : checkEntry weights1 1 1=true :=
  checkEntry_of_blocks numeric1_11

theorem numeric1_12 : ∀a b : Fin 3,checkBlock weights1 1 2 a b=true := by
  decide +kernel
theorem entry1_12 : checkEntry weights1 1 2=true :=
  checkEntry_of_blocks numeric1_12

theorem numeric1_20 : ∀a b : Fin 3,checkBlock weights1 2 0 a b=true := by
  decide +kernel
theorem entry1_20 : checkEntry weights1 2 0=true :=
  checkEntry_of_blocks numeric1_20

theorem numeric1_21 : ∀a b : Fin 3,checkBlock weights1 2 1 a b=true := by
  decide +kernel
theorem entry1_21 : checkEntry weights1 2 1=true :=
  checkEntry_of_blocks numeric1_21

theorem numeric1_22 : ∀a b : Fin 3,checkBlock weights1 2 2 a b=true := by
  decide +kernel
theorem entry1_22 : checkEntry weights1 2 2=true :=
  checkEntry_of_blocks numeric1_22

/-! The six nontrivial entries for detector 2. -/

theorem numeric2_10 : ∀a b : Fin 3,checkBlock weights2 1 0 a b=true := by
  decide +kernel
theorem entry2_10 : checkEntry weights2 1 0=true :=
  checkEntry_of_blocks numeric2_10

theorem numeric2_11 : ∀a b : Fin 3,checkBlock weights2 1 1 a b=true := by
  decide +kernel
theorem entry2_11 : checkEntry weights2 1 1=true :=
  checkEntry_of_blocks numeric2_11

theorem numeric2_12 : ∀a b : Fin 3,checkBlock weights2 1 2 a b=true := by
  decide +kernel
theorem entry2_12 : checkEntry weights2 1 2=true :=
  checkEntry_of_blocks numeric2_12

theorem numeric2_20 : ∀a b : Fin 3,checkBlock weights2 2 0 a b=true := by
  decide +kernel
theorem entry2_20 : checkEntry weights2 2 0=true :=
  checkEntry_of_blocks numeric2_20

theorem numeric2_21 : ∀a b : Fin 3,checkBlock weights2 2 1 a b=true := by
  decide +kernel
theorem entry2_21 : checkEntry weights2 2 1=true :=
  checkEntry_of_blocks numeric2_21

theorem numeric2_22 : ∀a b : Fin 3,checkBlock weights2 2 2 a b=true := by
  decide +kernel
theorem entry2_22 : checkEntry weights2 2 2=true :=
  checkEntry_of_blocks numeric2_22

/-! The six nontrivial entries for detector 3. -/

theorem numeric3_10 : ∀a b : Fin 3,checkBlock weights3 1 0 a b=true := by
  decide +kernel
theorem entry3_10 : checkEntry weights3 1 0=true :=
  checkEntry_of_blocks numeric3_10

theorem numeric3_11 : ∀a b : Fin 3,checkBlock weights3 1 1 a b=true := by
  decide +kernel
theorem entry3_11 : checkEntry weights3 1 1=true :=
  checkEntry_of_blocks numeric3_11

theorem numeric3_12 : ∀a b : Fin 3,checkBlock weights3 1 2 a b=true := by
  decide +kernel
theorem entry3_12 : checkEntry weights3 1 2=true :=
  checkEntry_of_blocks numeric3_12

theorem numeric3_20 : ∀a b : Fin 3,checkBlock weights3 2 0 a b=true := by
  decide +kernel
theorem entry3_20 : checkEntry weights3 2 0=true :=
  checkEntry_of_blocks numeric3_20

theorem numeric3_21 : ∀a b : Fin 3,checkBlock weights3 2 1 a b=true := by
  decide +kernel
theorem entry3_21 : checkEntry weights3 2 1=true :=
  checkEntry_of_blocks numeric3_21

theorem numeric3_22 : ∀a b : Fin 3,checkBlock weights3 2 2 a b=true := by
  decide +kernel
theorem entry3_22 : checkEntry weights3 2 2=true :=
  checkEntry_of_blocks numeric3_22

/-! The six nontrivial entries for detector 4. -/

theorem numeric4_10 : ∀a b : Fin 3,checkBlock weights4 1 0 a b=true := by
  decide +kernel
theorem entry4_10 : checkEntry weights4 1 0=true :=
  checkEntry_of_blocks numeric4_10

theorem numeric4_11 : ∀a b : Fin 3,checkBlock weights4 1 1 a b=true := by
  decide +kernel
theorem entry4_11 : checkEntry weights4 1 1=true :=
  checkEntry_of_blocks numeric4_11

theorem numeric4_12 : ∀a b : Fin 3,checkBlock weights4 1 2 a b=true := by
  decide +kernel
theorem entry4_12 : checkEntry weights4 1 2=true :=
  checkEntry_of_blocks numeric4_12

theorem numeric4_20 : ∀a b : Fin 3,checkBlock weights4 2 0 a b=true := by
  decide +kernel
theorem entry4_20 : checkEntry weights4 2 0=true :=
  checkEntry_of_blocks numeric4_20

theorem numeric4_21 : ∀a b : Fin 3,checkBlock weights4 2 1 a b=true := by
  decide +kernel
theorem entry4_21 : checkEntry weights4 2 1=true :=
  checkEntry_of_blocks numeric4_21

theorem numeric4_22 : ∀a b : Fin 3,checkBlock weights4 2 2 a b=true := by
  decide +kernel
theorem entry4_22 : checkEntry weights4 2 2=true :=
  checkEntry_of_blocks numeric4_22

/-! The six nontrivial entries for detector 5. -/

theorem numeric5_10 : ∀a b : Fin 3,checkBlock weights5 1 0 a b=true := by
  decide +kernel
theorem entry5_10 : checkEntry weights5 1 0=true :=
  checkEntry_of_blocks numeric5_10

theorem numeric5_11 : ∀a b : Fin 3,checkBlock weights5 1 1 a b=true := by
  decide +kernel
theorem entry5_11 : checkEntry weights5 1 1=true :=
  checkEntry_of_blocks numeric5_11

theorem numeric5_12 : ∀a b : Fin 3,checkBlock weights5 1 2 a b=true := by
  decide +kernel
theorem entry5_12 : checkEntry weights5 1 2=true :=
  checkEntry_of_blocks numeric5_12

theorem numeric5_20 : ∀a b : Fin 3,checkBlock weights5 2 0 a b=true := by
  decide +kernel
theorem entry5_20 : checkEntry weights5 2 0=true :=
  checkEntry_of_blocks numeric5_20

theorem numeric5_21 : ∀a b : Fin 3,checkBlock weights5 2 1 a b=true := by
  decide +kernel
theorem entry5_21 : checkEntry weights5 2 1=true :=
  checkEntry_of_blocks numeric5_21

theorem numeric5_22 : ∀a b : Fin 3,checkBlock weights5 2 2 a b=true := by
  decide +kernel
theorem entry5_22 : checkEntry weights5 2 2=true :=
  checkEntry_of_blocks numeric5_22

/-! The six nontrivial entries for detector 6. -/

theorem numeric6_10 : ∀a b : Fin 3,checkBlock weights6 1 0 a b=true := by
  decide +kernel
theorem entry6_10 : checkEntry weights6 1 0=true :=
  checkEntry_of_blocks numeric6_10

theorem numeric6_11 : ∀a b : Fin 3,checkBlock weights6 1 1 a b=true := by
  decide +kernel
theorem entry6_11 : checkEntry weights6 1 1=true :=
  checkEntry_of_blocks numeric6_11

theorem numeric6_12 : ∀a b : Fin 3,checkBlock weights6 1 2 a b=true := by
  decide +kernel
theorem entry6_12 : checkEntry weights6 1 2=true :=
  checkEntry_of_blocks numeric6_12

theorem numeric6_20 : ∀a b : Fin 3,checkBlock weights6 2 0 a b=true := by
  decide +kernel
theorem entry6_20 : checkEntry weights6 2 0=true :=
  checkEntry_of_blocks numeric6_20

theorem numeric6_21 : ∀a b : Fin 3,checkBlock weights6 2 1 a b=true := by
  decide +kernel
theorem entry6_21 : checkEntry weights6 2 1=true :=
  checkEntry_of_blocks numeric6_21

theorem numeric6_22 : ∀a b : Fin 3,checkBlock weights6 2 2 a b=true := by
  decide +kernel
theorem entry6_22 : checkEntry weights6 2 2=true :=
  checkEntry_of_blocks numeric6_22

end CycleQ2SegreModularCorrelationChecks


#print axioms CycleQ2SegreModularCorrelationChecks.entry0_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_22
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_10
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_11
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_12
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_20
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_21
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_22
end

/- Component: continuation_3/SegreModularDetectorEntryBinding.lean -/
section
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorEntryBinding
open MvPolynomial CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial
  CycleQ2SegreModularDetectorExpressions CycleQ2SegreModularDetectorData
  CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceUniversalChart CycleQ2GenericEntryCoefficientBinding

 theorem dotAction_eq_nf (W : WeightData) (r s i j a b : Fin 3) (u v : ℕ) :
    (dotAction W r s i j a b u v : F)=functional W r s
      (nf (57:F) 33 (rawSeedMatrix (57:F) i j*MvPolynomial.monomial
        (tupleExponent (a.val,u,v,14-(a.val+u+v+2*b.val),b.val)) 1)) := by
  unfold dotAction
  rw [flatActionTable_eq]
  exact CycleQ2SegreModularActionSemantics.dot_flat_action_eq_nf W r s i j a b u v

 theorem standardIndex_exponent (e : StandardIndex 14) :
    tupleExponent (e.val.1.1.val,e.val.2.1.val,e.val.2.2.val,
      14-(e.val.1.1.val+e.val.2.1.val+e.val.2.2.val+2*e.val.1.2.val),e.val.1.2.val)=
      standardExponent e := by
  ext l
  fin_cases l <;> rfl

 theorem basisMatrix_eq (i j : Fin 3) (e : StandardIndex 14) :
    CycleQ2SegreModularDetectorMatrixBinding.basisMatrix ((i,j),e)=
      CycleQ2SegreModularDetectorExpressions.basisMatrix i j
        (MvPolynomial.monomial (standardExponent e) (1:F)) := by
  funext r s
  rw [CycleQ2SegreModularDetectorMatrixBinding.basisMatrix_apply]
  simp only [CycleQ2SegreModularDetectorExpressions.basisMatrix,Prod.mk.injEq]

 theorem entry_column_eq_dot (k : Fin 7) (c : MatrixParameter) :
    (CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33) k c=
      (entryDot c.1.1 c.1.2 (weights k) c.2.val.1.1.val c.2.val.1.2.val
        c.2.val.2.1.val c.2.val.2.2.val : F) := by
  rcases c with ⟨⟨i,j⟩,e⟩
  rw [CycleQ2SegreModularDetectorMatrixBinding.detector_entry_column,basisMatrix_eq]
  have hd := firstRow_basisDifferential (rawSeedMatrix (57:F))
    (MvPolynomial.monomial (standardExponent e) (1:F))
    (fun s => (functional (weights k) 0 s).comp (nf (57:F) 33)) i j
  simp only [LinearMap.comp_apply] at hd
  rw [hd]
  symm
  rw [cast_entryDot]
  apply congrArg (signedEntry i j)
  funext s r t
  rw [dotAction_eq_nf,standardIndex_exponent]

 theorem annihilates_entry_of_checks
    (hc : ∀k : Fin 7,∀i j : Fin 3,checkEntry (weights k) i j=true) :
    CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33=0 := by
  ext k c
  rw [entry_column_eq_dot]
  have h := entryDot_zero_of_check (weights k) c.1.1 c.1.2 (hc k c.1.1 c.1.2)
    c.2.val.1.1.val c.2.val.1.2.val c.2.val.2.1.val c.2.val.2.2.val
    c.2.val.1.1.isLt c.2.val.1.2.isLt c.2.val.2.1.isLt c.2.val.2.2.isLt c.2.property
  rw [h,Nat.cast_zero]
  rfl

end CycleQ2SegreModularDetectorEntryBinding
#print axioms CycleQ2SegreModularDetectorEntryBinding.entry_column_eq_dot
#print axioms CycleQ2SegreModularDetectorEntryBinding.annihilates_entry_of_checks
end
end

/- Component: continuation_3/SegreModularCorrelationChecks.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2SegreModularDetectorExpressions

theorem checkEntry_first_row (W : WeightData) (j : Fin 3) :
    checkEntry W 0 j=true := by
  have hz (a b u v : ℕ) : entryDot 0 j W a b u v=0 := by
    fin_cases j <;> rfl
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro v hv
  simp [hz]

theorem all_entry_checks (k : Fin 7) (i j : Fin 3) :
    checkEntry (weights k) i j=true := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry0_10
  · exact entry0_11
  · exact entry0_12
  · exact entry0_20
  · exact entry0_21
  · exact entry0_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry1_10
  · exact entry1_11
  · exact entry1_12
  · exact entry1_20
  · exact entry1_21
  · exact entry1_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry2_10
  · exact entry2_11
  · exact entry2_12
  · exact entry2_20
  · exact entry2_21
  · exact entry2_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry3_10
  · exact entry3_11
  · exact entry3_12
  · exact entry3_20
  · exact entry3_21
  · exact entry3_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry4_10
  · exact entry4_11
  · exact entry4_12
  · exact entry4_20
  · exact entry4_21
  · exact entry4_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry5_10
  · exact entry5_11
  · exact entry5_12
  · exact entry5_20
  · exact entry5_21
  · exact entry5_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry6_10
  · exact entry6_11
  · exact entry6_12
  · exact entry6_20
  · exact entry6_21
  · exact entry6_22

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.all_entry_checks
end

/- Component: continuation_3/SegreModularDetectorCertificate.lean -/
section
/-! # Seven checked annihilators of the actual entry Jacobian

The coefficient functionals below annihilate every actual entry column. Their
values on the nine displayed invariant cubic columns have a checked right
inverse. All finite arithmetic is replayable by Lean's ordinary kernel.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorCertificate
open scoped Matrix

open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2IncidenceEquations CycleQ2GenericEntryCoefficientBinding
  CycleQ2SegreModularDetectorExpressions CycleQ2SegreModularDetectorEntryBinding
  CycleQ2SegreModularCorrelationChecks
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2SegreModularCubicPairing
  CycleQ2SegreModularCubicData CycleQ2SegreModularCubicSemantics

def L : Matrix (Fin 7) EquationIndex F := detectorMatrix

theorem annihilates_entry : L * entryJacobianBlock (57:F) 33=0 :=
  annihilates_entry_of_checks all_entry_checks

theorem cast_cubicDot (W : WeightData) (c : Fin 9) :
    (cubicDot W c : F)=
      ∑s : Fin 3,(dot W 0 s (0,0,0,0,0)
        (flattenTowersData (cubicTable s c)) : F) := by
  simp only [cubicDot,ZMod.natCast_mod,Nat.cast_add,Fin.sum_univ_three]

theorem cubic_pairing_eq : L * selectedCubicBlock=cubicPairingMatrix := by
  ext k c
  change (detectorMatrix*selectedCubicBlock) k c=(cubicPairing k c : F)
  rw [detector_cubic_numeric,←cast_cubicDot,all_pairing_checks]

theorem cubic_right_inverse : (L * selectedCubicBlock) * rightInverse=1 := by
  rw [cubic_pairing_eq]
  exact literal_cubic_right_inverse

theorem detected_kernelCubic : (L * selectedCubicBlock) *ᵥ kernelCubic=0 := by
  rw [cubic_pairing_eq]
  exact pairing_kernelCubic

end CycleQ2SegreModularDetectorCertificate

#print axioms CycleQ2SegreModularDetectorCertificate.annihilates_entry
#print axioms CycleQ2SegreModularDetectorCertificate.cubic_right_inverse
#print axioms CycleQ2SegreModularDetectorCertificate.detected_kernelCubic
end
end
