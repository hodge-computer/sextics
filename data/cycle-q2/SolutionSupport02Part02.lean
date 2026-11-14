import Proposal.GeometricSurfaceBindings
import Proposal.SolutionSupport02Part01

/-! Components extracted from SolutionSupport02.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

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

def rawMatrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : Coeff :=
  X (Sum.inr (Sum.inr ((i,j),e)))

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


