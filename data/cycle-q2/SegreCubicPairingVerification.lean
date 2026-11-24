import Proposal.SegreActionNormalForms
import Proposal.SegreCubicFirstRowVerification
import Proposal.SegreCubicSecondRowVerification
import Proposal.SegreCubicThirdRowVerification

/-!
# The cubic pairing in the modular quotient
-/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicData.lean -/
section
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial

def kqTable : Fin 3 → Towers := ![kq0, kq1, kq2]

def cubicTable : Fin 3 → Fin 9 → Towers :=
  ![![cubic0_0, cubic0_1, cubic0_2, cubic0_3, cubic0_4, cubic0_5, cubic0_6, cubic0_7, cubic0_8], ![cubic1_0, cubic1_1, cubic1_2, cubic1_3, cubic1_4, cubic1_5, cubic1_6, cubic1_7, cubic1_8], ![cubic2_0, cubic2_1, cubic2_2, cubic2_3, cubic2_4, cubic2_5, cubic2_6, cubic2_7, cubic2_8]]
end CycleQ2SegreModularCubicData
end

/- Component: continuation_3/SegreModularCubicStandard0.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good0_0 : goodTowers 28 cubic0_0=true := by decide +kernel

theorem good0_1 : goodTowers 28 cubic0_1=true := by decide +kernel

theorem good0_2 : goodTowers 28 cubic0_2=true := by decide +kernel

theorem good0_3 : goodTowers 28 cubic0_3=true := by decide +kernel

theorem good0_4 : goodTowers 28 cubic0_4=true := by decide +kernel

theorem good0_5 : goodTowers 28 cubic0_5=true := by decide +kernel

theorem good0_6 : goodTowers 28 cubic0_6=true := by decide +kernel

theorem good0_7 : goodTowers 28 cubic0_7=true := by decide +kernel

theorem good0_8 : goodTowers 28 cubic0_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good0_8
end

/- Component: continuation_3/SegreModularCubicStandard1.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good1_0 : goodTowers 28 cubic1_0=true := by decide +kernel

theorem good1_1 : goodTowers 28 cubic1_1=true := by decide +kernel

theorem good1_2 : goodTowers 28 cubic1_2=true := by decide +kernel

theorem good1_3 : goodTowers 28 cubic1_3=true := by decide +kernel

theorem good1_4 : goodTowers 28 cubic1_4=true := by decide +kernel

theorem good1_5 : goodTowers 28 cubic1_5=true := by decide +kernel

theorem good1_6 : goodTowers 28 cubic1_6=true := by decide +kernel

theorem good1_7 : goodTowers 28 cubic1_7=true := by decide +kernel

theorem good1_8 : goodTowers 28 cubic1_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good1_8
end

/- Component: continuation_3/SegreModularCubicStandard2.lean -/
section
/-! Ordinary-kernel support and degree checks for one actual cubic-table row. -/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CycleQ2SegreModularCubicStandard

open CycleQ2SparseGaussianPolynomial CycleQ2SegreModularCubicData

theorem good2_0 : goodTowers 28 cubic2_0=true := by decide +kernel

theorem good2_1 : goodTowers 28 cubic2_1=true := by decide +kernel

theorem good2_2 : goodTowers 28 cubic2_2=true := by decide +kernel

theorem good2_3 : goodTowers 28 cubic2_3=true := by decide +kernel

theorem good2_4 : goodTowers 28 cubic2_4=true := by decide +kernel

theorem good2_5 : goodTowers 28 cubic2_5=true := by decide +kernel

theorem good2_6 : goodTowers 28 cubic2_6=true := by decide +kernel

theorem good2_7 : goodTowers 28 cubic2_7=true := by decide +kernel

theorem good2_8 : goodTowers 28 cubic2_8=true := by decide +kernel

end CycleQ2SegreModularCubicStandard

#print axioms CycleQ2SegreModularCubicStandard.good2_8
end

/- Component: continuation_3/SegreModularCubicChecks.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

theorem eval_cubicTable {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) (s : Fin 3) (q : Fin 9) :
    evalTowers φ x w z v (cubicTable s q)=evalTowers φ x w z v (monomialCubic q) *
      evalTowers φ x w z v k * evalTowers φ x w z v (literalQ s) := by
  fin_cases s <;> fin_cases q
  · exact eval_cubic0_0 φ x w z v hz hw
  · exact eval_cubic0_1 φ x w z v hz hw
  · exact eval_cubic0_2 φ x w z v hz hw
  · exact eval_cubic0_3 φ x w z v hz hw
  · exact eval_cubic0_4 φ x w z v hz hw
  · exact eval_cubic0_5 φ x w z v hz hw
  · exact eval_cubic0_6 φ x w z v hz hw
  · exact eval_cubic0_7 φ x w z v hz hw
  · exact eval_cubic0_8 φ x w z v hz hw
  · exact eval_cubic1_0 φ x w z v hz hw
  · exact eval_cubic1_1 φ x w z v hz hw
  · exact eval_cubic1_2 φ x w z v hz hw
  · exact eval_cubic1_3 φ x w z v hz hw
  · exact eval_cubic1_4 φ x w z v hz hw
  · exact eval_cubic1_5 φ x w z v hz hw
  · exact eval_cubic1_6 φ x w z v hz hw
  · exact eval_cubic1_7 φ x w z v hz hw
  · exact eval_cubic1_8 φ x w z v hz hw
  · exact eval_cubic2_0 φ x w z v hz hw
  · exact eval_cubic2_1 φ x w z v hz hw
  · exact eval_cubic2_2 φ x w z v hz hw
  · exact eval_cubic2_3 φ x w z v hz hw
  · exact eval_cubic2_4 φ x w z v hz hw
  · exact eval_cubic2_5 φ x w z v hz hw
  · exact eval_cubic2_6 φ x w z v hz hw
  · exact eval_cubic2_7 φ x w z v hz hw
  · exact eval_cubic2_8 φ x w z v hz hw
end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubicTable
end

/- Component: continuation_3/SegreModularCubicMonomialBinding.lean -/
section
/-! The nine supplied cubic towers are the actual indexed monomials. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularCubicMonomialBinding

open MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional
  CycleQ2SegreModularCubicData CycleQ2SegreModularDetectorData
  CycleQ2SegreModularGaussianBinding CycleQ2IncidenceGaussianArithmetic

theorem monomialCubic_flatten (q : Fin 9) :
    flattenTowersData (monomialCubic q)=[(cubicExponents q,1)] := by
  fin_cases q <;> rfl

theorem flatten_value (p : Towers) :
    eval coeffHom (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      (flattenTowersData p)=value p := by
  rw [flattenTowersData_eq,eval_flattenTowers]
  rfl

theorem value_monomialCubic (q : Fin 9) :
    value (monomialCubic q)=
      MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109) := by
  rw [←flatten_value,monomialCubic_flatten]
  change eval (MvPolynomial.C.comp reduction)
    (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      [(cubicExponents q,1)]=_
  simp only [eval_cons,eval_nil,termValue_variables,map_one,add_zero]

end CycleQ2SegreModularCubicMonomialBinding

#print axioms CycleQ2SegreModularCubicMonomialBinding.value_monomialCubic
end
end

/- Component: continuation_3/SegreModularCubicPairingExpressions.lean -/
section
namespace CycleQ2SegreModularCubicPairing
open CycleQ2SparseModularFunctional CycleQ2SegreModularCubicData

def cubicDot (W : WeightData) (c : Fin 9) : ℕ :=
  (dot W 0 0 (0,0,0,0,0) (flattenTowersData (cubicTable 0 c)) +
   dot W 0 1 (0,0,0,0,0) (flattenTowersData (cubicTable 1 c)) +
   dot W 0 2 (0,0,0,0,0) (flattenTowersData (cubicTable 2 c))) % 109

end CycleQ2SegreModularCubicPairing
end

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

/- Component: continuation_3/SegreModularCubicPairingChecks.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem all_pairing_checks (k : Fin 7) (c : Fin 9) :
    cubicDot (weights k) c=cubicPairing k c := by
  fin_cases k
  · exact pairing0 c
  · exact pairing1 c
  · exact pairing2 c
  · exact pairing3 c
  · exact pairing4 c
  · exact pairing5 c
  · exact pairing6 c

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.all_pairing_checks
end
