import Proposal.Workspace
import Proposal.GeometricTarget11Part04
import Proposal.Assembly07Part04
import Proposal.Assembly08Part01

/-! Source partition of Assembly08.lean; declarations and proofs are preserved. -/

set_option Elab.async false

/- Component: continuation_3/SegreGaussianActionChecks02.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError02 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m02 (monomialTower oneLayers a b)))
    (negTowers (action02 a b))
private theorem checked_02_0_0 : checkTowers (actionError02 0 0) = true := by
  decide +kernel

private theorem checked_02_0_1 : checkTowers (actionError02 0 1) = true := by
  decide +kernel

private theorem checked_02_0_2 : checkTowers (actionError02 0 2) = true := by
  decide +kernel

private theorem checked_02_1_0 : checkTowers (actionError02 1 0) = true := by
  decide +kernel

private theorem checked_02_1_1 : checkTowers (actionError02 1 1) = true := by
  decide +kernel

private theorem checked_02_1_2 : checkTowers (actionError02 1 2) = true := by
  decide +kernel

private theorem checked_02_2_0 : checkTowers (actionError02 2 0) = true := by
  decide +kernel

private theorem checked_02_2_1 : checkTowers (actionError02 2 1) = true := by
  decide +kernel

private theorem checked_02_2_2 : checkTowers (actionError02 2 2) = true := by
  decide +kernel

theorem action_check02 (a b : Fin 3) : checkTowers (actionError02 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_02_0_0
  · exact checked_02_0_1
  · exact checked_02_0_2
  · exact checked_02_1_0
  · exact checked_02_1_1
  · exact checked_02_1_2
  · exact checked_02_2_0
  · exact checked_02_2_1
  · exact checked_02_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check02
end


/- Component: continuation_3/SegreGaussianActionChecks10.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError10 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m10 (monomialTower oneLayers a b)))
    (negTowers (action10 a b))
private theorem checked_10_0_0 : checkTowers (actionError10 0 0) = true := by
  decide +kernel

private theorem checked_10_0_1 : checkTowers (actionError10 0 1) = true := by
  decide +kernel

private theorem checked_10_0_2 : checkTowers (actionError10 0 2) = true := by
  decide +kernel

private theorem checked_10_1_0 : checkTowers (actionError10 1 0) = true := by
  decide +kernel

private theorem checked_10_1_1 : checkTowers (actionError10 1 1) = true := by
  decide +kernel

private theorem checked_10_1_2 : checkTowers (actionError10 1 2) = true := by
  decide +kernel

private theorem checked_10_2_0 : checkTowers (actionError10 2 0) = true := by
  decide +kernel

private theorem checked_10_2_1 : checkTowers (actionError10 2 1) = true := by
  decide +kernel

private theorem checked_10_2_2 : checkTowers (actionError10 2 2) = true := by
  decide +kernel

theorem action_check10 (a b : Fin 3) : checkTowers (actionError10 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_10_0_0
  · exact checked_10_0_1
  · exact checked_10_0_2
  · exact checked_10_1_0
  · exact checked_10_1_1
  · exact checked_10_1_2
  · exact checked_10_2_0
  · exact checked_10_2_1
  · exact checked_10_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check10
end


/- Component: continuation_3/SegreGaussianActionChecks11.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError11 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m11 (monomialTower oneLayers a b)))
    (negTowers (action11 a b))
private theorem checked_11_0_0 : checkTowers (actionError11 0 0) = true := by
  decide +kernel

private theorem checked_11_0_1 : checkTowers (actionError11 0 1) = true := by
  decide +kernel

private theorem checked_11_0_2 : checkTowers (actionError11 0 2) = true := by
  decide +kernel

private theorem checked_11_1_0 : checkTowers (actionError11 1 0) = true := by
  decide +kernel

private theorem checked_11_1_1 : checkTowers (actionError11 1 1) = true := by
  decide +kernel

private theorem checked_11_1_2 : checkTowers (actionError11 1 2) = true := by
  decide +kernel

private theorem checked_11_2_0 : checkTowers (actionError11 2 0) = true := by
  decide +kernel

private theorem checked_11_2_1 : checkTowers (actionError11 2 1) = true := by
  decide +kernel

private theorem checked_11_2_2 : checkTowers (actionError11 2 2) = true := by
  decide +kernel

theorem action_check11 (a b : Fin 3) : checkTowers (actionError11 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_11_0_0
  · exact checked_11_0_1
  · exact checked_11_0_2
  · exact checked_11_1_0
  · exact checked_11_1_1
  · exact checked_11_1_2
  · exact checked_11_2_0
  · exact checked_11_2_1
  · exact checked_11_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check11
end


/- Component: continuation_3/SegreGaussianActionChecks12.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError12 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m12 (monomialTower oneLayers a b)))
    (negTowers (action12 a b))
private theorem checked_12_0_0 : checkTowers (actionError12 0 0) = true := by
  decide +kernel

private theorem checked_12_0_1 : checkTowers (actionError12 0 1) = true := by
  decide +kernel

private theorem checked_12_0_2 : checkTowers (actionError12 0 2) = true := by
  decide +kernel

private theorem checked_12_1_0 : checkTowers (actionError12 1 0) = true := by
  decide +kernel

private theorem checked_12_1_1 : checkTowers (actionError12 1 1) = true := by
  decide +kernel

private theorem checked_12_1_2 : checkTowers (actionError12 1 2) = true := by
  decide +kernel

private theorem checked_12_2_0 : checkTowers (actionError12 2 0) = true := by
  decide +kernel

private theorem checked_12_2_1 : checkTowers (actionError12 2 1) = true := by
  decide +kernel

private theorem checked_12_2_2 : checkTowers (actionError12 2 2) = true := by
  decide +kernel

theorem action_check12 (a b : Fin 3) : checkTowers (actionError12 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_12_0_0
  · exact checked_12_0_1
  · exact checked_12_0_2
  · exact checked_12_1_0
  · exact checked_12_1_1
  · exact checked_12_1_2
  · exact checked_12_2_0
  · exact checked_12_2_1
  · exact checked_12_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check12
end


/- Component: continuation_3/SegreGaussianActionChecks20.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError20 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m20 (monomialTower oneLayers a b)))
    (negTowers (action20 a b))
private theorem checked_20_0_0 : checkTowers (actionError20 0 0) = true := by
  decide +kernel

private theorem checked_20_0_1 : checkTowers (actionError20 0 1) = true := by
  decide +kernel

private theorem checked_20_0_2 : checkTowers (actionError20 0 2) = true := by
  decide +kernel

private theorem checked_20_1_0 : checkTowers (actionError20 1 0) = true := by
  decide +kernel

private theorem checked_20_1_1 : checkTowers (actionError20 1 1) = true := by
  decide +kernel

private theorem checked_20_1_2 : checkTowers (actionError20 1 2) = true := by
  decide +kernel

private theorem checked_20_2_0 : checkTowers (actionError20 2 0) = true := by
  decide +kernel

private theorem checked_20_2_1 : checkTowers (actionError20 2 1) = true := by
  decide +kernel

private theorem checked_20_2_2 : checkTowers (actionError20 2 2) = true := by
  decide +kernel

theorem action_check20 (a b : Fin 3) : checkTowers (actionError20 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_20_0_0
  · exact checked_20_0_1
  · exact checked_20_0_2
  · exact checked_20_1_0
  · exact checked_20_1_1
  · exact checked_20_1_2
  · exact checked_20_2_0
  · exact checked_20_2_1
  · exact checked_20_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check20
end


/- Component: continuation_3/SegreGaussianActionChecks21.lean -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
def actionError21 (a b : ℕ) : Towers :=
  addTowers (normalizeTower a0 a1 b0 32 (mulTowers m21 (monomialTower oneLayers a b)))
    (negTowers (action21 a b))
private theorem checked_21_0_0 : checkTowers (actionError21 0 0) = true := by
  decide +kernel

private theorem checked_21_0_1 : checkTowers (actionError21 0 1) = true := by
  decide +kernel

private theorem checked_21_0_2 : checkTowers (actionError21 0 2) = true := by
  decide +kernel

private theorem checked_21_1_0 : checkTowers (actionError21 1 0) = true := by
  decide +kernel

private theorem checked_21_1_1 : checkTowers (actionError21 1 1) = true := by
  decide +kernel

private theorem checked_21_1_2 : checkTowers (actionError21 1 2) = true := by
  decide +kernel

private theorem checked_21_2_0 : checkTowers (actionError21 2 0) = true := by
  decide +kernel

private theorem checked_21_2_1 : checkTowers (actionError21 2 1) = true := by
  decide +kernel

private theorem checked_21_2_2 : checkTowers (actionError21 2 2) = true := by
  decide +kernel

theorem action_check21 (a b : Fin 3) : checkTowers (actionError21 a b) = true := by
  fin_cases a <;> fin_cases b
  · exact checked_21_0_0
  · exact checked_21_0_1
  · exact checked_21_0_2
  · exact checked_21_1_0
  · exact checked_21_1_1
  · exact checked_21_1_2
  · exact checked_21_2_0
  · exact checked_21_2_1
  · exact checked_21_2_2
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.action_check21
end


/- Component: continuation_3/SegreGaussianActionStandard.lean -/
section
/-! The saved81 action representatives have the actual standard monomial
support. Coefficient values are irrelevant to this finite support check. -/

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreGaussianActionData

open CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional

theorem action00_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action00 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action01_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action01 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action02_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action02 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action10_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action10 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action11_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action11 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action12_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action12 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action20_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action20 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action21_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action21 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem action22_standard (a b : Fin 3) :
    standardPolynomial (flattenTowersData (action22 a b))=true := by
  fin_cases a <;> fin_cases b <;> decide +kernel

end CycleQ2SegreGaussianActionData

#print axioms CycleQ2SegreGaussianActionData.action00_standard
#print axioms CycleQ2SegreGaussianActionData.action22_standard
end


