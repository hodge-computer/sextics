import Proposal.Workspace
import Proposal.GeometricTarget11Part04
import Proposal.Assembly06Part03
import Proposal.Assembly07Part03

/-! Source partition of Assembly07.lean; declarations and proofs are preserved. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicRightInverse.lean -/
section
/-! # The literal seven by nine pairing has a displayed right inverse

The identification of this small matrix with the actual incidence pairing is
proved separately.  This arithmetic statement uses ordinary kernel reduction.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularDetectorCertificate
open scoped Matrix

def cubicPairingMatrix : Matrix (Fin 7) (Fin 9) (ZMod 109) :=
  fun k c => CycleQ2SegreModularDetectorData.cubicPairing k c

def rightInverse : Matrix (Fin 9) (Fin 7) (ZMod 109) :=
  fun c k => CycleQ2SegreModularDetectorData.pairingRightInverse c k

theorem literal_cubic_right_inverse : cubicPairingMatrix * rightInverse=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

def kernelCubic : Fin 9 → ZMod 109 := ![0,76,93,93,92,93,93,71,0]

theorem pairing_kernelCubic : cubicPairingMatrix *ᵥ kernelCubic=0 := by
  decide +kernel

theorem kernelCubic_trace :
    (33 : ZMod 109)*kernelCubic 1-(1+33)*kernelCubic 8=1 := by
  decide +kernel

end CycleQ2SegreModularDetectorCertificate

#print axioms CycleQ2SegreModularDetectorCertificate.literal_cubic_right_inverse
#print axioms CycleQ2SegreModularDetectorCertificate.pairing_kernelCubic
#print axioms CycleQ2SegreModularDetectorCertificate.kernelCubic_trace
end


