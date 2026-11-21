import Proposal.SegreGaussianActionThirdRow
import Proposal.SegreThreeBlockDetectors

/-!
# The Segre cubic pairing

The cubic monomials, right inverse and trace normalization for the pairing.
-/

set_option Elab.async false

/- Component: continuation_3/SegreModularCubicMonomials.lean -/
section
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial

def monomialCubic0 : Towers :=
[
  [],
  [[[((0,0,0,1,0),⟨1,0⟩)]]]
]

def monomialCubic1 : Towers :=
[
  [[[((0,0,0,3,0),⟨1,0⟩)]]]
]

def monomialCubic2 : Towers :=
[
  [[[((0,0,3,0,0),⟨1,0⟩)]]]
]

def monomialCubic3 : Towers :=
[
  [[[],
    [((0,0,1,1,0),⟨1,0⟩)]]]
]

def monomialCubic4 : Towers :=
[
  [[[],
    [],
    [],
    [((0,0,0,0,0),⟨1,0⟩)]]]
]

def monomialCubic5 : Towers :=
[
  [[],
   [[((0,0,1,1,0),⟨1,0⟩)]]]
]

def monomialCubic6 : Towers :=
[
  [[],
   [[],
    [],
    [((0,0,0,0,0),⟨1,0⟩)]]]
]

def monomialCubic7 : Towers :=
[
  [[],
   [],
   [[],
    [((0,0,0,0,0),⟨1,0⟩)]]]
]

def monomialCubic8 : Towers :=
[
  [[],
   [],
   [],
   [[((0,0,0,0,0),⟨1,0⟩)]]]
]

def monomialCubic : Fin 9 → Towers := ![monomialCubic0, monomialCubic1, monomialCubic2, monomialCubic3, monomialCubic4, monomialCubic5, monomialCubic6, monomialCubic7, monomialCubic8]

def literalQ : Fin 3 → Towers := ![CycleQ2SegreGaussianTangentData.q00, CycleQ2SegreGaussianTangentData.q01, CycleQ2SegreGaussianTangentData.q02]
end CycleQ2SegreModularCubicData
end

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
