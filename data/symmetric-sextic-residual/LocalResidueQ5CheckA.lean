import Proposal.LocalResidueQ5Poly

/-! Part 5a of `LocalResidueQ5`: certified degree/L1 bounds and centered `T`-grid slices 0–1. -/

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  SymmetricSexticResidual.Q5WeightsData SymmetricSexticResidual.VerticalData
  SymmetricSexticResidual.VerticalIdentity
  PolynomialEncoding.KroneckerCheck QuadraticCovers
  CrossedRationalResidue Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

/-! ### Section 4: Factored Centered Grid × Kronecker Kernel Check (`sum_RQ5_eta_L`) -/

def masterBits : ℕ := 474
def masterDegS : ℕ := 70
def masterLim : ℕ := Nat.pow 2 masterBits
def bS2D : ℤ := Int.ofNat masterLim
def bQ2D : ℤ := Int.ofNat (Nat.pow 2 (masterDegS * masterBits))
def c2D : SQCache ℤ := evalSQCache intOps bS2D bQ2D
def cPB2D : SQCache PB := evalSQCache pbOps ⟨1, 0, 0, 1⟩ ⟨0, 1, 0, 1⟩

def checkMasterBounds : Bool :=
  (evalTStep pbOps ⟨1, 0, 0, 1⟩ cPB2D ⟨0, 0, 1, 10⟩).all fun row =>
    row.all fun b => Nat.blt b.dS masterDegS && Nat.blt b.dT 20 && Nat.blt b.M masterLim

def checkMasterTChunk (lo : ℤ) (n : ℕ) : Bool :=
  allRange lo n fun t =>
    (evalTStep intOps bS2D c2D t).all fun row =>
      row.all fun z => z == 0

lemma checkMasterTChunk_append (lo : ℤ) (m n : ℕ) :
    checkMasterTChunk lo (m + n) = (checkMasterTChunk lo m && checkMasterTChunk (lo + (m : ℤ)) n) :=
  allRange_append lo m n _

lemma master_bounds_ok : checkMasterBounds = true := by decide +kernel
lemma master_t_0 : checkMasterTChunk (-9) 4 = true := by decide +kernel
lemma master_t_1 : checkMasterTChunk (-5) 4 = true := by decide +kernel

end SymmetricSexticResidual.LocalResidueQ5
