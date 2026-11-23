import Proposal.LocalResidueQ5CheckA

/-! Part 5b of `LocalResidueQ5`: centered `T`-grid slices 2–4 and full `master_values_ok`. -/

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

lemma master_t_2 : checkMasterTChunk (-1) 4 = true := by decide +kernel
lemma master_t_3 : checkMasterTChunk 3 4 = true := by decide +kernel
lemma master_t_4 : checkMasterTChunk 7 4 = true := by decide +kernel

lemma master_values_ok : checkMasterTChunk (-9) 20 = true := by
  rw [show (20 : ℕ) = 4 + 16 from rfl, checkMasterTChunk_append, master_t_0, Bool.true_and]
  rw [show ((-9 : ℤ) + (4 : ℕ)) = -5 from rfl, show (16 : ℕ) = 4 + 12 from rfl, checkMasterTChunk_append, master_t_1, Bool.true_and]
  rw [show ((-5 : ℤ) + (4 : ℕ)) = -1 from rfl, show (12 : ℕ) = 4 + 8 from rfl, checkMasterTChunk_append, master_t_2, Bool.true_and]
  rw [show ((-1 : ℤ) + (4 : ℕ)) = 3 from rfl, show (8 : ℕ) = 4 + 4 from rfl, checkMasterTChunk_append, master_t_3, Bool.true_and]
  exact master_t_4


end SymmetricSexticResidual.LocalResidueQ5
