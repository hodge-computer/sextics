import Proposal.SymmetricNegativeSource
import Proposal.SymmetricNegativeJacobianGrading
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! The actual twelve Jacobian directions lie in the negative weighted-sextic
source space. Its quotient by their span has dimension 48. Identifying this
span with the full Jacobian ideal in this bidegree is a separate statement.
-/

noncomputable section

namespace SymmetricNegativeJacobian

open MvPolynomial SymmetricNegativeSource
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem bidegree_formula (e : Fin 5 →₀ ℕ) :
    Finsupp.weight bidegreeWeight e =
      (weightedDegree e, ((e 2 + e 3 : ℕ) : ZMod 2)) := by
  apply Prod.ext <;>
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, bidegreeWeight,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    weightedDegree, nsmul_eq_mul, Nat.mul_comm, add_assoc]

theorem bihomogeneous_iff_mem_source (p : Poly) :
    p.IsWeightedHomogeneous bidegreeWeight (6,1) ↔ p ∈ source := by
  rw [mem_source]
  constructor
  · intro hp e he
    have h := hp he
    rw [bidegree_formula] at h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have hsnd := congrArg Prod.snd h
    have hv := congrArg ZMod.val hsnd
    simpa only [ZMod.val_natCast, ZMod.val_one] using hv
  · intro hp e he
    obtain ⟨hdegree, hodd⟩ := hp e he
    rw [bidegree_formula, hdegree]
    congr 1
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast, ZMod.val_one] using hodd

theorem direction_mem_source (j : Fin 12) : direction j ∈ source :=
  (bihomogeneous_iff_mem_source _).mp (direction_bihomogeneous j)

def directionInSource (j : Fin 12) : source := ⟨direction j, direction_mem_source j⟩

theorem directionInSource_independent : LinearIndependent ℂ directionInSource := by
  apply LinearIndependent.of_comp source.subtype
  exact direction_independent

/-- The span inside the actual coefficient-defined source space. -/
def directionSpan : Submodule ℂ source := Submodule.span ℂ (Set.range directionInSource)

theorem directionSpan_finrank : Module.finrank ℂ directionSpan = 12 := by
  simpa [directionSpan] using finrank_span_eq_card directionInSource_independent

theorem direction_quotient_finrank :
    Module.finrank ℂ (source ⧸ directionSpan) = 48 := by
  have h := Submodule.finrank_quotient_add_finrank directionSpan
  rw [directionSpan_finrank, source_finrank] at h
  omega

#print axioms direction_mem_source
#print axioms directionSpan_finrank
#print axioms direction_quotient_finrank

end SymmetricNegativeJacobian
