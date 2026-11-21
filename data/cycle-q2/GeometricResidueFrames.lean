import Proposal.GeometricAdjunctionOverlap
import Mathlib.Tactic.Module

/-!
# Derivations and compatible local residue representatives

The coordinate-change matrix from `GeometricAdjunctionOverlap` acts on
actual derivations into modules. In particular it acts on the universal
Kahler derivation; it is not just a matrix with the right determinant.

For three differential generators subject to the two actual equation
relations, the signed 2x2 Jacobian minors give consistent residue
representatives. Whenever two minors are units, the corresponding
normalized differentials are equal. No division by a nonunit or use of a
function field is needed.

These are local algebraic pieces for an adjunction comparison. This file
does not identify global projective sheaves, prove a Serre trace theorem,
or conclude that the protected residue is exact.
Validation: compiled with the repository's pinned Lean 4.33.1 and independently
kernel-replayed. This check establishes the displayed local differential
identities; it does not establish the global comparisons listed above.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricResidueFrames

open CycleQ2GeometricAdjunctionOverlap CycleQ2GeometricAffineCurveCharts

section LinearRelations

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def rowAction (f : Fin 3 → R) (w : Fin 3 → M) : M :=
  f 0 • w 0 + f 1 • w 1 + f 2 • w 2

/-- Cofactors with the signs appropriate to df wedge dh. -/
def jacobianMinors (f g : Fin 3 → R) : Fin 3 → R :=
  ![f 1 * g 2 - f 2 * g 1,
    f 2 * g 0 - f 0 * g 2,
    f 0 * g 1 - f 1 * g 0]

theorem minor_balance01 (f g : Fin 3 → R) (w : Fin 3 → M)
    (hf : rowAction f w = 0) (hg : rowAction g w = 0) :
    jacobianMinors f g 0 • w 1 = jacobianMinors f g 1 • w 0 := by
  apply sub_eq_zero.mp
  calc
    jacobianMinors f g 0 • w 1 - jacobianMinors f g 1 • w 0 =
        g 2 • rowAction f w - f 2 • rowAction g w := by
      dsimp [jacobianMinors, rowAction]
      module
    _ = 0 := by rw [hf, hg]; simp

theorem minor_balance02 (f g : Fin 3 → R) (w : Fin 3 → M)
    (hf : rowAction f w = 0) (hg : rowAction g w = 0) :
    jacobianMinors f g 0 • w 2 = jacobianMinors f g 2 • w 0 := by
  apply sub_eq_zero.mp
  calc
    jacobianMinors f g 0 • w 2 - jacobianMinors f g 2 • w 0 =
        f 1 • rowAction g w - g 1 • rowAction f w := by
      dsimp [jacobianMinors, rowAction]
      module
    _ = 0 := by rw [hf, hg]; simp

theorem minor_balance12 (f g : Fin 3 → R) (w : Fin 3 → M)
    (hf : rowAction f w = 0) (hg : rowAction g w = 0) :
    jacobianMinors f g 1 • w 2 = jacobianMinors f g 2 • w 1 := by
  apply sub_eq_zero.mp
  calc
    jacobianMinors f g 1 • w 2 - jacobianMinors f g 2 • w 1 =
        g 0 • rowAction f w - f 0 • rowAction g w := by
      dsimp [jacobianMinors, rowAction]
      module
    _ = 0 := by rw [hf, hg]; simp

theorem minor_balance (f g : Fin 3 → R) (w : Fin 3 → M)
    (hf : rowAction f w = 0) (hg : rowAction g w = 0) (i j : Fin 3) :
    jacobianMinors f g i • w j = jacobianMinors f g j • w i := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact minor_balance01 f g w hf hg
  · exact minor_balance02 f g w hf hg
  · exact (minor_balance01 f g w hf hg).symm
  · rfl
  · exact minor_balance12 f g w hf hg
  · exact (minor_balance02 f g w hf hg).symm
  · exact (minor_balance12 f g w hf hg).symm
  · rfl

/-- Two invertible Jacobian minors define the same residue differential.
The normalization uses the signed minors, so no further parity convention
is hidden in the statement. -/
theorem local_residue_eq (f g : Fin 3 → R) (w : Fin 3 → M)
    (hf : rowAction f w = 0) (hg : rowAction g w = 0)
    (i j : Fin 3) (u v : Rˣ)
    (hu : (u : R) = jacobianMinors f g i)
    (hv : (v : R) = jacobianMinors f g j) :
    (↑(u⁻¹) : R) • w i = (↑(v⁻¹) : R) • w j := by
  have hbalance : (u : R) • w j = (v : R) • w i := by
    rw [hu, hv]
    exact minor_balance f g w hf hg i j
  have huinv : (↑(u⁻¹) : R) * (u : R) = 1 := u.inv_mul
  have hvinv : (↑(v⁻¹) : R) * (v : R) = 1 := v.inv_mul
  calc
    (↑(u⁻¹) : R) • w i =
        (↑(u⁻¹) : R) • ((↑(v⁻¹) : R) • ((v : R) • w i)) := by
      simp only [smul_smul, mul_assoc, hvinv, mul_one]
    _ = (↑(u⁻¹) : R) • ((↑(v⁻¹) : R) • ((u : R) • w j)) := by
      rw [← hbalance]
    _ = (↑(v⁻¹) : R) • ((↑(u⁻¹) : R) • ((u : R) • w j)) := by
      exact smul_comm _ _ _
    _ = (↑(v⁻¹) : R) • w j := by
      simp only [smul_smul, mul_assoc, huinv, mul_one]

end LinearRelations

section Derivations

variable {k R M : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

/-- Inverse differentiation valid for a unit in any commutative algebra. -/
theorem derivation_unit_inverse (D : Derivation k R M) (b : Rˣ) :
    D (↑(b⁻¹) : R) = -((↑(b⁻¹) : R) ^ 2) • D (b : R) := by
  have h := D.leibniz (b : R) (↑(b⁻¹) : R)
  rw [b.mul_inv, D.map_one_eq_zero] at h
  have h' := congrArg (fun z : M => (↑(b⁻¹) : R) • z) h
  have hi : (↑(b⁻¹) : R) * (b : R) = 1 := b.inv_mul
  have hz : D (↑(b⁻¹) : R) + (↑(b⁻¹) : R) ^ 2 • D (b : R) = 0 := by
    simpa only [smul_zero, smul_add, smul_smul, hi, one_smul, pow_two] using h'.symm
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left hz

/-- The displayed Jacobian is the genuine change on differential generators
for every derivation, including the universal Kahler derivation. -/
theorem coordinate_differential_change (D : Derivation k R M) (a c : R) (b : Rˣ) :
    ![D (a * (↑(b⁻¹) : R)), D (↑(b⁻¹) : R), D (c * (↑(b⁻¹) : R))] =
      (fun i : Fin 3 => ∑ j : Fin 3,
        coordinateJacobian a c (↑(b⁻¹) : R) i j • ![D a, D (b : R), D c] j) := by
  funext i
  fin_cases i <;>
    simp [coordinateJacobian, Fin.sum_univ_succ, Derivation.leibniz,
      derivation_unit_inverse, smul_smul] <;> module

/-- Relative fiber differentiation; the coefficient hypotheses are explicit.
For Kahler differentials over C the three coefficients are complex scalars. -/
theorem first_equation_differentials (D : Derivation k R M)
    (r i θ a b c : R) (hr : D r = 0) (hi : D i = 0) (hθ : D θ = 0) :
    D (quadricOne r a b c) = rowAction (gradQuadricOne r a) ![D a, D b, D c] ∧
    D (cubicOne i θ a b c) =
      rowAction (gradCubicOne i θ a b c) ![D a, D b, D c] := by
  constructor
  · simp [quadricOne, gradQuadricOne, rowAction, Derivation.leibniz,
      Derivation.leibniz_pow, hr] <;> module
  · simp [cubicOne, gradCubicOne, rowAction, Derivation.leibniz,
      Derivation.leibniz_pow, hr, hi, hθ] <;> module

/-- On the actual affine curve, the differential relations needed for the
local residue identity follow by differentiation of its equations. -/
theorem first_equations_give_relations (D : Derivation k R M)
    (r i θ a b c : R) (hr : D r = 0) (hi : D i = 0) (hθ : D θ = 0)
    (hf : quadricOne r a b c = 0) (hh : cubicOne i θ a b c = 0) :
    rowAction (gradQuadricOne r a) ![D a, D b, D c] = 0 ∧
    rowAction (gradCubicOne i θ a b c) ![D a, D b, D c] = 0 := by
  have hd := first_equation_differentials D r i θ a b c hr hi hθ
  constructor
  · rw [← hd.1, hf, map_zero]
  · rw [← hd.2, hh, map_zero]

end Derivations

end CycleQ2GeometricResidueFrames

end
