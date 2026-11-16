/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx` (prepared with OpenAI ChatGPT assistance); the target-specific source, companion and trace data are replaced, all other modules are unchanged. Adaptation prepared with Claude Code assistance for `DiamondJM`. -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic
import Proposal.DeckTrace

/- Source component: CoverSource -/
section
/-!
Exact orientation and source normalization for the holdout cover. The
quotient order is X0,X1,X2,S,P,beta. In that order the source has a positive
sign. These scalar identities and the finite-field trace implication do
not assert a certificate. Prepared with OpenAI ChatGPT assistance for a
contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

section Scalars

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Jacobian of (y,T,beta) to (Y0,Y1,Y2), with alpha^6+beta^6=1. -/
theorem physical_cover_jacobian (a b t : K) (ha : a ≠ 0)
    (hab : a^6+b^6=1) :
    Matrix.det !![0, a, -t*b^5/a^5; 1, 0, 0; 0, b, t] = -t/a^5 := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination -t*hab

omit [CharZero K] in
/-- The quotient coordinates occur in S,P order. -/
theorem quotient_cover_jacobian (y t : K) :
    Matrix.det !![2*y, 2*t, 0; t, y, 0; 0, 0, (1:K)] =
      -2*(t^2-y^2) := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Source multiplication under the exact physical-to-quotient Jacobian. -/
theorem cover_source_identity (a b x0 y t : K) (ha : a ≠ 0) (ht : t ≠ 0) :
    (2*a^5*(t^2-y^2)/t) * (x0^3*(y*t)*b/(2*a^4)) =
      x0^3*(a*t)*y*(b*t) - x0^3*(a*t)*y^3*(b*t)/t^2 := by
  field_simp <;> ring

/-- The same identity applies to the distinguished normal-divergence
source, because the coordinate Jacobian is independent of X0. -/
theorem cover_normal_source_identity (a b x0 y t g h : K)
    (ha : a ≠ 0) (ht : t ≠ 0) :
    (2*a^5*(t^2-y^2)/t) *
      (((3*x0^2*(y*t)*b/(2*a^4))*g -
        (x0^3*(y*t)*b/(2*a^4))*h)/g^2) =
      (((3*x0^2*(a*t)*y*(b*t))*g-(x0^3*(a*t)*y*(b*t))*h)/g^2) -
        (((3*x0^2*(a*t)*y^3*(b*t))*g-(x0^3*(a*t)*y^3*(b*t))*h)/g^2)/t^2 := by
  by_cases hg : g = 0
  · simp [hg]
  · field_simp <;> ring

end Scalars

end HoldoutConstruction

#print axioms HoldoutConstruction.physical_cover_jacobian
#print axioms HoldoutConstruction.cover_source_identity
#print axioms HoldoutConstruction.cover_normal_source_identity
end
end

/- Source component: CoverJacobian -/
section
/-!
The exact five-coordinate residue Jacobian from physical coordinates
(X1,X2,Y0,Y1,Y2) to quotient coordinates (X1,X2,S,P,beta).
The two X coordinates form an identity block. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

variable {K : Type*} [Field K]

def coverJacobianTail (a b y t : K) : Matrix (Fin 3) (Fin 3) K :=
  !![2*t*a^5, 2*y, 2*t*b^5;
     y*a^5, t, y*b^5;
     -b*a^5/t, 0, a^6/t]

theorem coverJacobianTail_det (a b y t : K) (ht : t ≠ 0)
    (hab : a^6+b^6=1) :
    (coverJacobianTail a b y t).det = 2*a^5*(t^2-y^2)/t := by
  simp only [coverJacobianTail, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination 2*a^5*(t^2-y^2)*hab

def coverResidueJacobian (a b y t : K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)
    (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0
      (coverJacobianTail a b y t))

theorem coverResidueJacobian_eq_matrix (a b y t : K) :
    coverResidueJacobian a b y t =
      !![1,0,0,0,0;
         0,1,0,0,0;
         0,0,2*t*a^5,2*y,2*t*b^5;
         0,0,y*a^5,t,y*b^5;
         0,0,-b*a^5/t,0,a^6/t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coverResidueJacobian_det (a b y t : K) (ht : t ≠ 0)
    (hab : a^6+b^6=1) :
    (coverResidueJacobian a b y t).det = 2*a^5*(t^2-y^2)/t := by
  rw [coverResidueJacobian, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    coverJacobianTail_det a b y t ht hab]

theorem coverResidueJacobian_det_ne_zero [CharZero K] (a b y t : K)
    (ha : a ≠ 0) (ht : t ≠ 0) (hquad : t^2-y^2 ≠ 0)
    (hab : a^6+b^6=1) :
    (coverResidueJacobian a b y t).det ≠ 0 := by
  rw [coverResidueJacobian_det a b y t ht hab]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hquad) ht

end HoldoutConstruction

#print axioms HoldoutConstruction.coverResidueJacobian_det
#print axioms HoldoutConstruction.coverResidueJacobian_det_ne_zero
end
end
