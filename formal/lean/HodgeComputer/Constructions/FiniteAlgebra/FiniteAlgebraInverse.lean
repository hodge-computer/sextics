import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

namespace FiniteAlgebraInverse

open Module
open scoped Matrix
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix invertibility of multiplication by x implies that x itself is a unit.
The inverse element is obtained by applying the inverse matrix to the coordinates of 1. -/
theorem isUnit_of_leftMulMatrix (b : Basis n R A) (x : A)
    (h : IsUnit (Algebra.leftMulMatrix b x).det) : IsUnit x := by
  let c : n → R := (Algebra.leftMulMatrix b x)⁻¹ *ᵥ b.repr (1 : A)
  let y : A := b.equivFun.symm c
  have hy : x * y = 1 := by
    apply b.equivFun.injective
    change (fun i => b.repr (x * y) i) = fun i => b.repr (1 : A) i
    rw [← Algebra.leftMulMatrix_mulVec_repr]
    have hc : (fun i => b.repr y i) = c := b.equivFun.apply_symm_apply c
    change Algebra.leftMulMatrix b x *ᵥ (fun i => b.repr y i) = _
    rw [hc]
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

/-- Every ring homomorphism transports the inverse of an established unit. -/
theorem map_ringInverse {B : Type*} [CommRing B] (f : A →+* B) (x : A) (h : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  apply (h.map f).mul_left_inj.mp
  rw [← map_mul, Ring.inverse_mul_cancel _ h, map_one,
    Ring.inverse_mul_cancel _ (h.map f)]

end FiniteAlgebraInverse

