import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Transporting a velocity to a derivation

Restrict a velocity along a ring map and identify its values through a ring
isomorphism. Compatibility of the scalar actions and vanishing on complex
constants give a complex-linear derivation on the source ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

namespace CycleQ2LiteralAbelJacobiEvaluationVelocityAlgebra

variable {S C B A : Type*} [CommRing S] [CommRing C] [CommRing B] [CommRing A]
  [Algebra ℂ S] [Algebra ℂ C] [Algebra S C]
  (j : S →+* B) (s : B →+* A) (e : C ≃+* A) (d : B →+ A)
  (hcomp : ∀ x, e (algebraMap S C x) = s (j x))
  (hscalar : ∀ z, algebraMap S C (algebraMap ℂ S z) = algebraMap ℂ C z)
  (hleib : ∀ x y, d (x * y) = s x * d y + s y * d x)
  (hconst : ∀ z, d (j (algebraMap ℂ S z)) = 0)

/-- Descend a Leibniz velocity using the chosen scalar action of the source on its values. -/
def descend : Derivation ℂ S C where
  toFun x := e.symm (d (j x))
  map_add' x y := by simp
  map_smul' z x := by
    change e.symm (d (j (z • x))) = z • e.symm (d (j x))
    apply e.injective
    simp only [Algebra.smul_def, RingEquiv.apply_symm_apply, map_mul, hleib, hconst,
      mul_zero, add_zero, ← hscalar, hcomp]
  map_one_eq_zero' := by
    change e.symm (d (j 1)) = 0
    simpa only [map_one, map_zero] using congrArg e.symm (hconst 1)
  leibniz' x y := by
    change e.symm (d (j (x * y))) = x • e.symm (d (j y)) + y • e.symm (d (j x))
    apply e.injective
    simp only [Algebra.smul_def, map_add, map_mul, RingEquiv.apply_symm_apply, hleib, hcomp]

/-- Evaluation through the comparison isomorphism recovers the given velocity. -/
@[simp] theorem descend_apply (x : S) :
    e (descend j s e d hcomp hscalar hleib hconst x) = d (j x) :=
  e.apply_symm_apply _

#print axioms descend_apply

end CycleQ2LiteralAbelJacobiEvaluationVelocityAlgebra
