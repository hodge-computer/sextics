import Proposal.GeometricSeedProjectiveImageTwist

/-!
# The positive twist in the actual image-to-ideal-dual comparison

For two linkage presentations over the same ring, suppose their literal
matrices differ by the fourteenth power of a unit and their literal left
generators differ by its tenth power. The extended left ideals are equal.
The corresponding image-vector change then intertwines the two original
image-dual isomorphisms with the positive fourth power of that unit.

The functional identity holds on every image vector and every ideal
element. It is proved by evaluation on the actual left generators, which
generate the ideal, and uses no chosen image-line frame.

This is a generic algebraic component. Binding its coefficient ring,
presentations, and maps to actual projective restrictions is separate.
Source-only draft: no Lean elaboration or kernel replay has been run.
No new axioms or admissions are introduced. Prepared for fqlx with OpenAI
ChatGPT assistance; the geometric route is credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedImageTwistedDuality

open Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SegreLinkageImage CycleQ2SeedProjectiveImageTwist

variable {R : Type*} [CommRing R]
variable (F G : FactorData R) (t : Rˣ)

/-- Unit rescaling of the original generators preserves the actual ideal. -/
theorem leftIdeal_eq
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a) :
    F.leftIdeal = G.leftIdeal := by
  rw [Regrading.leftIdeal_eq_span F, Regrading.leftIdeal_eq_span G]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hg : G.left a ∈ Ideal.span (Set.range G.left) :=
      Ideal.subset_span ⟨a, rfl⟩
    have he : F.left a = (((t⁻¹ : Rˣ) : R) ^ 10) * G.left a := by
      rw [hL, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ hg
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [hL]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)

/-- The ideal identification is literally the identity on ring values. -/
def idealEquiv
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a) :
    F.leftIdeal ≃ₗ[R] G.leftIdeal :=
  LinearEquiv.ofEq _ _ (leftIdeal_eq F G t hL)

theorem idealEquiv_val
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a)
    (x : F.leftIdeal) :
    (idealEquiv F G t hL x : R) = (x : R) := rfl

theorem idealEquiv_symm_val
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a)
    (x : G.leftIdeal) :
    ((idealEquiv F G t hL).symm x : R) = (x : R) := rfl

/-- Under the identity ideal comparison, the new selected generator has
exactly the original degree-ten scaling. -/
theorem idealEquiv_symm_leftElement
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a) (a : Fin 3) :
    (idealEquiv F G t hL).symm (leftElement G a) =
      (t : R) ^ 10 • leftElement F a := by
  apply Subtype.ext
  change G.left a = (t : R) ^ 10 * F.left a
  exact hL a

/-- The unit-scaled matrix has the same actual range submodule. -/
theorem image_eq
    (hM : G.matrix = (t : R) ^ 14 • F.matrix) :
    Regrading.Image G = Regrading.Image F := by
  change LinearMap.range G.matrix.mulVecLin = Regrading.Image F
  rw [hM]
  simpa only [inv_inv] using Regrading.normalized_matrix_range F t⁻¹

/-- The image-vector transition keeps the degree-fourteen multiplier. -/
def imageTransition
    (hM : G.matrix = (t : R) ^ 14 • F.matrix) :
    Regrading.Image F ≃ₗ[R] Regrading.Image G :=
  (LinearEquiv.smulOfUnit (t ^ 14) :
      Regrading.Image F ≃ₗ[R] Regrading.Image F).trans
    (LinearEquiv.ofEq _ _ (image_eq F G t hM).symm)

theorem imageTransition_val
    (hM : G.matrix = (t : R) ^ 14 • F.matrix)
    (z : Regrading.Image F) :
    (imageTransition F G t hM z).val = (t : R) ^ 14 • z.val := rfl

/-- The original image-dual maps intertwine with the positive degree-four
twist. This is equality of functionals on the entire actual target ideal. -/
theorem imageDual_transition
    (hM : G.matrix = (t : R) ^ 14 • F.matrix)
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a)
    (z : Regrading.Image F) :
    Regrading.imageDual G (imageTransition F G t hM z) =
      (t : R) ^ 4 •
        ((Regrading.imageDual F z).comp (idealEquiv F G t hL).symm.toLinearMap) := by
  apply Regrading.dual_ext G
  intro a
  rw [Regrading.imageDual_selected, imageTransition_val]
  change (t : R) ^ 14 * z.val a =
    (t : R) ^ 4 * Regrading.imageDual F z
      ((idealEquiv F G t hL).symm (leftElement G a))
  rw [idealEquiv_symm_leftElement, map_smul, Regrading.imageDual_selected]
  change (t : R) ^ 14 * z.val a = (t : R) ^ 4 * ((t : R) ^ 10 * z.val a)
  rw [← mul_assoc, ← pow_add]

theorem imageDual_transition_apply
    (hM : G.matrix = (t : R) ^ 14 • F.matrix)
    (hL : ∀ a, G.left a = (t : R) ^ 10 * F.left a)
    (z : Regrading.Image F) (x : G.leftIdeal) :
    Regrading.imageDual G (imageTransition F G t hM z) x =
      (t : R) ^ 4 *
        Regrading.imageDual F z ((idealEquiv F G t hL).symm x) := by
  exact LinearMap.congr_fun (imageDual_transition F G t hM hL z) x

#print axioms leftIdeal_eq
#print axioms imageTransition_val
#print axioms imageDual_transition
#print axioms imageDual_transition_apply

end CycleQ2SeedImageTwistedDuality
end
