import Proposal.GeometricSeedProjectiveImageRestriction
import Proposal.GeometricSeedImageTwistedDuality

/-!
# The degree-four comparison square on actual projective overlaps

The two presentations are the actual `leftData` and `rightData` in the
section ring of the original projective intersection. Their matrix and
ideal-generator rescalings are discharged by the actual section identities.
The resulting comparison is an equality of functionals on the entire
overlap ideal, for every overlap image vector.

The last theorem also binds this equality to the original affine-chart
duality under its actual restriction map. No coefficient-map, regularity,
or rescaling premise remains in these specialized endpoints.

The identification with restricted associated-module/internal-Hom sheaves,
and subsequent global gluing, remain separate. Prepared for fqlx with OpenAI
ChatGPT assistance; the geometric route is credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveImageCompatibility

open AlgebraicGeometry
open CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction

def ratioUnit (i j : Fin 3) : Γ(Surface, OverlapOpen i j)ˣ :=
  transitionUnit i j (OverlapOpen i j)
    (pair_le_left 57 1 i.succ j.succ) (pair_le_right 57 1 i.succ j.succ)

theorem data_matrix_change (i j : Fin 3) :
    (rightData i j).matrix =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 14 • (leftData i j).matrix :=
  sectionMatrix_change i j (OverlapOpen i j)
    (pair_le_left 57 1 i.succ j.succ) (pair_le_right 57 1 i.succ j.succ)

theorem data_left_change (i j : Fin 3) (a : Fin 3) :
    (rightData i j).left a =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 10 * (leftData i j).left a :=
  congrFun (sectionLeft_change i j (OverlapOpen i j)
    (pair_le_left 57 1 i.succ j.succ) (pair_le_right 57 1 i.succ j.succ)) a

/-- The two actual extended orbit ideals coincide as ideals of sections. -/
theorem orbitIdeals_eq (i j : Fin 3) :
    (leftData i j).leftIdeal = (rightData i j).leftIdeal :=
  CycleQ2SeedImageTwistedDuality.leftIdeal_eq
    (leftData i j) (rightData i j) (ratioUnit i j) (data_left_change i j)

def idealIdentification (i j : Fin 3) :
    (leftData i j).leftIdeal ≃ₗ[Γ(Surface, OverlapOpen i j)] (rightData i j).leftIdeal :=
  CycleQ2SeedImageTwistedDuality.idealEquiv
    (leftData i j) (rightData i j) (ratioUnit i j) (data_left_change i j)

theorem idealIdentification_val (i j : Fin 3) (x : (leftData i j).leftIdeal) :
    (idealIdentification i j x : Γ(Surface, OverlapOpen i j)) = x.val :=
  CycleQ2SeedImageTwistedDuality.idealEquiv_val
    (leftData i j) (rightData i j) (ratioUnit i j) (data_left_change i j) x

def imageTransition (i j : Fin 3) :
    Regrading.Image (leftData i j) ≃ₗ[Γ(Surface, OverlapOpen i j)]
      Regrading.Image (rightData i j) :=
  CycleQ2SeedImageTwistedDuality.imageTransition
    (leftData i j) (rightData i j) (ratioUnit i j) (data_matrix_change i j)

theorem imageTransition_val (i j : Fin 3) (z : Regrading.Image (leftData i j)) :
    (imageTransition i j z).val =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 14 • z.val := rfl

/-- The degree-four square holds for every actual overlap image vector,
as equality of linear functionals on the whole extended orbit ideal. -/
theorem imageDual_compatibility (i j : Fin 3) (z : Regrading.Image (leftData i j)) :
    Regrading.imageDual (rightData i j) (imageTransition i j z) =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 4 •
        ((Regrading.imageDual (leftData i j) z).comp (idealIdentification i j).symm.toLinearMap) :=
  CycleQ2SeedImageTwistedDuality.imageDual_transition
    (leftData i j) (rightData i j) (ratioUnit i j)
    (data_matrix_change i j) (data_left_change i j) z

theorem imageDual_compatibility_apply (i j : Fin 3)
    (z : Regrading.Image (leftData i j)) (x : (rightData i j).leftIdeal) :
    Regrading.imageDual (rightData i j) (imageTransition i j z) x =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 4 *
        Regrading.imageDual (leftData i j) z ((idealIdentification i j).symm x) :=
  CycleQ2SeedImageTwistedDuality.imageDual_transition_apply
    (leftData i j) (rightData i j) (ratioUnit i j)
    (data_matrix_change i j) (data_left_change i j) z x

/-- The overlap square restricts the original affine comparison, with
the same ideal element and the positive degree-four multiplier. -/
theorem imageDual_compatibility_original (i j : Fin 3)
    (z : ImageModule i) (x : OrbitIdeal i) :
    Regrading.imageDual (rightData i j)
        (imageTransition i j (leftImageRestriction i j z))
        (idealIdentification i j
          (mappedLeft (chartFactorData i) _ (leftSection_linkage_regular i j) x)) =
      (ratioUnit i j : Γ(Surface, OverlapOpen i j)) ^ 4 *
        chartSectionMap i (OverlapOpen i j) (pair_le_left 57 1 i.succ j.succ)
          (imageDualEquiv i z x) := by
  rw [imageDual_compatibility_apply, LinearEquiv.symm_apply_apply, left_imageDual_restriction]

#print axioms orbitIdeals_eq
#print axioms imageTransition_val
#print axioms imageDual_compatibility
#print axioms imageDual_compatibility_original

end CycleQ2SeedProjectiveImageCompatibility
end
