import Proposal.GeometricSeedProjectiveLocalizedDuality
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual overlap transition on both module models

The dual transition is precomposition with the identity-valued ideal
identification, followed by multiplication by the positive fourth power
of the original coordinate ratio. It is an equivalence on the entire
ideal-dual module. The existing image transition and image-dual maps
therefore form a square of module isomorphisms, and applying the native
associated-sheaf functor gives the same square of sheaf isomorphisms.

These sheaves are the literal overlap module models on the spectrum of
the actual overlap section ring. Binding them to the original restricted
projective sheaves and proving triple-overlap descent are further steps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedOverlapTransitionModels

open CategoryTheory AlgebraicGeometry
open CycleQ2SeedProjectiveImageTwist CycleQ2SeedProjectiveImageRestriction
  CycleQ2SeedProjectiveImageCompatibility CycleQ2SeedProjectiveLocalizedDuality

/-- The dual of the actual identity-valued identification of overlap ideals. -/
def dualIdealIdentification (i j : Fin 3) :
    LeftOverlapDual i j ≃ₗ[OverlapSections i j] RightOverlapDual i j :=
  (idealIdentification i j).arrowCongr
    (LinearEquiv.refl (OverlapSections i j) (OverlapSections i j))

/-- The dual transition retains the positive degree-four multiplier. -/
def dualTransition (i j : Fin 3) :
    LeftOverlapDual i j ≃ₗ[OverlapSections i j] RightOverlapDual i j :=
  (dualIdealIdentification i j).trans (LinearEquiv.smulOfUnit (ratioUnit i j ^ 4))

theorem dualTransition_apply (i j : Fin 3) (φ : LeftOverlapDual i j) :
    dualTransition i j φ =
      (ratioUnit i j : OverlapSections i j) ^ 4 •
        φ.comp (idealIdentification i j).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [dualTransition, dualIdealIdentification, LinearEquiv.trans_apply,
    LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

/-- The established pointwise square is an equality of module morphisms. -/
theorem moduleTransition_square (i j : Fin 3) :
    (imageTransition i j).toModuleIso.hom ≫
        (Regrading.imageDual (rightData i j)).toModuleIso.hom =
      (Regrading.imageDual (leftData i j)).toModuleIso.hom ≫
        (dualTransition i j).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change Regrading.imageDual (rightData i j) (imageTransition i j z) =
    dualTransition i j (Regrading.imageDual (leftData i j) z)
  rw [dualTransition_apply]
  exact imageDual_compatibility i j z

abbrev leftImageModelSheaf (i j : Fin 3) :=
  tilde (ModuleCat.of (OverlapSections i j) (Regrading.Image (leftData i j)))

abbrev rightImageModelSheaf (i j : Fin 3) :=
  tilde (ModuleCat.of (OverlapSections i j) (Regrading.Image (rightData i j)))

abbrev leftDualModelSheaf (i j : Fin 3) :=
  tilde (ModuleCat.of (OverlapSections i j) (LeftOverlapDual i j))

abbrev rightDualModelSheaf (i j : Fin 3) :=
  tilde (ModuleCat.of (OverlapSections i j) (RightOverlapDual i j))

def modelImageTransition (i j : Fin 3) :
    leftImageModelSheaf i j ≅ rightImageModelSheaf i j :=
  (tilde.functor (CommRingCat.of (OverlapSections i j))).mapIso
    (imageTransition i j).toModuleIso

def modelDualTransition (i j : Fin 3) :
    leftDualModelSheaf i j ≅ rightDualModelSheaf i j :=
  (tilde.functor (CommRingCat.of (OverlapSections i j))).mapIso
    (dualTransition i j).toModuleIso

def leftModelDuality (i j : Fin 3) :
    leftImageModelSheaf i j ≅ leftDualModelSheaf i j :=
  (tilde.functor (CommRingCat.of (OverlapSections i j))).mapIso
    (Regrading.imageDual (leftData i j)).toModuleIso

def rightModelDuality (i j : Fin 3) :
    rightImageModelSheaf i j ≅ rightDualModelSheaf i j :=
  (tilde.functor (CommRingCat.of (OverlapSections i j))).mapIso
    (Regrading.imageDual (rightData i j)).toModuleIso

/-- The native associated-sheaf functor preserves the actual overlap square. -/
theorem modelTransition_square (i j : Fin 3) :
    (modelImageTransition i j).hom ≫ (rightModelDuality i j).hom =
      (leftModelDuality i j).hom ≫ (modelDualTransition i j).hom := by
  change (tilde.functor (CommRingCat.of (OverlapSections i j))).map _ ≫
      (tilde.functor (CommRingCat.of (OverlapSections i j))).map _ =
    (tilde.functor (CommRingCat.of (OverlapSections i j))).map _ ≫
      (tilde.functor (CommRingCat.of (OverlapSections i j))).map _
  rw [← Functor.map_comp, ← Functor.map_comp, moduleTransition_square]

#print axioms dualIdealIdentification
#print axioms dualTransition_apply
#print axioms moduleTransition_square
#print axioms modelTransition_square

end CycleQ2SeedOverlapTransitionModels
end
