import Proposal.GeometricSeedImageLocalizedModules
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Localization of the literal image-to-ideal-dual isomorphism

The Hom-localization map below takes values in the dual of the actual
extended ideal, over the actual localized coefficient ring. Agreement
on original ideal elements identifies its image-duality value as an
entire functional. Finite presentation of the original ideal then makes
this Hom map a module localization.

Localizing the original image-dual equivalence gives exactly the literal
linkage equivalence over the localized ring, on every localized image
vector. The generic finite-presentation hypothesis must be discharged
when applying this component to the projective chart modules.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. The geometric route
and remaining certificate obligation are credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedImageLocalizedDuality

open CycleQ2SegreFactorSequence CycleQ2SeedProjectiveImageTwist
  CycleQ2SeedImageLocalization CycleQ2SeedImageLocalizedModules

variable {A : Type*} [CommRing A]
variable (F : FactorData A) (S : Submonoid A)
variable (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]

abbrev LocalizedDual := (localizedFactorData F S B).leftIdeal →ₗ[B] B

/-- The extension of the original functional to the actual extended ideal. -/
def dualLocalizationMap :
    (F.leftIdeal →ₗ[A] A) →ₗ[A] LocalizedDual F S B :=
  IsLocalizedModule.mapExtendScalars S
    (extendedIdealMap S B F.leftIdeal) (Algebra.linearMap A B) B

theorem dualLocalizationMap_apply (φ : F.leftIdeal →ₗ[A] A) (x : F.leftIdeal) :
    dualLocalizationMap F S B φ (extendedIdealMap S B F.leftIdeal x) =
      algebraMap A B (φ x) := by
  change IsLocalizedModule.map S
      (extendedIdealMap S B F.leftIdeal) (Algebra.linearMap A B) φ
      (extendedIdealMap S B F.leftIdeal x) = _
  exact IsLocalizedModule.map_apply S _ _ φ x

/-- Evaluation uses the existing literal extension of the ideal element. -/
theorem dualLocalizationMap_original (φ : F.leftIdeal →ₗ[A] A) (x : F.leftIdeal) :
    dualLocalizationMap F S B φ (localizedLeft F S B x) = algebraMap A B (φ x) := by
  rw [← extendedLeftMap_eq_localizedLeft F S B x]
  exact dualLocalizationMap_apply F S B φ x

/-- Equality on the original ideal determines the entire extended functional.
This step does not require finite presentation. -/
theorem dualLocalizationMap_imageDual (z : Regrading.Image F) :
    dualLocalizationMap F S B (Regrading.imageDual F z) =
      Regrading.imageDual (localizedFactorData F S B)
        (imageLocalizationMap F S B z) := by
  rw [imageLocalizationMap_eq_localizedImage]
  refine imageDual_baseChange_unique F (algebraMap A B)
    (localization_linkage_regular F S B) z _ ?_
  intro x
  exact dualLocalizationMap_original F S B (Regrading.imageDual F z) x

section FinitePresentation

variable [Module.FinitePresentation A F.leftIdeal]

instance dualLocalizationMap_isLocalized :
    IsLocalizedModule S (dualLocalizationMap F S B) := by
  unfold dualLocalizationMap
  infer_instance

/-- Canonical localization of the original dual is the actual extended dual.
This equivalence is stated over the original coefficient ring. -/
def dualCanonicalEquiv :
    LocalizedModule S (F.leftIdeal →ₗ[A] A) ≃ₗ[A] LocalizedDual F S B :=
  IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (F.leftIdeal →ₗ[A] A)) (dualLocalizationMap F S B)

theorem dualCanonicalEquiv_original (φ : F.leftIdeal →ₗ[A] A) :
    dualCanonicalEquiv F S B (LocalizedModule.mkLinearMap S (F.leftIdeal →ₗ[A] A) φ) =
      dualLocalizationMap F S B φ :=
  IsLocalizedModule.linearEquiv_apply S _ _ φ

/-- Localizing the original equivalence gives an equivalence linear over B. -/
def localizedImageDualEquiv :
    Regrading.Image (localizedFactorData F S B) ≃ₗ[B] LocalizedDual F S B :=
  IsLocalizedModule.mapEquiv S (imageLocalizationMap F S B)
    (dualLocalizationMap F S B) B (Regrading.imageDual F)

/-- The localized original equivalence agrees on every localized vector
with the literal linkage comparison of the transported factor data. -/
theorem localizedImageDualEquiv_toLinearMap :
    (localizedImageDualEquiv F S B).toLinearMap =
      (Regrading.imageDual (localizedFactorData F S B)).toLinearMap := by
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext S
    (imageLocalizationMap F S B) (dualLocalizationMap F S B)
  apply LinearMap.ext
  intro z
  change IsLocalizedModule.map S (imageLocalizationMap F S B)
      (dualLocalizationMap F S B) (Regrading.imageDual F).toLinearMap
      (imageLocalizationMap F S B z) =
    Regrading.imageDual (localizedFactorData F S B) (imageLocalizationMap F S B z)
  rw [IsLocalizedModule.map_apply]
  exact dualLocalizationMap_imageDual F S B z

theorem localizedImageDualEquiv_eq :
    localizedImageDualEquiv F S B = Regrading.imageDual (localizedFactorData F S B) := by
  apply LinearEquiv.ext
  intro z
  exact LinearMap.congr_fun (localizedImageDualEquiv_toLinearMap F S B) z

end FinitePresentation

#print axioms dualLocalizationMap_original
#print axioms dualLocalizationMap_imageDual
#print axioms dualLocalizationMap_isLocalized
#print axioms dualCanonicalEquiv_original
#print axioms localizedImageDualEquiv_eq

end CycleQ2SeedImageLocalizedDuality
end
