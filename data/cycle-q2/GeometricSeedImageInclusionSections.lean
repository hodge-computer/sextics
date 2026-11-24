import Proposal.GeometricSeedImageLocalizedModules
import Proposal.GeometricSeedPrincipalSections

/-!
# The original image inclusion on normalized principal-open sections

Localizing the original matrix-image subtype inclusion gives the literal
subtype inclusion of the localized matrix image into the localized three
coordinates. The native principal-section comparison therefore carries
the original associated-sheaf inclusion to that literal vector inclusion
on every section.

The comparisons retain the native action of the original ring. No finite
presentation, injectivity of the coefficient map, or extra regularity of
the localizing element is required. Transport to a common projective free
sheaf and compatibility between different charts remain separate steps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedImageInclusionSections

open CategoryTheory AlgebraicGeometry
open CycleQ2SegreFactorSequence CycleQ2SeedProjectiveImageTwist
  CycleQ2SeedImageLocalization CycleQ2SeedImageLocalizedModules
  CycleQ2SeedPrincipalSections

variable {A : Type u} [CommRing A]

section Localization

variable (F : FactorData A) (S : Submonoid A)
variable (B : Type u) [CommRing B] [Algebra A B] [IsLocalization S B]

/-- The localized original subtype map is the actual localized-image
inclusion, with both sides viewed as linear maps over the original ring. -/
theorem localizedImageInclusion_eq :
    IsLocalizedModule.map S (imageLocalizationMap F S B) (coordinateMap B)
        (Regrading.Image F).subtype =
      ((Regrading.Image (localizedFactorData F S B)).subtype).restrictScalars A := by
  apply IsLocalizedModule.linearMap_ext S
    (imageLocalizationMap F S B) (coordinateMap B)
  apply LinearMap.ext
  intro z
  change IsLocalizedModule.map S (imageLocalizationMap F S B) (coordinateMap B)
      (Regrading.Image F).subtype (imageLocalizationMap F S B z) =
    (imageLocalizationMap F S B z).val
  rw [IsLocalizedModule.map_apply]
  funext a
  exact (imageLocalizationMap_apply F S B z a).symm

end Localization

section PrincipalSections

variable (F : FactorData A) (r : A)
variable (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away r B]

/-- Normalizing the native section map of the original inclusion yields
the literal inclusion of the localized image, on the entire section module. -/
theorem principalImageInclusion_square :
    (sectionsEquiv (R := CommRingCat.of A)
        (ModuleCat.of A (Fin 3 → A)) r (coordinateMap B)).toLinearMap.comp
      (sectionsMap (R := CommRingCat.of A) (ModuleCat.ofHom (R := A) (Regrading.Image F).subtype) r) =
    (((Regrading.Image (localizedFactorData F (Submonoid.powers r) B)).subtype).restrictScalars A).comp
      (sectionsEquiv (R := CommRingCat.of A)
        (ModuleCat.of A (Regrading.Image F)) r
        (imageLocalizationMap F (Submonoid.powers r) B)).toLinearMap := by
  rw [← localizedImageInclusion_eq F (Submonoid.powers r) B]
  exact sectionsEquiv_naturality (R := CommRingCat.of A)
    (ModuleCat.ofHom (R := A) (Regrading.Image F).subtype) r
    (imageLocalizationMap F (Submonoid.powers r) B) (coordinateMap B)

/-- Every native principal-open image section has exactly its normalized
image vector as the normalized value of the original sheaf inclusion. -/
theorem principalImageInclusion_apply
    (s : principalSections (R := CommRingCat.of A)
      (ModuleCat.of A (Regrading.Image F)) r) :
    sectionsEquiv (R := CommRingCat.of A)
        (ModuleCat.of A (Fin 3 → A)) r (coordinateMap B)
        (sectionsMap (R := CommRingCat.of A) (ModuleCat.ofHom (R := A) (Regrading.Image F).subtype) r s) =
      (sectionsEquiv (R := CommRingCat.of A)
        (ModuleCat.of A (Regrading.Image F)) r
        (imageLocalizationMap F (Submonoid.powers r) B) s).val :=
  LinearMap.congr_fun (principalImageInclusion_square F r B) s

end PrincipalSections

#print axioms localizedImageInclusion_eq
#print axioms principalImageInclusion_square
#print axioms principalImageInclusion_apply

end CycleQ2SeedImageInclusionSections
end
