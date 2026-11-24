import Proposal.GeometricSeedProjectiveImageTwist
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization of the actual image-to-orbit-dual comparison

The coordinatewise matrix-image map commutes with the original linkage
duality. For localization, transported linkage regularity is proved from
the existing regularity of the source linkage element. No regularity of
the denominators or injectivity of the coefficient map is assumed.

The final denominator identity covers every element of the extended
orbit ideal. This is the algebraic comparison needed on principal
projective overlaps; identifying those overlap rings and their sheaf
maps remains a separate geometric binding.

The protected certificate and its existing admission are unchanged.
Prepared for fqlx with OpenAI ChatGPT assistance; the geometric route is
credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedImageLocalization

open Matrix
open scoped BigOperators
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SegreLinkageImage CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageTwist

section RingMap

variable {A B : Type*} [CommRing A] [CommRing B]
variable (F : FactorData A) (f : A →+* B)
variable (hf : Function.Injective (fun z : B => f F.linkage * z))

/-- This map sends the literal image vector to its coordinatewise image.
Its range proof uses the original matrix, not a chosen duality model. -/
def imageBaseChange :
    Regrading.Image F →ₛₗ[f] Regrading.Image (mapFactorData F f hf) where
  toFun z := ⟨fun a => f (z.val a), by
    obtain ⟨v, hv⟩ := z.property
    refine ⟨fun b => f (v b), ?_⟩
    funext a
    have ha : (∑ b : Fin 3, F.matrix a b * v b) = z.val a := congrFun hv a
    change (∑ b : Fin 3, f (F.matrix a b) * f (v b)) = f (z.val a)
    simpa only [map_sum, map_mul] using congrArg f ha⟩
  map_add' z w := by
    apply Subtype.ext
    funext a
    exact map_add f (z.val a) (w.val a)
  map_smul' c z := by
    apply Subtype.ext
    funext a
    change f (c * z.val a) = f c * f (z.val a)
    exact map_mul f c (z.val a)

theorem imageBaseChange_apply (z : Regrading.Image F) (a : Fin 3) :
    (imageBaseChange F f hf z).val a = f (z.val a) := rfl

/-- The original linkage parametrization commutes with the literal map. -/
theorem imageBaseChange_rightEquivImage (y : F.rightIdeal) :
    imageBaseChange F f hf (rightEquivImage F y) =
      rightEquivImage (mapFactorData F f hf) (mappedRight F f hf y) := by
  apply Subtype.ext
  funext a
  change f ((rightEquivImage F y).val a) =
    (rightEquivImage (mapFactorData F f hf) (mappedRight F f hf y)).val a
  rw [rightEquivImage_apply, rightEquivImage_apply]
  exact (mapFactorData_pairing F f hf (leftElement F a) y).symm

/-- Base change commutes with the image-to-dual comparison on every
original ideal element, not just on the three selected generators. -/
theorem imageDual_baseChange (z : Regrading.Image F) (x : F.leftIdeal) :
    Regrading.imageDual (mapFactorData F f hf) (imageBaseChange F f hf z)
        (mappedLeft F f hf x) =
      f (Regrading.imageDual F z x) := by
  obtain ⟨y, rfl⟩ := (rightEquivImage F).surjective z
  rw [imageBaseChange_rightEquivImage]
  change pairing (mapFactorData F f hf)
      ((rightEquivImage (mapFactorData F f hf)).symm
        (rightEquivImage (mapFactorData F f hf) (mappedRight F f hf y)))
      (mappedLeft F f hf x) =
    f (pairing F ((rightEquivImage F).symm (rightEquivImage F y)) x)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact mapFactorData_pairing F f hf x y

/-- Agreement on the original ideal determines the entire extended
functional, since the actual transported generators span its domain. -/
theorem imageDual_baseChange_unique (z : Regrading.Image F)
    (φ : (mapFactorData F f hf).leftIdeal →ₗ[B] B)
    (hφ : ∀ x : F.leftIdeal,
      φ (mappedLeft F f hf x) = f (Regrading.imageDual F z x)) :
    φ = Regrading.imageDual (mapFactorData F f hf) (imageBaseChange F f hf z) := by
  apply Regrading.dual_ext (mapFactorData F f hf)
  intro a
  change φ (mappedLeft F f hf (leftElement F a)) =
    Regrading.imageDual (mapFactorData F f hf) (imageBaseChange F f hf z)
      (mappedLeft F f hf (leftElement F a))
  rw [hφ, imageDual_baseChange]

end RingMap

section Localization

variable {A : Type*} [CommRing A] (F : FactorData A)
variable (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]

include M

/-- Localization preserves regularity even when the coefficient
map is not injective or some localization denominators are zero divisors. -/
theorem localization_regular (a : A)
    (ha : Function.Injective (fun z : A => a * z)) :
    Function.Injective (fun z : B => algebraMap A B a * z) := by
  have hreg : IsRegular a := by
    refine ⟨ha, ?_⟩
    intro x y h
    apply ha
    simpa only [mul_comm] using h
  have hn : algebraMap A B a ∈ nonZeroDivisors B :=
    IsLocalization.nonZeroDivisors_le_comap M B
      (isRegular_iff_mem_nonZeroDivisors.mp hreg)
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hn).left

theorem localization_linkage_regular :
    Function.Injective (fun z : B => algebraMap A B F.linkage * z) :=
  localization_regular M B F.linkage F.regular

def localizedFactorData : FactorData B :=
  mapFactorData F (algebraMap A B) (localization_linkage_regular F M B)

def localizedImage :
    Regrading.Image F →ₛₗ[algebraMap A B] Regrading.Image (localizedFactorData F M B) :=
  imageBaseChange F (algebraMap A B) (localization_linkage_regular F M B)

def localizedLeft (x : F.leftIdeal) : (localizedFactorData F M B).leftIdeal :=
  mappedLeft F (algebraMap A B) (localization_linkage_regular F M B) x

theorem localizedImageDual_original (z : Regrading.Image F) (x : F.leftIdeal) :
    Regrading.imageDual (localizedFactorData F M B) (localizedImage F M B z)
        (localizedLeft F M B x) =
      algebraMap A B (Regrading.imageDual F z x) :=
  imageDual_baseChange F (algebraMap A B) (localization_linkage_regular F M B) z x

/-- Every element of the actual extended orbit ideal admits a denominator
whose clearing gives the original image-duality value. -/
theorem localizedImageDual_clear_denominator (z : Regrading.Image F)
    (b : (localizedFactorData F M B).leftIdeal) :
    ∃ (x : F.leftIdeal) (s : M),
      (b : B) * algebraMap A B (s : A) = algebraMap A B (x : A) ∧
      algebraMap A B (s : A) *
          Regrading.imageDual (localizedFactorData F M B) (localizedImage F M B z) b =
        algebraMap A B (Regrading.imageDual F z x) := by
  obtain ⟨⟨x, s⟩, hxs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff M B).mp b.property
  refine ⟨x, s, hxs, ?_⟩
  have he : algebraMap A B (s : A) • b = localizedLeft F M B x := by
    apply Subtype.ext
    change algebraMap A B (s : A) * (b : B) = algebraMap A B (x : A)
    exact (mul_comm _ _).trans hxs
  have h := congrArg
    (Regrading.imageDual (localizedFactorData F M B) (localizedImage F M B z)) he
  simpa only [map_smul, smul_eq_mul, localizedImageDual_original] using h

end Localization

#print axioms imageDual_baseChange
#print axioms imageDual_baseChange_unique
#print axioms localization_linkage_regular
#print axioms localizedImageDual_clear_denominator

end CycleQ2SeedImageLocalization
end
