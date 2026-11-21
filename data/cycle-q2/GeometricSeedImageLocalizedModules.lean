import Proposal.GeometricSeedImageLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Canonical localization and the literal extended seed modules

The actual extended ideal and the actual matrix image satisfy the module
localization property for their literal coefficient maps. The proofs use
localization of submodules and the finite-product localization map on
the three matrix coordinates. They do not assume regular denominators,
an injective coefficient map, or finite presentation.

The resulting canonical equivalences are linear over the original ring.
Their original-element formulas bind them to the existing literal
`localizedLeft` and `localizedImage` maps. Identifying the coefficient
map with a particular projective restriction is separate.

No axioms or admissions are introduced. Prepared for fqlx with OpenAI
ChatGPT assistance; the geometric route is credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedImageLocalizedModules

open Matrix
open scoped BigOperators
open CycleQ2SegreFactorSequence CycleQ2SeedProjectiveImageTwist
  CycleQ2SeedImageLocalization

variable {A : Type*} [CommRing A]
variable (F : FactorData A) (S : Submonoid A)
variable (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]

/-- The submodule localization is the actual extension of the ideal. -/
theorem idealLocalized_eq (I : Ideal A) :
    I.localized' B S (Algebra.linearMap A B) = I.map (algebraMap A B) := by
  rw [Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]

def extendedIdealEquiv (I : Ideal A) :
    I.localized' B S (Algebra.linearMap A B) ≃ₗ[B] I.map (algebraMap A B) :=
  LinearEquiv.ofEq _ _ (idealLocalized_eq S B I)

/-- The original element maps to its literal image in the extended ideal. -/
def extendedIdealMap (I : Ideal A) : I →ₗ[A] I.map (algebraMap A B) :=
  ((extendedIdealEquiv S B I).restrictScalars A).toLinearMap.comp
    (I.toLocalized' B S (Algebra.linearMap A B))

theorem extendedIdealMap_val (I : Ideal A) (x : I) :
    (extendedIdealMap S B I x : B) = algebraMap A B (x : A) := rfl

instance extendedIdealMap_isLocalized (I : Ideal A) :
    IsLocalizedModule S (extendedIdealMap S B I) :=
  IsLocalizedModule.of_linearEquiv S
    (I.toLocalized' B S (Algebra.linearMap A B))
    ((extendedIdealEquiv S B I).restrictScalars A)

/-- This is an equivalence over the original ring, with the actual
extended ideal as its target. -/
def extendedIdealCanonicalEquiv (I : Ideal A) :
    LocalizedModule S I ≃ₗ[A] I.map (algebraMap A B) :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S I)
    (extendedIdealMap S B I)

theorem extendedIdealCanonicalEquiv_original (I : Ideal A) (x : I) :
    extendedIdealCanonicalEquiv S B I (LocalizedModule.mkLinearMap S I x) =
      extendedIdealMap S B I x :=
  IsLocalizedModule.linearEquiv_apply S _ _ x

theorem extendedLeftMap_eq_localizedLeft (x : F.leftIdeal) :
    extendedIdealMap S B F.leftIdeal x = localizedLeft F S B x := by
  apply Subtype.ext
  rfl

/-- The finite-product map uses the original coefficient homomorphism
on every one of the three matrix coordinates. -/
def coordinateMap : (Fin 3 → A) →ₗ[A] (Fin 3 → B) :=
  LinearMap.pi fun i => (Algebra.linearMap A B).comp (LinearMap.proj i)

theorem coordinateMap_apply (v : Fin 3 → A) (a : Fin 3) :
    coordinateMap B v a = algebraMap A B (v a) := rfl

instance coordinateMap_isLocalized :
    IsLocalizedModule S (coordinateMap (A := A) B) := by
  unfold coordinateMap
  infer_instance

/-- Localization of the original matrix operator is the actual mapped
matrix operator, with its correct localized coefficient linearity. -/
theorem localizedMatrix_eq :
    (IsLocalizedModule.map S (coordinateMap B) (coordinateMap B)
      F.matrix.mulVecLin).extendScalarsOfIsLocalization S B =
      (localizedFactorData F S B).matrix.mulVecLin := by
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext S (coordinateMap B) (coordinateMap B)
  apply LinearMap.ext
  intro v
  funext a
  change IsLocalizedModule.map S (coordinateMap B) (coordinateMap B) F.matrix.mulVecLin
      (coordinateMap B v) a =
    (localizedFactorData F S B).matrix.mulVecLin (coordinateMap B v) a
  rw [IsLocalizedModule.map_apply]
  change algebraMap A B (∑ b : Fin 3, F.matrix a b * v b) =
    ∑ b : Fin 3, algebraMap A B (F.matrix a b) * algebraMap A B (v b)
  simp only [map_sum, map_mul]

/-- The localized original range is the literal image of the mapped matrix. -/
theorem imageLocalized_eq :
    (Regrading.Image F).localized' B S (coordinateMap B) =
      Regrading.Image (localizedFactorData F S B) := by
  change (LinearMap.range F.matrix.mulVecLin).localized' B S (coordinateMap B) = _
  rw [LinearMap.localized'_range_eq_range_localizedMap B S
    (coordinateMap B) (coordinateMap B) F.matrix.mulVecLin]
  rw [localizedMatrix_eq]

def imageLocalizedEquiv :
    (Regrading.Image F).localized' B S (coordinateMap B) ≃ₗ[B]
      Regrading.Image (localizedFactorData F S B) :=
  LinearEquiv.ofEq _ _ (imageLocalized_eq F S B)

/-- The literal image map, now as a linear map over the original ring. -/
def imageLocalizationMap :
    Regrading.Image F →ₗ[A] Regrading.Image (localizedFactorData F S B) :=
  ((imageLocalizedEquiv F S B).restrictScalars A).toLinearMap.comp
    ((Regrading.Image F).toLocalized' B S (coordinateMap B))

theorem imageLocalizationMap_apply (z : Regrading.Image F) (a : Fin 3) :
    (imageLocalizationMap F S B z).val a = algebraMap A B (z.val a) := rfl

theorem imageLocalizationMap_eq_localizedImage (z : Regrading.Image F) :
    imageLocalizationMap F S B z = localizedImage F S B z := by
  apply Subtype.ext
  funext a
  rfl

instance imageLocalizationMap_isLocalized :
    IsLocalizedModule S (imageLocalizationMap F S B) :=
  IsLocalizedModule.of_linearEquiv S
    ((Regrading.Image F).toLocalized' B S (coordinateMap B))
    ((imageLocalizedEquiv F S B).restrictScalars A)

/-- Canonical module localization agrees with the actual mapped image.
The scalar ring of this equivalence is the original ring A. -/
def imageCanonicalEquiv :
    LocalizedModule S (Regrading.Image F) ≃ₗ[A]
      Regrading.Image (localizedFactorData F S B) :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (Regrading.Image F))
    (imageLocalizationMap F S B)

theorem imageCanonicalEquiv_original (z : Regrading.Image F) :
    imageCanonicalEquiv F S B (LocalizedModule.mkLinearMap S (Regrading.Image F) z) =
      localizedImage F S B z := by
  rw [imageCanonicalEquiv, IsLocalizedModule.linearEquiv_apply,
    imageLocalizationMap_eq_localizedImage]

#print axioms extendedIdealMap_isLocalized
#print axioms extendedIdealCanonicalEquiv_original
#print axioms coordinateMap_isLocalized
#print axioms localizedMatrix_eq
#print axioms imageLocalizationMap_isLocalized
#print axioms imageCanonicalEquiv_original

end CycleQ2SeedImageLocalizedModules
end
