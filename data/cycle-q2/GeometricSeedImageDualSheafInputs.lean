import Proposal.GeometricSeedProjectiveImageChart
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Finite presentation and actual sheaf naturality for the seed duality

The original affine chart ring is a quotient of a polynomial ring in four
variables over the complex numbers. Its orbit ideal and matrix image are
therefore finitely presented modules. These are proved instances, not
additional assumptions on the seed geometry.

Finite presentation supplies localization of the actual orbit-ideal dual.
The final theorem is the section naturality of the existing affine sheaf
isomorphism induced by the original image-dual map. Identifying the canonical
localized modules below with the explicit projective-overlap modules is
still required before gluing that comparison globally.

Prepared for fqlx with OpenAI ChatGPT assistance. The geometric route and
remaining protected certificate obligation are recorded in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedImageDualSheafInputs

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart

local instance affineCommRing (i : Fin 3) : CommRing (AffineRing i) := inferInstance
local instance orbitIdealAddCommGroup (i : Fin 3) : AddCommGroup (OrbitIdeal i) := inferInstance
local instance localizedOrbitAddCommGroup (i : Fin 3) (S : Submonoid (AffineRing i)) :
    AddCommGroup (LocalizedModule S (OrbitIdeal i)) := inferInstance
local instance localizedAffineCommRing (i : Fin 3) (S : Submonoid (AffineRing i)) :
    CommRing (Localization S) := inferInstance

instance affineRing_noetherian (i : Fin 3) : IsNoetherianRing (AffineRing i) := by
  infer_instance

instance orbitIdeal_finite (i : Fin 3) :
    Module.Finite (AffineRing i) (OrbitIdeal i) := by
  infer_instance

instance imageModule_finite (i : Fin 3) :
    Module.Finite (AffineRing i) (ImageModule i) := by
  infer_instance

instance orbitIdeal_finitePresentation (i : Fin 3) :
    Module.FinitePresentation (AffineRing i) (OrbitIdeal i) :=
  Module.finitePresentation_of_finite (AffineRing i) (OrbitIdeal i)

instance imageModule_finitePresentation (i : Fin 3) :
    Module.FinitePresentation (AffineRing i) (ImageModule i) :=
  Module.finitePresentation_of_finite (AffineRing i) (ImageModule i)

abbrev LocalizedOrbitDual (i : Fin 3) (S : Submonoid (AffineRing i)) :=
  LocalizedModule S (OrbitIdeal i) →ₗ[Localization S] Localization S

local instance localizedCoefficient_isLocalized (i : Fin 3) (S : Submonoid (AffineRing i)) :
    IsLocalizedModule S (Algebra.linearMap (AffineRing i) (Localization S)) :=
  (isLocalizedModule_iff_isLocalization' S (Localization S)).mpr
    (Localization.isLocalization (M := S))

/-- The canonical extension of the original ideal functional to the
localized ideal, with values in the actual localized coefficient ring. -/
def orbitDualLocalizationMap (i : Fin 3) (S : Submonoid (AffineRing i)) :
    OrbitDual i →ₗ[AffineRing i] LocalizedOrbitDual i S :=
  IsLocalizedModule.mapExtendScalars S
    (LocalizedModule.mkLinearMap S (OrbitIdeal i))
    (Algebra.linearMap (AffineRing i) (Localization S)) (Localization S)

set_option maxHeartbeats 1000000 in
/-- The required Hom-localization hypothesis is discharged for the
original orbit ideal by its proved finite presentation. -/
instance orbitDualLocalizationMap_isLocalized (i : Fin 3) (S : Submonoid (AffineRing i)) :
    IsLocalizedModule S (orbitDualLocalizationMap i S) := by
  unfold orbitDualLocalizationMap
  exact Module.FinitePresentation.isLocalizedModule_mapExtendScalars
    (R := AffineRing i) (M := OrbitIdeal i) (N := AffineRing i)
    (M' := LocalizedModule S (OrbitIdeal i)) (N' := Localization S) S
    (LocalizedModule.mkLinearMap S (OrbitIdeal i))
    (Algebra.linearMap (AffineRing i) (Localization S)) (Localization S)

theorem orbitDualLocalizationMap_original (i : Fin 3) (S : Submonoid (AffineRing i))
    (φ : OrbitDual i) (x : OrbitIdeal i) :
    orbitDualLocalizationMap i S φ (LocalizedModule.mkLinearMap S (OrbitIdeal i) x) =
      algebraMap (AffineRing i) (Localization S) (φ x) := by
  change IsLocalizedModule.map S
      (LocalizedModule.mkLinearMap S (OrbitIdeal i))
      (Algebra.linearMap (AffineRing i) (Localization S)) φ
      (LocalizedModule.mkLinearMap S (OrbitIdeal i) x) = _
  exact IsLocalizedModule.map_apply S _ _ φ x

/-- This equivalence is linear over the original coefficient ring. Its
target consists of functionals linear over the localized coefficient ring. -/
def orbitDualLocalizationEquiv (i : Fin 3) (S : Submonoid (AffineRing i)) :
    LocalizedModule S (OrbitDual i) ≃ₗ[AffineRing i] LocalizedOrbitDual i S :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (OrbitDual i))
    (orbitDualLocalizationMap i S)

theorem orbitDualLocalizationEquiv_original (i : Fin 3) (S : Submonoid (AffineRing i))
    (φ : OrbitDual i) :
    orbitDualLocalizationEquiv i S (LocalizedModule.mkLinearMap S (OrbitDual i) φ) =
      orbitDualLocalizationMap i S φ :=
  IsLocalizedModule.linearEquiv_apply S _ _ φ

/-- The existing affine sheaf isomorphism has the same naturality square
as its original module map, under the actual maps to sheaf sections. -/
theorem affineImageDualIso_section_naturality (i : Fin 3)
    (U : (Spec (CommRingCat.of (AffineRing i))).Opens) :
    tilde.toOpen (R := CommRingCat.of (AffineRing i))
        (ModuleCat.of (AffineRing i) (ImageModule i)) U ≫
        (modulesSpecToSheaf.map (affineImageDualIso i).hom).1.app (op U) =
      (imageDualEquiv i).toModuleIso.hom ≫
        tilde.toOpen (R := CommRingCat.of (AffineRing i))
          (ModuleCat.of (AffineRing i) (OrbitDual i)) U :=
  tilde.toOpen_map_app (R := CommRingCat.of (AffineRing i))
    ((imageDualEquiv i).toModuleIso.hom) U

#print axioms orbitIdeal_finitePresentation
#print axioms imageModule_finitePresentation
#print axioms orbitDualLocalizationMap_isLocalized
#print axioms orbitDualLocalizationEquiv
#print axioms affineImageDualIso_section_naturality

end CycleQ2SeedImageDualSheafInputs
end
