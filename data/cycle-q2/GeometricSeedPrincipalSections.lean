import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Native principal-open sections and specified module localizations

The actual sections of `tilde M` on `D(r)` in `Spec R` are canonically
identified with any specified localization map for `M`. This comparison
intertwines the native section map of `tilde.map` with localization of
the original module map, on every section.

These are principal opens of `Spec R`. Identifying them with projective
overlaps and transporting restricted sheaves remain separate steps.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. The geometric route
and remaining certificate obligation are credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedPrincipalSections

open CategoryTheory Opposite AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The native sections, with the original ring's scalar action supplied
by `modulesSpecToSheaf`. -/
abbrev principalSections (M : ModuleCat.{u} R) (r : R) : ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (PrimeSpectrum.basicOpen r))

section Comparison

variable (M : ModuleCat.{u} R) (r : R)
variable {Mloc : Type u} [AddCommGroup Mloc] [Module R Mloc]
variable (p : M →ₗ[R] Mloc) [IsLocalizedModule.Away r p]

/-- Localization uniqueness compares native sections with the specified
localized module, linearly over the original ring. -/
def sectionsEquiv : principalSections M r ≃ₗ[R] Mloc :=
  IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom p

theorem sectionsEquiv_original (x : M) :
    sectionsEquiv M r p ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x) = p x :=
  IsLocalizedModule.linearEquiv_apply (Submonoid.powers r) _ _ x

end Comparison

variable {M N : ModuleCat.{u} R} (φ : M ⟶ N) (r : R)

/-- The map on native principal-open sections induced by the original map. -/
def sectionsMap : principalSections M r →ₗ[R] principalSections N r :=
  ((modulesSpecToSheaf.map (tilde.map φ)).1.app (op (PrimeSpectrum.basicOpen r))).hom

theorem sectionsMap_original (x : M) :
    sectionsMap φ r ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x) =
      (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom (φ.hom x) := by
  exact congrArg (fun k : M ⟶ principalSections N r => k.hom x)
    (tilde.toOpen_map_app φ (PrimeSpectrum.basicOpen r))

variable {Mloc Nloc : Type u}
variable [AddCommGroup Mloc] [Module R Mloc]
variable [AddCommGroup Nloc] [Module R Nloc]
variable (p : M →ₗ[R] Mloc) (q : N →ₗ[R] Nloc)
variable [IsLocalizedModule.Away r p] [IsLocalizedModule.Away r q]

/-- The localization comparison commutes with the entire native section
map, rather than only its values on original module elements. -/
theorem sectionsEquiv_naturality :
    (sectionsEquiv N r q).toLinearMap.comp (sectionsMap φ r) =
      (IsLocalizedModule.map (Submonoid.powers r) p q φ.hom).comp
        (sectionsEquiv M r p).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom q
  apply LinearMap.ext
  intro x
  change sectionsEquiv N r q
      (sectionsMap φ r ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x)) =
    IsLocalizedModule.map (Submonoid.powers r) p q φ.hom
      (sectionsEquiv M r p ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x))
  simp only [sectionsMap_original, sectionsEquiv_original, IsLocalizedModule.map_apply]

#print axioms sectionsEquiv_original
#print axioms sectionsMap_original
#print axioms sectionsEquiv_naturality

end CycleQ2SeedPrincipalSections
end
