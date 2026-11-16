import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Reconstructing affine quasi-coherent sheaf maps from global sections

The canonical tilde--global-sections counit reconstructs a map from a
quasi-coherent source sheaf and its map on native global sections.
The right triangle identity proves that reconstruction recovers that
specified map. Counit naturality proves uniqueness and compatibility
with existing sheaf maps, identities, and composition.

Only the source must be quasi-coherent for reconstructing a morphism.
Both endpoints must be quasi-coherent for reconstructing an isomorphism.
These generic results do not identify any concrete projective overlap
or discharge its descent and internal-Hom obligations.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedAffineReconstruction

open CategoryTheory Opposite AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- Global sections with their native R-module structure. -/
abbrev globalSections (M : (Spec R).Modules) : ModuleCat R :=
  (moduleSpecΓFunctor (R := R)).obj M

/-- The right triangle identifies the global-section map of the counit. -/
theorem unit_counit (M : (Spec R).Modules) :
    (tilde.isoTop (globalSections M)).hom ≫
      (moduleSpecΓFunctor (R := R)).map M.fromTildeΓ = 𝟙 _ :=
  (tilde.adjunction (R := R)).right_triangle_components M

theorem map_inv_fromTildeΓ (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := R)).map (inv M.fromTildeΓ) =
      (tilde.isoTop (globalSections M)).hom := by
  apply (cancel_mono ((moduleSpecΓFunctor (R := R)).map M.fromTildeΓ)).mp
  calc
    _ = 𝟙 _ := by
      rw [← Functor.map_comp]
      simp
    _ = _ := (unit_counit M).symm

/-- Lift a specified global-section map by the canonical counit. -/
def liftΓHom (M N : (Spec R).Modules) [M.IsQuasicoherent]
    (f : globalSections M ⟶ globalSections N) : M ⟶ N := by
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact inv M.fromTildeΓ ≫ (tilde.functor R).map f ≫ N.fromTildeΓ

/-- Reconstruction recovers exactly the supplied native global-section map. -/
theorem map_liftΓHom (M N : (Spec R).Modules) [M.IsQuasicoherent]
    (f : globalSections M ⟶ globalSections N) :
    (moduleSpecΓFunctor (R := R)).map (liftΓHom M N f) = f := by
  have hnat : (tilde.isoTop (globalSections M)).hom ≫
      (moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map f) =
        f ≫ (tilde.isoTop (globalSections N)).hom :=
    tilde.toOpen_map_app f ⊤
  unfold liftΓHom
  rw [Functor.map_comp, Functor.map_comp, map_inv_fromTildeΓ,
    ← Category.assoc, hnat, Category.assoc, unit_counit, Category.comp_id]

/-- Maps with quasi-coherent source are determined by their native global sections. -/
theorem hom_ext_of_globalSections {M N : (Spec R).Modules} [M.IsQuasicoherent]
    {f g : M ⟶ N}
    (h : (moduleSpecΓFunctor (R := R)).map f =
      (moduleSpecΓFunctor (R := R)).map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  calc
    M.fromTildeΓ ≫ f =
        (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫ N.fromTildeΓ :=
      ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f).symm
    _ = (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map g) ≫
        N.fromTildeΓ := by rw [h]
    _ = M.fromTildeΓ ≫ g :=
      (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality g

/-- Reconstructing the global sections of an existing sheaf map returns that map. -/
theorem liftΓHom_map (M N : (Spec R).Modules) [M.IsQuasicoherent] (f : M ⟶ N) :
    liftΓHom M N ((moduleSpecΓFunctor (R := R)).map f) = f := by
  apply hom_ext_of_globalSections
  exact map_liftΓHom M N _

theorem liftΓHom_id (M : (Spec R).Modules) [M.IsQuasicoherent] :
    liftΓHom M M (𝟙 (globalSections M)) = 𝟙 M := by
  apply hom_ext_of_globalSections
  rw [map_liftΓHom, CategoryTheory.Functor.map_id]

theorem liftΓHom_comp (M N P : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : globalSections M ⟶ globalSections N)
    (g : globalSections N ⟶ globalSections P) :
    liftΓHom M P (f ≫ g) = liftΓHom M N f ≫ liftΓHom N P g := by
  apply hom_ext_of_globalSections
  simp only [Functor.map_comp, map_liftΓHom]

/-- Lift an isomorphism of native global-section modules to a sheaf isomorphism. -/
def liftΓIso (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : globalSections M ≅ globalSections N) : M ≅ N := by
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  letI : IsIso N.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) N
  exact (asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e ≪≫ asIso N.fromTildeΓ

theorem liftΓIso_hom (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : globalSections M ≅ globalSections N) :
    (liftΓIso M N e).hom = liftΓHom M N e.hom := rfl

theorem map_liftΓIso (M N : (Spec R).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : globalSections M ≅ globalSections N) :
    (moduleSpecΓFunctor (R := R)).mapIso (liftΓIso M N e) = e := by
  apply Iso.ext
  exact map_liftΓHom M N e.hom

/-- Compare a quasi-coherent sheaf with the associated sheaf of any
specified module model for its native global sections. -/
def comparisonIso (M : (Spec R).Modules) [M.IsQuasicoherent]
    {E : ModuleCat R} (e : globalSections M ≅ E) : M ≅ tilde E :=
  (asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e

/-- A square of native global-section maps lifts to the entire sheaf square. -/
theorem comparisonIso_naturality {M Q : (Spec R).Modules}
    [M.IsQuasicoherent] [Q.IsQuasicoherent] {E F : ModuleCat R}
    (φ : M ⟶ Q) (eM : globalSections M ≅ E) (eQ : globalSections Q ≅ F)
    (h : E ⟶ F)
    (H : (moduleSpecΓFunctor (R := R)).map φ ≫ eQ.hom = eM.hom ≫ h) :
    φ ≫ (comparisonIso Q eQ).hom =
      (comparisonIso M eM).hom ≫ (tilde.functor R).map h := by
  have hnat : (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ) ≫
      Q.fromTildeΓ = M.fromTildeΓ ≫ φ :=
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  apply (cancel_epi M.fromTildeΓ).mp
  change M.fromTildeΓ ≫ (φ ≫ (inv Q.fromTildeΓ ≫ (tilde.functor R).map eQ.hom)) =
    M.fromTildeΓ ≫ ((inv M.fromTildeΓ ≫ (tilde.functor R).map eM.hom) ≫
      (tilde.functor R).map h)
  rw [← Category.assoc M.fromTildeΓ φ, ← hnat]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  simpa only [Functor.map_comp] using congrArg (fun k => (tilde.functor R).map k) H

#print axioms map_liftΓHom
#print axioms hom_ext_of_globalSections
#print axioms liftΓHom_map
#print axioms liftΓHom_comp
#print axioms map_liftΓIso
#print axioms comparisonIso_naturality

end CycleQ2SeedAffineReconstruction
end
