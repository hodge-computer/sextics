import Proposal.GeometricSeedAffineHomEvaluation

/-!
# The canonical comparison with the actual orbit-ideal internal Hom

The algebraic orbit dual has a canonical morphism of associated sheaves
to the genuine internal-Hom sheaf. It is the tilde image of the proved
global-section identification, followed by the tilde--Gamma counit.
This construction imposes no quasi-coherence hypothesis on its target.

On every open, an original dual element is sent to the restriction of
its actual global sheaf morphism. At the whole affine chart the map
retains evaluation on every original orbit-ideal element. Invertibility
of this concrete comparison is equivalent to the precise remaining
localization condition on the genuine internal-Hom sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedOrbitHomComparison

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricIntrinsicNormal CycleQ2SeedProjectiveImageChart
open CycleQ2SeedAffineHomEvaluation

private theorem tilde_counit_toOpen {A : CommRingCat.{0}} {P : ModuleCat A}
    (N : (Spec A).Modules)
    (f : P ⟶ (moduleSpecΓFunctor (R := A)).obj N) (U : (Spec A).Opens) :
    tilde.toOpen (R := A) P U ≫
        ((modulesSpecToSheaf (R := A)).map
          ((tilde.functor A).map f ≫ Scheme.Modules.fromTildeΓ (R := A) N)).1.app (op U) =
      f ≫ ((modulesSpecToSheaf (R := A)).obj N).1.map (homOfLE le_top).op := by
  rw [CategoryTheory.Functor.map_comp]
  change tilde.toOpen (R := A) P U ≫
      ((modulesSpecToSheaf (R := A)).map (tilde.map f)).1.app (op U) ≫
      ((modulesSpecToSheaf (R := A)).map N.fromTildeΓ).1.app (op U) = _
  rw [tilde.toOpen_map_app_assoc]
  exact congrArg (fun k => f ≫ k) (Scheme.Modules.toOpen_fromTildeΓ_app (R := A) N U)

/-- The previously proved global functional identification in the native module carrier. -/
def orbitHomGlobalIso (i : Fin 3) :
    ModuleCat.of (AffineRing i) (OrbitDual i) ≅
      (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i) :=
  (orbitHomTopEquiv i).symm.toModuleIso
    (X₁ := ModuleCat.of (AffineRing i) (OrbitDual i))
    (X₂ := (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i))

/-- The unconditional sheaf morphism induced by the actual normalized
global orbit-dual functional and the canonical counit. -/
def orbitHomComparison (i : Fin 3) : affineOrbitDualSheaf i ⟶ orbitHomSheaf i :=
  (tilde.functor (CommRingCat.of (AffineRing i))).map
      (orbitHomGlobalIso i).hom ≫
    Scheme.Modules.fromTildeΓ (R := CommRingCat.of (AffineRing i)) (orbitHomSheaf i)

/-- The comparison sends each original dual element to the restriction
of its actual global local-sheaf morphism, on every open. -/
theorem orbitHomComparison_toOpen (i : Fin 3)
    (U : (Spec (CommRingCat.of (AffineRing i))).Opens) :
    tilde.toOpen (R := CommRingCat.of (AffineRing i))
        (ModuleCat.of (AffineRing i) (OrbitDual i)) U ≫
        ((modulesSpecToSheaf (R := CommRingCat.of (AffineRing i))).map
          (orbitHomComparison i)).1.app (op U) =
      (orbitHomGlobalIso i).hom ≫
        ((modulesSpecToSheaf (R := CommRingCat.of (AffineRing i))).obj
          (orbitHomSheaf i)).1.map (homOfLE le_top).op :=
  tilde_counit_toOpen (orbitHomSheaf i) (orbitHomGlobalIso i).hom U

/-- Native global sections recover exactly the previously proved
inverse of orbitHomTopEquiv. -/
theorem orbitHomComparison_top (i : Fin 3) :
    tilde.toOpen (R := CommRingCat.of (AffineRing i))
        (ModuleCat.of (AffineRing i) (OrbitDual i)) ⊤ ≫
        (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).map
          (orbitHomComparison i) =
      (orbitHomGlobalIso i).hom := by
  have h := orbitHomComparison_toOpen i ⊤
  have hi : (homOfLE (show (⊤ : (Spec (CommRingCat.of (AffineRing i))).Opens) ≤ ⊤
      from le_top)).op =
        𝟙 (op (⊤ : (Spec (CommRingCat.of (AffineRing i))).Opens)) :=
    Subsingleton.elim _ _
  have hres : ((modulesSpecToSheaf (R := CommRingCat.of (AffineRing i))).obj
      (orbitHomSheaf i)).1.map (homOfLE le_top).op = 𝟙 _ := by
    rw [hi, CategoryTheory.Functor.map_id]
  exact h.trans ((congrArg (fun k => (orbitHomGlobalIso i).hom ≫ k) hres).trans
    (Category.comp_id _))

theorem orbitHomComparison_top_apply (i : Fin 3) (φ : OrbitDual i) :
    ((moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).map
        (orbitHomComparison i)).hom
      ((tilde.toOpen (R := CommRingCat.of (AffineRing i))
        (ModuleCat.of (AffineRing i) (OrbitDual i)) ⊤).hom φ) =
      (orbitHomTopEquiv i).symm φ :=
  congrArg (fun k : ModuleCat.of (AffineRing i) (OrbitDual i) ⟶
    (moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).obj (orbitHomSheaf i) =>
      k φ) (orbitHomComparison_top i)

/-- The actual comparison evaluates to the original orbit functional,
with the canonical affine section-ring normalization. -/
theorem orbitHomComparison_evaluate (i : Fin 3) (φ : OrbitDual i) (x : OrbitIdeal i) :
    localLinearHomEvaluate (Spec (CommRingCat.of (AffineRing i))).sheaf
        (tilde (R := CommRingCat.of (AffineRing i)) (ModuleCat.of (AffineRing i) (OrbitIdeal i)))
        (structureModule (CommRingCat.of (AffineRing i))) ⊤
        (((moduleSpecΓFunctor (R := CommRingCat.of (AffineRing i))).map
          (orbitHomComparison i)).hom
            ((tilde.toOpen (R := CommRingCat.of (AffineRing i))
              (ModuleCat.of (AffineRing i) (OrbitDual i)) ⊤).hom φ))
        (orbitElementSection i x) =
      (Scheme.ΓSpecIso (CommRingCat.of (AffineRing i))).inv (φ x) := by
  rw [orbitHomComparison_top_apply]
  exact orbitHomTopEquiv_symm_evaluate i φ x

/-- The remaining obligation is exactly localization of the genuine
internal-Hom sheaf. No such localization property is assumed here. -/
theorem orbitHomComparison_isIso_iff_isLocalizing (i : Fin 3) :
    IsIso (orbitHomComparison i) ↔
      IsLocalizing (modulesSpecToSheaf.obj (orbitHomSheaf i)) := by
  unfold orbitHomComparison
  rw [isIso_comp_left_iff, isIso_fromTildeΓ_iff_isLocalizing]

#print axioms orbitHomComparison
#print axioms orbitHomComparison_toOpen
#print axioms orbitHomComparison_top
#print axioms orbitHomComparison_evaluate
#print axioms orbitHomComparison_isIso_iff_isLocalizing

end CycleQ2SeedOrbitHomComparison
end
