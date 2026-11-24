import Proposal.GeometricLiteralCotangentEpsilonComparison
import Proposal.GeometricSurfaceResidueFunctoriality

/-!
# The epsilon inclusion as a morphism on each native chart

The unit of the structure-module pullback corresponds to the original
global section one. Its image determines a morphism out of the pullback.
On an affine chart this identifies the pullback of the epsilon inclusion
with the tilde of the native tensor inclusion.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentEpsilonMap

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralCotangentEpsilonComparison CycleQ2LiteralCotangentEpsilon
  CycleQ2SurfacePullbackFrame CycleQ2LiteralAffineCotangent CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeCotangent

variable {X Y : Scheme.{0}}

/-- A morphism from the structure sheaf is determined by the image of one
on the entire scheme. -/
theorem structureUnit_hom_ext {M : X.Modules} (u v : structureModule X ⟶ M)
    (h : onTop u (1 : Γ(X, ⊤)) = onTop v (1 : Γ(X, ⊤))) : u = v := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let i : op (⊤ : X.Opens) ⟶ V := (homOfLE (show V.unop ≤ ⊤ from le_top)).op
  exact ((M.unitHomEquiv u).property i).symm.trans
    ((congrArg (M.val.map i) h).trans ((M.unitHomEquiv v).property i))

theorem pulledUnit_hom_ext (f : X ⟶ Y) {M : X.Modules}
    (u v : (Scheme.Modules.pullback f).obj (structureModule Y) ⟶ M)
    (h : onTop u (pullTop f (structureModule Y) (1 : Γ(Y, ⊤))) =
      onTop v (pullTop f (structureModule Y) (1 : Γ(Y, ⊤)))) : u = v := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply structureUnit_hom_ext
  exact h

theorem pulledUnitIso_one (f : X ⟶ Y) :
    onTop (pullbackUnitIso f).hom (pullTop f (structureModule Y) (1 : Γ(Y, ⊤))) =
      (1 : Γ(X, ⊤)) := by
  have h := pullbackUnitIso_unit f
  exact (congrArg (fun u => u.val.app (op (⊤ : Y.Opens)) (1 : Γ(Y, ⊤))) h).trans
    (map_one f.appTop.hom)

theorem tildeSelf_one (R : CommRingCat.{0}) :
    onTop (tildeSelf (R := R)).inv (1 : Γ(Spec R, ⊤)) =
      tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R) := by
  change (1 : Γ(Spec R, ⊤)) = algebraMap R Γ(Spec R, ⊤) 1
  exact (map_one _).symm

def affineUnitIso {R : CommRingCat.{0}} (f : Spec R ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ tilde (ModuleCat.of R R) :=
  pullbackUnitIso f ≪≫ (tildeSelf (R := R)).symm

theorem affineUnitIso_one {R : CommRingCat.{0}} (f : Spec R ⟶ Y) :
    onTop (affineUnitIso f).hom (pullTop f (structureModule Y) (1 : Γ(Y, ⊤))) =
      tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R) := by
  change onTop ((pullbackUnitIso f).hom ≫ (tildeSelf (R := R)).inv) _ = _
  rw [onTop_comp, pulledUnitIso_one, tildeSelf_one]

theorem affineUnit_comparison {R : CommRingCat.{0}} (f : Spec R ⟶ Y)
    {M : Y.Modules} {N : ModuleCat R} (u : structureModule Y ⟶ M)
    (v : ModuleCat.of R R ⟶ N) (e : (Scheme.Modules.pullback f).obj M ≅ tilde N)
    (h : onTop e.hom (pullTop f M (onTop u (1 : Γ(Y, ⊤)))) =
      tilde.toOpen N ⊤ (v (1 : R))) :
    (affineUnitIso f).hom ≫ tilde.map v = (Scheme.Modules.pullback f).map u ≫ e.hom := by
  apply pulledUnit_hom_ext
  rw [onTop_comp, onTop_comp, affineUnitIso_one, pullTop_map, h]
  have hv := ConcreteCategory.congr_hom (C := ModuleCat R) (X := ModuleCat.of R R)
    (tilde.toOpen_map_app (R := R) v ⊤) (show ModuleCat.of R R from (1 : R))
  exact hv

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

abbrev nativeUnitIso (s : Finset Vertex) (hs : s.Nonempty) :=
  affineUnitIso (closedAffineMap s hs)

theorem nativeUnitIso_one (s : Finset Vertex) (hs : s.Nonempty) :
    onTop (nativeUnitIso s hs).hom
        (pullTop (closedAffineMap s hs) (structureModule ClosedSurface) (1 : Γ(ClosedSurface, ⊤))) =
      tilde.toOpen (R := CommRingCat.of (ClosedRing s))
        (ModuleCat.of (ClosedRing s) (ClosedRing s)) ⊤ (1 : ClosedRing s) :=
  affineUnitIso_one (closedAffineMap s hs)

theorem nativeCotangentEpsilon_comm (s : Finset Vertex) (hs : s.Nonempty) :
    (nativeUnitIso s hs).hom ≫ tilde.map (ModuleCat.ofHom (nativeEpsilonInclusion s)) =
      (Scheme.Modules.pullback (closedAffineMap s hs)).map epsilonInclusion ≫
        (nativeCotangentIso s hs).hom := by
  apply affineUnit_comparison (closedAffineMap s hs) epsilonInclusion
    (ModuleCat.ofHom (nativeEpsilonInclusion s)) (nativeCotangentIso s hs)
  exact (congrArg (fun x => onTop (nativeCotangentIso s hs).hom
    (pullTop (closedAffineMap s hs) restrictedCotangentSheaf x))
      epsilonInclusion_global_one).trans (nativeCotangentIso_epsilon s hs)

end CycleQ2LiteralCotangentEpsilonMap

end

#print axioms CycleQ2LiteralCotangentEpsilonMap.nativeCotangentEpsilon_comm
