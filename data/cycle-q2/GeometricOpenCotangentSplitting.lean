import Proposal.GeometricIntrinsicNormal
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Sections of a split sequence over an open immersion

A splitting of the pullback by the open restriction functor acts on
sections of all ambient opens contained in its image. Its section and
retraction satisfy the split identities there.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2OpenCotangentSplitting

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricIntrinsicNormal

private theorem component_restrict {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
    (M N : SheafOfModules.{0} (CycleQ2GeometricDifferentialSheaf.ringSheaf R))
    {U V W : TopologicalSpace.Opens T} (f : LocalLinearHom R M N U)
    (h : V ≤ W) (hW : W ≤ U) (x : M.val.obj (op W)) :
    N.val.map (homOfLE h).op (f.val.app (op (Over.mk (homOfLE hW))) x) =
      f.val.app (op (Over.mk (homOfLE (h.trans hW)))) (M.val.map (homOfLE h).op x) := by
  let a : Over.mk (homOfLE (h.trans hW)) ⟶ Over.mk (homOfLE hW) := Over.homMk (homOfLE h)
  have eq := ConcreteCategory.congr_hom (f.val.naturality a.op) x
  exact eq.symm

private theorem component_eq_top {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
    (M N : SheafOfModules.{0} (CycleQ2GeometricDifferentialSheaf.ringSheaf R))
    {U W : TopologicalSpace.Opens T} (H : LocalLinearHom R M N U) (h : W ≤ U) (x : M.val.obj (op W)) :
    H.val.app (op (Over.mk (homOfLE h))) x = localLinearHomEvaluate R M N W
      (restrictLocalLinearHom R M N (homOfLE h).op H) x :=
  (ConcreteCategory.congr_hom
    (presheafHom_map_app_op_mk_id (F := M.val.presheaf) (G := N.val.presheaf) (homOfLE h) H.val) x).symm

section Transport
variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
  {M N : Y.Modules} (f : M.restrict j ⟶ N.restrict j)

/-- A morphism on an open affine chart acts on every open contained in its image. -/
def sectionMap (W : Y.Opens) (h : W ≤ j.opensRange) : (M.val.obj (op W)) →ₗ[Γ(Y,W)] (N.val.obj (op W)) :=
  let H := (localLinearHomOpenImmersionEquiv j M N).symm f
  { toFun := H.val.app (op (Over.mk (homOfLE h)))
    map_add' := (H.val.app (op (Over.mk (homOfLE h)))).hom.map_add
    map_smul' := H.property (Over.mk (homOfLE h)) }


/-- Evaluation after restricting to the top subopen agrees with the
original local Hom component at that subopen. -/
theorem sectionMap_eq_top (W : Y.Opens) (h : W ≤ j.opensRange) (x : M.val.obj (op W)) :
    sectionMap j f W h x = localLinearHomEvaluate Y.sheaf M N W
      (restrictLocalLinearHom Y.sheaf M N (homOfLE h).op
        ((localLinearHomOpenImmersionEquiv j M N).symm f)) x :=
  component_eq_top Y.sheaf M N ((localLinearHomOpenImmersionEquiv j M N).symm f) h x

theorem sectionMap_image (Z : X.Opens) (hZ : j ''ᵁ Z ≤ j.opensRange) (m : (M.val.obj (op (j ''ᵁ Z)))) :
    sectionMap j f _ hZ m = f.app Z m := by
  let H := (localLinearHomOpenImmersionEquiv j M N).symm f
  have e := localLinearHomOpenImmersionEquiv_app j M N H Z m
  change (localLinearHomOpenImmersionEquiv j M N ((localLinearHomOpenImmersionEquiv j M N).symm f)).val.app (op Z) m = _ at e
  rw [Equiv.apply_symm_apply] at e
  exact e.symm

theorem sectionMap_restrict {W V : Y.Opens} (h : V ≤ W) (hW : W ≤ j.opensRange) (x : (M.val.obj (op W))) :
    N.val.map (homOfLE h).op (sectionMap j f W hW x) =
      sectionMap j f V (h.trans hW) (M.val.map (homOfLE h).op x) :=
  component_restrict Y.sheaf M N ((localLinearHomOpenImmersionEquiv j M N).symm f) h hW x
end Transport

variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
  (S : ShortComplex Y.Modules) (h : (S.map (Scheme.Modules.restrictFunctor j)).Splitting)

theorem split_reduce (W : Y.Opens) (hW : W ≤ j.opensRange) (x : S.X₃.val.obj (op W)) :
    S.g.val.app (op W) (sectionMap (M := S.X₃) (N := S.X₂) j h.s W hW x) = x := by
  obtain ⟨V,rfl⟩ : ∃ V, j ''ᵁ V = W :=
    ⟨j ⁻¹ᵁ W, (j.image_preimage_eq_opensRange_inf W).trans (inf_eq_right.mpr hW)⟩
  have e := sectionMap_image (M := S.X₃) (N := S.X₂) j h.s V (j.image_le_opensRange V) x
  exact (congrArg (S.g.val.app _) e).trans (congrArg (fun k => k.app V x) h.s_g)

theorem split_identity (W : Y.Opens) (hW : W ≤ j.opensRange) (x : S.X₂.val.obj (op W)) :
    S.f.val.app (op W) (sectionMap (M := S.X₂) (N := S.X₁) j h.r W hW x) +
      sectionMap (M := S.X₃) (N := S.X₂) j h.s W hW (S.g.val.app (op W) x) = x := by
  obtain ⟨V,rfl⟩ : ∃ V, j ''ᵁ V = W :=
    ⟨j ⁻¹ᵁ W, (j.image_preimage_eq_opensRange_inf W).trans (inf_eq_right.mpr hW)⟩
  have er := sectionMap_image (M := S.X₂) (N := S.X₁) j h.r V (j.image_le_opensRange V) x
  have es := sectionMap_image (M := S.X₃) (N := S.X₂) j h.s V (j.image_le_opensRange V) (S.g.val.app _ x)
  exact (congrArg₂ (· + ·) (congrArg (S.f.val.app _) er) es).trans
    (congrArg (fun k => k.app V x) h.id)

end CycleQ2OpenCotangentSplitting
end

#print axioms CycleQ2OpenCotangentSplitting.split_identity
