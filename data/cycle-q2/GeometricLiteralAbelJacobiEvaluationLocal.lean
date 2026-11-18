import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricModuleLocalIso

/-!
# Recovering a curve differential from its affine chart

If a subopen of the first-order family meets its closed fibre only inside
one seed chart, restriction to that chart loses no information about a
differential on the fibre. The inverse of the actual restriction gives the
local sheaf map obtained by computing time evaluation in affine coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationLocal

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricModuleLocalIso

variable {X Y D : Scheme.{0}} (r : Y ⟶ X) (k : D ⟶ Y) [IsOpenImmersion k]
  (N : Y.Modules)

abbrev target := (Scheme.Modules.pushforward r).obj N
abbrev chartTarget := (Scheme.Modules.pushforward r).obj
  ((Scheme.Modules.pushforward k).obj (N.restrict k))

def restrictTarget : target r N ⟶ chartTarget r k N :=
  (Scheme.Modules.pushforward r).map ((Scheme.Modules.restrictAdjunction k).unit.app N)

theorem restrictTarget_bijective (W : X.Opens) (h : r ⁻¹ᵁ W ≤ k.opensRange) :
    Function.Bijective ((restrictTarget r k N).val.app (op W)) := by
  have he : k ''ᵁ k ⁻¹ᵁ (r ⁻¹ᵁ W) = r ⁻¹ᵁ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr h]
  have : IsIso (homOfLE (k.image_preimage_le (r ⁻¹ᵁ W))) := by
    exact ⟨⟨homOfLE he.ge, by subsingleton, by subsingleton⟩⟩
  change Function.Bijective (N.presheaf.map (homOfLE (k.image_preimage_le (r ⁻¹ᵁ W))).op)
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

def restrictEquiv (W : X.Opens) (h : r ⁻¹ᵁ W ≤ k.opensRange) :=
  LinearEquiv.ofBijective ((restrictTarget r k N).val.app (op W)).hom
    (restrictTarget_bijective r k N W h)

variable (M : X.Modules) (f : M ⟶ chartTarget r k N) (U : X.Opens) (hU : r ⁻¹ᵁ U ≤ k.opensRange)

private def component (W : X.Opens) (hW : W ≤ U) :
    M.val.obj (op W) →ₗ[Γ(X,W)] (target r N).val.obj (op W) :=
  (restrictEquiv r k N W ((r.preimage_mono hW).trans hU)).symm.toLinearMap.comp
    (f.val.app (op W)).hom

theorem restrict_component (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    (restrictTarget r k N).val.app (op W) (component r k N M f U hU W hW x) =
      f.val.app (op W) x :=
  (restrictEquiv r k N W ((r.preimage_mono hW).trans hU)).apply_symm_apply _

/-- Evaluation in a seed chart, with values returned to the actual curve sheaf. -/
def localMap : LocalLinearHom X.sheaf M (target r N) U :=
  ⟨{
    app V := AddCommGrpCat.ofHom (component r k N M f U hU V.unop.left V.unop.hom.le).toAddMonoidHom
    naturality {V W} g := by
      apply ConcreteCategory.hom_ext
      intro x
      apply (restrictTarget_bijective r k N W.unop.left ((r.preimage_mono W.unop.hom.le).trans hU)).1
      change (restrictTarget r k N).val.app _
        (component r k N M f U hU W.unop.left W.unop.hom.le (M.val.map g.unop.left.op x)) =
        (restrictTarget r k N).val.app _
          ((target r N).val.map g.unop.left.op (component r k N M f U hU V.unop.left V.unop.hom.le x))
      rw [restrict_component, PresheafOfModules.naturality_apply (restrictTarget r k N).val
        g.unop.left.op _, restrict_component]
      exact PresheafOfModules.naturality_apply f.val _ x
  }, fun V c x => (component r k N M f U hU V.left V.hom.le).map_smul c x⟩

theorem localMap_restrict (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    (restrictTarget r k N).val.app (op W)
      ((localMap r k N M f U hU).val.app (op (Over.mk (homOfLE hW))) x) =
        f.val.app (op W) x :=
  restrict_component r k N M f U hU W hW x

end CycleQ2LiteralAbelJacobiEvaluationLocal
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationLocal.localMap_restrict
