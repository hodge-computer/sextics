import Proposal.GeometricOpenDifferentialSheaf
import Proposal.GeometricLiteralAbelJacobiEvaluationLocal

/-!
# Differential sections inside the range of an open immersion

Pullback of ordinary one-forms through an open immersion is bijective on
every subopen of its image, with the section map induced by the universal
differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2OpenDifferentialSections
open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2GeometricOpenDifferentialSheaf CycleQ2LiteralAbelJacobiEvaluationLocal

variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
  (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤)) (hc : ∀ (U : Y.Opens) (c : ℂ),
    j.app U (coefficientOn Y.sheaf cY U c) = coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c)

theorem pull_bijective (W : Y.Opens) (hW : W ≤ j.opensRange) :
    Function.Bijective ((schemeDifferentialMap j cX cY hc).val.app (op W)) := by
  let M := differentialSheaf Y.sheaf cY
  let N := differentialSheaf X.sheaf cX
  let e := openDifferentialIso j cX cY hc
  have h : ((Scheme.Modules.restrictAdjunction j).unit.app M) ≫ (Scheme.Modules.pushforward j).map e.hom =
      schemeDifferentialMap j cX cY hc :=
    ((Scheme.Modules.restrictAdjunction j).homEquiv_unit M N e.hom).symm.trans
      (openDifferentialIso_adjunct j cX cY hc)
  rw [← h]
  exact (((SheafOfModules.evaluation _ (op W)).mapIso
    ((Scheme.Modules.pushforward j).mapIso e)).toLinearEquiv.bijective).comp
    (restrictTarget_bijective (𝟙 Y) j M W hW)

end CycleQ2OpenDifferentialSections
end

#print axioms CycleQ2OpenDifferentialSections.pull_bijective
