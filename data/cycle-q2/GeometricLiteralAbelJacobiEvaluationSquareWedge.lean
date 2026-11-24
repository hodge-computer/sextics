import Proposal.GeometricLiteralAbelJacobiEvaluationChartTransport
import Proposal.GeometricLiteralAbelJacobiEvaluationWedge

/-!
# Coordinates of tangent evaluation on a commutative chart square

The time derivative on an affine thick chart evaluates the pullback
of each exact wedge. Transport through the reduction square identifies
the two residual functions with restrictions on the original curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationSquareWedge

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiEvaluationWedge CycleQ2LiteralAbelJacobiEvaluationChartTransport
  CycleQ2ExteriorPullComposition

variable {X Y : Scheme.{0}} {B A : Type} [CommRing B] [CommRing A]
  [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A]
  (j : Spec (CommRingCat.of B) ⟶ Y) (k : Spec (CommRingCat.of A) ⟶ X) (r : X ⟶ Y)
  (e : k ≫ r = reduction B A ≫ j) (c : ℂ →+* Γ(Y,⊤)) (hc : compatible j (affineCoefficient B) c)
  (v : Derivation ℂ B A) (W : Y.Opens)

local instance affineSectionModule (O : (Spec (CommRingCat.of A)).Opens) :
    Module Γ(Spec (CommRingCat.of A),O) ((affineDifferentialSheaf A).val.obj (op O)) :=
  ((affineDifferentialSheaf A).val.obj (op O)).isModule

private abbrev timesD (O : (Spec (CommRingCat.of A)).Opens)
    (a b : Γ(Spec (CommRingCat.of A),O)) : (affineDifferentialSheaf A).val.obj (op O) :=
  @SMul.smul _ _ (affineSectionModule (A := A) O).toSMul a
    ((affineUniversalDifferential A).d (X := op O) b)

abbrev coefficient (x : Γ(Y,W)) :=
  (Spec (CommRingCat.of A)).presheaf.map (eqToHom (square_preimage e W)).op (velocityOn v (j ⁻¹ᵁ W) (j.app W x))

abbrev seedValue (x : Γ(Y,W)) := k.app (r ⁻¹ᵁ W) (r.app W x)

theorem square_wedge (a : Fin 2 → Γ(Y,W)) :
    ((Scheme.Modules.pushforwardCongr e.symm).hom.app (affineDifferentialSheaf A)).val.app (op W)
      ((evaluation v).val.app (op (j ⁻¹ᵁ W))
        ((schemeExteriorPull j (affineCoefficient B) c hc 2).val.app (op W) (exactWedge Y c W a))) =
      timesD (k ⁻¹ᵁ r ⁻¹ᵁ W) (coefficient j k r e v W (a 0)) (seedValue k r W (a 1)) -
      timesD (k ⁻¹ᵁ r ⁻¹ᵁ W) (coefficient j k r e v W (a 1)) (seedValue k r W (a 0)) := by
  let u := square_preimage e W
  let m := (affineDifferentialSheaf A).val.map (eqToHom u).op
  refine (pushforwardCongr_apply e.symm W (affineDifferentialSheaf A) _).trans ?_
  refine (congrArg (fun ω => m ((evaluation v).val.app (op (j ⁻¹ᵁ W)) ω))
    (pull_exactWedge j (affineCoefficient B) c hc W a)).trans ?_
  refine (congrArg m (evaluation_exactWedge v (j ⁻¹ᵁ W) (fun p => j.app W (a p)))).trans ?_
  refine (differential_expression (X := Spec (CommRingCat.of A)) u (affineCoefficient A) _ _ _ _).trans ?_
  rw [square_app e W (a 0), square_app e W (a 1)]
  rfl

end CycleQ2LiteralAbelJacobiEvaluationSquareWedge
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationSquareWedge.square_wedge
