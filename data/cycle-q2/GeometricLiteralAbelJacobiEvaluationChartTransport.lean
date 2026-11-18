import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricOpenDifferentialSheaf

/-!
# Transport of differential coefficients on the Cartesian reduction chart

The two paths from an affine seed chart to the first-order family are
equal as scheme maps. Their inverse images of each open give the same
restriction of regular functions and ordinary one-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationChartTransport

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2FirstOrderCurveSeedFiber

section Morphisms
variable {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens)

/-- View a function on the first inverse image on the second inverse image. -/
theorem app_transport (x : Γ(Y,U)) :
    X.presheaf.map (eqToHom (congrArg (fun p : X ⟶ Y => p ⁻¹ᵁ U) e).symm).op (f.app U x) =
      g.app U x := by subst g; simp

variable (M : X.Modules)

theorem pushforwardCongr_apply (x : M.val.obj (op (f ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforwardCongr e).hom.app M).val.app (op U) x =
      M.val.map (eqToHom (congrArg (fun p : X ⟶ Y => p ⁻¹ᵁ U) e).symm).op x := by
  subst g
  change ((Scheme.Modules.pushforwardCongr rfl).hom.app M).app U x = _
  simp [Scheme.Modules.pushforwardCongr_hom_app_app]

theorem differential_expression {V W : X.Opens} (h : W = V) (c : ℂ →+* Γ(X,⊤))
    (a b p q : Γ(X,V)) :
    (differentialSheaf X.sheaf c).val.map (eqToHom h).op
      (a • (universalDifferential X.sheaf c).d b - p • (universalDifferential X.sheaf c).d q) =
      X.presheaf.map (eqToHom h).op a • (universalDifferential X.sheaf c).d (X.presheaf.map (eqToHom h).op b) -
      X.presheaf.map (eqToHom h).op p • (universalDifferential X.sheaf c).d (X.presheaf.map (eqToHom h).op q) := by
  subst W
  simp

end Morphisms

section Square
variable {D C B X : Scheme.{0}} {k : D ⟶ C} {r : C ⟶ X} {s : D ⟶ B} {j : B ⟶ X}
  (e : k ≫ r = s ≫ j) (W : X.Opens)

include e in
theorem square_preimage : k ⁻¹ᵁ r ⁻¹ᵁ W = s ⁻¹ᵁ j ⁻¹ᵁ W :=
  congrArg (fun p : D ⟶ X => p ⁻¹ᵁ W) e

theorem square_app (a : Γ(X,W)) :
    D.presheaf.map (eqToHom (square_preimage e W)).op (s.app (j ⁻¹ᵁ W) (j.app W a)) =
      k.app (r ⁻¹ᵁ W) (r.app W a) :=
  app_transport e.symm W a

end Square

abbrev chart_preimage (t : Fin 3 → ℂ) (i : Fin 4) := square_preimage (seedChart_to_germ t i)
abbrev reduction_app (t : Fin 3 → ℂ) (i : Fin 4) := square_app (seedChart_to_germ t i)

end CycleQ2LiteralAbelJacobiEvaluationChartTransport
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationChartTransport.reduction_app
