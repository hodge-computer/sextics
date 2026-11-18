import Proposal.GeometricFirstOrderCurveCharts
import Proposal.GeometricLiteralAbelJacobiMovingNormal
import Proposal.GeometricAffineDifferentialSheaf

/-!
# The epsilon function on the first-order curve and its affine charts

The parameter epsilon of the dual-number base gives a regular function on
every open of the first-order curve. Its restriction to each tensor chart
is the image of the same parameter under the chart's coefficient map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationVelocityEpsilon

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GeometricAffineDifferentialSheaf CycleQ2FirstOrderCurve
  CycleQ2FirstOrderCurveCharts CycleQ2LiteralAbelJacobiMovingNormal
open scoped DualNumber

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

/-- Pull a coefficient from an affine base to a section on a source open. -/
def coefficientSection (p : X ⟶ Spec (CommRingCat.of K)) (W : X.Opens) (c : K) : Γ(X, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫
    X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op) c

theorem coefficientSection_restrict (p : X ⟶ Spec (CommRingCat.of K))
    (W U : X.Opens) (h : U ≤ W) (c : K) :
    X.presheaf.map (homOfLE h).op (coefficientSection p W c) = coefficientSection p U c := by
  let a := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  change X.presheaf.map (homOfLE h).op
    (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  all_goals rfl

private theorem coefficientSection_app (j : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K))
    (W : X.Opens) (c : K) :
    j.app W (coefficientSection p W c) = coefficientSection (j ≫ p) (j ⁻¹ᵁ W) c := by
  let a := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  exact congrArg (fun g => g a) (j.naturality (homOfLE (show W ≤ ⊤ from le_top)).op)

theorem coefficientSection_chart {A : Type} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of K)) (f : K →+* A) (hj : j ≫ p = Spec.map (CommRingCat.ofHom f))
    (W : X.Opens) (c : K) :
    j.app W (coefficientSection p W c) =
      algebraMap A (AffineSections A (j ⁻¹ᵁ W)) (f c) := by
  rw [coefficientSection_app, hj]
  unfold coefficientSection
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  all_goals rfl

attribute [local instance] CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul

abbrev epsilonSection (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens) : Γ(firstOrderCurve t, W) :=
  coefficientSection (firstOrderCurveToBase t) W (ε : ℂ[ε])

/-- The same epsilon generator on any two nested opens of the germ. -/
theorem epsilonSection_restrict (t : Fin 3 → ℂ) (W U : (firstOrderCurve t).Opens) (h : U ≤ W) :
    (firstOrderCurve t).presheaf.map (homOfLE h).op (epsilonSection t W) = epsilonSection t U :=
  coefficientSection_restrict (firstOrderCurveToBase t) W U h ε

private abbrev affineScalar (R : Type) [CommRing R] (U : (Spec (CommRingCat.of R)).Opens) :
    R →+* AffineSections R U :=
  algebraMap R (AffineSections R U)

/-- On every subopen of any chart, pullback of the parameter function is
the restriction of the tensor algebra's actual dual-number coefficient. -/
theorem epsilonSection_chart (t : Fin 3 → ℂ) (i : Fin 4) (W : (firstOrderCurve t).Opens) :
    (firstOrderChartToCurve t i).app W (epsilonSection t W) =
      affineScalar (B t i) ((firstOrderChartToCurve t i) ⁻¹ᵁ W)
        (algebraMap ℂ[ε] (B t i) ε) :=
  coefficientSection_chart (A := B t i) (K := ℂ[ε]) (firstOrderChartToCurve t i)
    (firstOrderCurveToBase t) (algebraMap ℂ[ε] (B t i)) (firstOrderChartToCurve_overBase t i) W ε

end CycleQ2LiteralAbelJacobiEvaluationVelocityEpsilon
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationVelocityEpsilon.epsilonSection_restrict
#print axioms CycleQ2LiteralAbelJacobiEvaluationVelocityEpsilon.epsilonSection_chart
