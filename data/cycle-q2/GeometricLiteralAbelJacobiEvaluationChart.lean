import Proposal.GeometricLiteralAbelJacobiEvaluationAffine
import Proposal.GeometricLiteralAbelJacobiEvaluationSeedForms
import Proposal.GeometricLiteralAbelJacobiEvaluationGerm
import Proposal.GeometricLiteralAbelJacobiEvaluationLocal
import Proposal.GeometricLiteralAbelJacobiEvaluationNormalized

/-!
# The mixed differential on each open of the original curve germ

The affine tangent evaluation is transported through the Cartesian seed
and infinitesimal charts. On every subopen of one of the four projective
charts it takes values in the actual Kähler sheaf of the projective seed
curve, whose cohomology carries the residue trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationChart

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2LiteralAbelJacobiEvaluationAffine CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiEvaluationGerm CycleQ2LiteralAbelJacobiEvaluationLocal
  CycleQ2LiteralAbelJacobiEvaluationSeedForms CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralCylinderEvaluation
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2GeometricOpenDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2FirstOrderCurveSeedFiber CycleQ2ExteriorPullComposition
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing
  CycleQ2LiteralCylinderEvaluation.closedRing
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  CycleQ2LiteralCylinderEvaluation.familyComplexSMul
  CycleQ2LiteralCylinderEvaluation.familyComplexModule
  CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2LiteralCylinderEvaluation.familyReductionTower

/-- Write the composite of the two given module maps on the other side of a
commuting square, keeping the two pushforwards separate. -/
private def acrossSquare {D E Y X : Scheme.{0}}
    (a : D ⟶ E) (b : E ⟶ X) (k : D ⟶ Y) (r : Y ⟶ X) (e : k ≫ r = a ≫ b)
    (N : D.Modules) (L : E.Modules) (M : X.Modules)
    (f : L ⟶ (Scheme.Modules.pushforward a).obj N)
    (g : M ⟶ (Scheme.Modules.pushforward b).obj L) :
    M ⟶ (Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward r).obj N :=
  composeIntoPush a b f g ≫ (Scheme.Modules.pushforwardCongr e.symm).hom.app N ≫
    (Scheme.Modules.pushforwardComp k r).inv.app N

private theorem acrossSquare_apply {D E Y X : Scheme.{0}}
    (a : D ⟶ E) (b : E ⟶ X) (k : D ⟶ Y) (r : Y ⟶ X) (e : k ≫ r = a ≫ b)
    (N : D.Modules) (L : E.Modules) (M : X.Modules)
    (f : L ⟶ (Scheme.Modules.pushforward a).obj N)
    (g : M ⟶ (Scheme.Modules.pushforward b).obj L) (W : X.Opens) (x : M.val.obj (op W)) :
    (acrossSquare a b k r e N L M f g).val.app (op W) x =
      ((Scheme.Modules.pushforwardCongr e.symm).hom.app N).val.app (op W)
        (f.val.app (op (b ⁻¹ᵁ W)) (g.val.app (op W) x)) := rfl

section Sections

variable {D Y X : Scheme.{0}} (r : Y ⟶ X) (k : D ⟶ Y) [IsOpenImmersion k]
  (N : Y.Modules) (F : D.Modules) (e : N.restrict k ≅ F)

private abbrev image := Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward r

private def coordinates : target r N ⟶ (image r k).obj F :=
  restrictTarget r k N ≫ (image r k).map e.hom

private theorem coordinates_eq :
    coordinates r k N F e = (Scheme.Modules.pushforward r).map
      ((Scheme.Modules.restrictAdjunction k).unit.app N ≫ (Scheme.Modules.pushforward k).map e.hom) :=
  ((Scheme.Modules.pushforward r).map_comp _ _).symm

local instance nativeSectionModule (S : Scheme.{0}) (G : S.Modules) (U : S.Opens) :
    Module Γ(S,U) (G.val.obj (op U)) := (G.val.obj (op U)).isModule

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coord_smul (W : X.Opens) (a : Γ(Y, r ⁻¹ᵁ W)) (z : N.val.obj (op (r ⁻¹ᵁ W))) :
    (coordinates r k N F e).val.app (op W)
      (@SMul.smul _ _ (nativeSectionModule Y N (r ⁻¹ᵁ W)).toSMul a z) =
      @SMul.smul _ _ (nativeSectionModule D F (k ⁻¹ᵁ (r ⁻¹ᵁ W))).toSMul
        (k.app (r ⁻¹ᵁ W) a) ((coordinates r k N F e).val.app (op W) z) :=
  (CycleQ2LiteralAbelJacobiQPullback.onSections k (M := N) (N := F)
    ((Scheme.Modules.restrictAdjunction k).unit.app N ≫ (Scheme.Modules.pushforward k).map e.hom)
    (r ⁻¹ᵁ W)).map_smulₛₗ a z

private theorem coord_injective (U : X.Opens) (hU : r ⁻¹ᵁ U ≤ k.opensRange)
    (W : X.Opens) (hW : W ≤ U) : Function.Injective ((coordinates r k N F e).val.app (op W)) :=
  (((SheafOfModules.evaluation _ (op W)).mapIso ((image r k).mapIso e)).toLinearEquiv.injective).comp
    (restrictTarget_bijective r k N W ((r.preimage_mono hW).trans hU)).1

private def toTarget (M : X.Modules) (f : M ⟶ (image r k).obj F) : M ⟶ chartTarget r k N :=
  f ≫ (image r k).map e.inv

private theorem coord_localMap (M : X.Modules) (f : M ⟶ (image r k).obj F)
    (U : X.Opens) (hU : r ⁻¹ᵁ U ≤ k.opensRange) (W : X.Opens) (hW : W ≤ U) (x : M.val.obj (op W)) :
    (coordinates r k N F e).val.app (op W)
      ((localMap r k N M (toTarget r k N F e M f) U hU).val.app (op (Over.mk (homOfLE hW))) x) =
      f.val.app (op W) x := by
  let q := ((SheafOfModules.evaluation _ (op W)).mapIso ((image r k).mapIso e)).toLinearEquiv
  exact (congrArg q (localMap_restrict r k N M (toTarget r k N F e M f) U hU W hW x)).trans
    (q.apply_symm_apply (f.val.app (op W) x))

variable (cD : ℂ →+* Γ(D,⊤)) (cY : ℂ →+* Γ(Y,⊤))
  (hc : compatible k cD cY)

private theorem coord_differentialMap :
    coordinates r k (differentialSheaf Y.sheaf cY) (differentialSheaf D.sheaf cD)
      (openDifferentialIso k cD cY hc) =
      (Scheme.Modules.pushforward r).map (schemeDifferentialMap k cD cY hc) := by
  refine (coordinates_eq r k _ _ _).trans ?_
  exact congrArg (Scheme.Modules.pushforward r).map
    (((Scheme.Modules.restrictAdjunction k).homEquiv_unit (differentialSheaf Y.sheaf cY)
      (differentialSheaf D.sheaf cD) (openDifferentialIso k cD cY hc).hom).symm.trans
      (openDifferentialIso_adjunct k cD cY hc))

private theorem coord_D (W : X.Opens) (a : Γ(Y, r ⁻¹ᵁ W)) :
    (coordinates r k (differentialSheaf Y.sheaf cY) (differentialSheaf D.sheaf cD)
      (openDifferentialIso k cD cY hc)).val.app (op W)
        ((universalDifferential Y.sheaf cY).d (X := op (r ⁻¹ᵁ W)) a) =
      (universalDifferential D.sheaf cD).d (X := op (k ⁻¹ᵁ (r ⁻¹ᵁ W))) (k.app _ a) := by
  rw [coord_differentialMap]
  exact schemeDifferentialMap_D k cD cY hc (r ⁻¹ᵁ W) a

end Sections

variable (t : Fin 3 → ℂ) (i : Fin 4)

local instance chartReductionModule : Module (B t i) (A t i) :=
  (CycleQ2LiteralCylinderEvaluation.reductionAlgebra t i).toModule

abbrev mapToChart := Spec.map (CommRingCat.ofHom (toClosed t i))
abbrev seedThenGerm := image (seedCurveToFirstOrderCurve t) (seedChart t i)

private abbrev seedOpen (W : (firstOrderCurve t).Opens) := (seedCurveToFirstOrderCurve t) ⁻¹ᵁ W
private abbrev affineOpen (W : (firstOrderCurve t).Opens) := (seedChart t i) ⁻¹ᵁ seedOpen t W

local instance curveSectionModule (W : (firstOrderCurve t).Opens) :
    Module Γ(CycleQ2LiteralMovingResidueAdjunction.AffineFrame.Curve t, seedOpen t W)
      ((curveDifferentials t).val.obj (op (seedOpen t W))) :=
  ((curveDifferentials t).val.obj (op (seedOpen t W))).isModule

local instance affineImageSectionModule (W : (firstOrderCurve t).Opens) :
    Module Γ(Spec (CommRingCat.of (A t i)), affineOpen t i W)
      (((seedThenGerm t i).obj (affineDifferentialSheaf (A t i))).val.obj (op W)) :=
  ((affineDifferentialSheaf (A t i)).val.obj (op (affineOpen t i W))).isModule

/-- The mixed component in affine curve coordinates transported along the Cartesian chart square. -/
abbrev rawEvaluation (v : Derivation ℂ (B t i) (A t i)) :=
  acrossSquare (mapToChart t i) (firstOrderChartToCurve t i) (seedChart t i)
    (seedCurveToFirstOrderCurve t) (seedChart_to_germ t i) (affineDifferentialSheaf (A t i))
    (CycleQ2LiteralAbelJacobiEvaluationRestriction.thickTwoForms t i) (germTwoForms t)
    (evaluation v) (germToChart t i)

abbrev rawEvaluation_apply (v : Derivation ℂ (B t i) (A t i)) :=
  acrossSquare_apply (mapToChart t i) (firstOrderChartToCurve t i) (seedChart t i)
    (seedCurveToFirstOrderCurve t) (seedChart_to_germ t i) (affineDifferentialSheaf (A t i))
    (CycleQ2LiteralAbelJacobiEvaluationRestriction.thickTwoForms t i) (germTwoForms t)
    (evaluation v) (germToChart t i)

/-- The full affine computation in the actual restricted differential sheaf. -/
abbrev chartEvaluation (v : Derivation ℂ (B t i) (A t i)) :=
  toTarget (seedCurveToFirstOrderCurve t) (seedChart t i) (curveDifferentials t)
    (affineDifferentialSheaf (A t i)) (seedChartDifferentials t i) (germTwoForms t) (rawEvaluation t i v)

/-- Restrict an intrinsic differential to affine coordinates. -/
abbrev toSeedCoordinates := coordinates (seedCurveToFirstOrderCurve t) (seedChart t i)
  (curveDifferentials t) (affineDifferentialSheaf (A t i)) (seedChartDifferentials t i)

abbrev toSeedCoordinates_differentialMap := coord_differentialMap (seedCurveToFirstOrderCurve t)
  (seedChart t i) (affineCoefficient (A t i)) (curveCoefficient t) (seedChart_coefficient t i)

abbrev toSeedCoordinates_smul := coord_smul (seedCurveToFirstOrderCurve t) (seedChart t i)
  (curveDifferentials t) (affineDifferentialSheaf (A t i)) (seedChartDifferentials t i)

abbrev toSeedCoordinates_D := coord_D (seedCurveToFirstOrderCurve t) (seedChart t i)
  (affineCoefficient (A t i)) (curveCoefficient t) (seedChart_coefficient t i)

theorem seedWithin :
    seedCurveToFirstOrderCurve t ⁻¹ᵁ (firstOrderCurveCoordinateOpen t i) ≤ (seedChart t i).opensRange :=
  (germ_preimage_coordinate t i).trans_le (seedChart_opensRange t i).symm.le

abbrev evaluationOn (v : Derivation ℂ (B t i) (A t i)) :=
  localMap (seedCurveToFirstOrderCurve t) (seedChart t i) (curveDifferentials t) (germTwoForms t)
    (chartEvaluation t i v) (firstOrderCurveCoordinateOpen t i) (seedWithin t i)

abbrev evaluationOn_chart (v : Derivation ℂ (B t i) (A t i)) :=
  localMap_restrict (seedCurveToFirstOrderCurve t) (seedChart t i) (curveDifferentials t) (germTwoForms t)
    (chartEvaluation t i v) (firstOrderCurveCoordinateOpen t i) (seedWithin t i)

abbrev toSeedCoordinates_injective := coord_injective (seedCurveToFirstOrderCurve t) (seedChart t i)
  (curveDifferentials t) (affineDifferentialSheaf (A t i)) (seedChartDifferentials t i)
  (firstOrderCurveCoordinateOpen t i) (seedWithin t i)

abbrev evaluationOn_coordinates (v : Derivation ℂ (B t i) (A t i)) :=
  coord_localMap (seedCurveToFirstOrderCurve t) (seedChart t i) (curveDifferentials t)
    (affineDifferentialSheaf (A t i)) (seedChartDifferentials t i) (germTwoForms t)
    (rawEvaluation t i v) (firstOrderCurveCoordinateOpen t i) (seedWithin t i)

end CycleQ2LiteralAbelJacobiEvaluationChart
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationChart.evaluationOn_chart
#print axioms CycleQ2LiteralAbelJacobiEvaluationChart.evaluationOn_coordinates
#print axioms CycleQ2LiteralAbelJacobiEvaluationChart.toSeedCoordinates_smul
#print axioms CycleQ2LiteralAbelJacobiEvaluationChart.toSeedCoordinates_D
