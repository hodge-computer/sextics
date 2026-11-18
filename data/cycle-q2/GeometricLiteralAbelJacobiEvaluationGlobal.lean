import Proposal.GeometricLiteralAbelJacobiEvaluationFormula
import Proposal.GeometricLiteralAbelJacobiEvaluationExt
import Proposal.GeometricLiteralAbelJacobiEvaluationOverlapSections

/-!
# The global tangent evaluation on the original curve family

The normalized time velocities on the four projective charts all give
the same evaluation on their intersections. They glue in the internal
Hom sheaf on the original first-order family. Restriction from the smooth
time family then gives an intrinsic map into the ordinary one-forms of
the embedded projective seed curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationGlobal

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralAbelJacobiEvaluationFormula CycleQ2LiteralAbelJacobiEvaluationLocal
  CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2LiteralAbelJacobiEvaluationFiber
  CycleQ2LiteralAbelJacobiEvaluationGerm CycleQ2LiteralAbelJacobiEvaluationWedge
  CycleQ2LiteralAbelJacobiEvaluationExt CycleQ2LiteralAbelJacobiEvaluationOverlapSections
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceChartFiberScheme CycleQ2IncidenceSeedFiberCover
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurveSeedFiber
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricModuleLocalIso CycleQ2LiteralMovingResidueCurve

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
abbrev germTarget := target (seedCurveToFirstOrderCurve t) (curveDifferentials t)
abbrev homSheaf := addSheaf (moduleHomSheaf (firstOrderCurve t).sheaf (germTwoForms t) (germTarget t))
def onChart (i : Fin 4) :
    LocalLinearHom (firstOrderCurve t).sheaf (germTwoForms t) (germTarget t)
      (firstOrderCurveCoordinateOpen t i) :=
  evaluationOn t i (normalizedVelocity t i ht)

private theorem compatible_of_exact {X : Scheme.{0}} {I : Type} (c : ℂ →+* Γ(X,⊤))
    (N : X.Modules) (U : I → X.Opens)
    (L : ∀ i, LocalLinearHom X.sheaf (CycleQ2ExteriorPullComposition.forms X c 2) N (U i))
    (agree : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j), IsAffineOpen W →
      ∀ a : Fin 2 → Γ(X,W), (L i).val.app (op (Over.mk (homOfLE hi))) (exactWedge X c W a) =
        (L j).val.app (op (Over.mk (homOfLE hj))) (exactWedge X c W a)) :
    TopCat.Presheaf.IsCompatible
      (addSheaf (moduleHomSheaf X.sheaf (CycleQ2ExteriorPullComposition.forms X c 2) N)).obj U L := by
  intro i j
  let M := CycleQ2ExteriorPullComposition.forms X c 2
  exact localLinearHom_ext_affine_exact (X := X) N 2 (U i ⊓ U j) c
    (restrictLocalLinearHom X.sheaf M N (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (L i))
    (restrictLocalLinearHom X.sheaf M N (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (L j))
    (fun W hW hA a => agree i j W (hW.trans inf_le_left) (hW.trans inf_le_right) hA a)

private def evaluateExact {X : Scheme.{0}} (c : ℂ →+* Γ(X,⊤)) (N : X.Modules)
    (U : X.Opens) (L : LocalLinearHom X.sheaf (CycleQ2ExteriorPullComposition.forms X c 2) N U)
    (W : X.Opens) (h : W ≤ U) (a : Fin 2 → Γ(X,W)) : N.val.obj (op W) :=
  L.val.app (op (Over.mk (homOfLE h))) (exactWedge X c W a)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem agree_on_exact (i j : Fin 4) (W : (firstOrderCurve t).Opens)
    (hi : W ≤ firstOrderCurveCoordinateOpen t i) (hj : W ≤ firstOrderCurveCoordinateOpen t j)
    (hA : IsAffineOpen W) (a : Fin 2 → Γ(firstOrderCurve t,W)) :
    evaluateExact (germCoefficient t) (germTarget t) _ (onChart t ht i) W hi a =
      evaluateExact (germCoefficient t) (germTarget t) _ (onChart t ht j) W hj a := by
  unfold evaluateExact onChart
  rw [evaluation_exact, evaluation_exact]
  exact onOpen_cartan t W ht hA i j hi hj (normalizedVelocity t i ht) (normalizedVelocity t j ht)
    (normalizedVelocity_epsilon t i ht) (normalizedVelocity_epsilon t j ht) (a 0) (a 1)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
abbrev compatible :=
  compatible_of_exact (X := firstOrderCurve t) (germCoefficient t) (germTarget t)
    (firstOrderCurveCoordinateOpen t) (onChart t ht) (agree_on_exact t ht)

private theorem existsUnique_evaluation :
    ∃! e : (homSheaf t).obj.obj (op ⊤), ∀ i,
      (homSheaf t).obj.map (homOfLE (show firstOrderCurveCoordinateOpen t i ≤ ⊤ from le_top)).op e =
        onChart t ht i :=
  (homSheaf t).existsUnique_gluing' (firstOrderCurveCoordinateOpen t) ⊤ (fun _ => homOfLE le_top)
    (iSup_firstOrderCurveCoordinateOpen t).ge (onChart t ht) (compatible t ht)

def germEvaluation : germTwoForms t ⟶ germTarget t :=
  localLinearHomTopEquiv _ _ _ (Classical.choose (existsUnique_evaluation t ht))

theorem germEvaluation_on (i : Fin 4) (W : (firstOrderCurve t).Opens)
    (hW : W ≤ firstOrderCurveCoordinateOpen t i) (ω : (germTwoForms t).val.obj (op W)) :
    (germEvaluation t ht).val.app (op W) ω =
      (onChart t ht i).val.app (op (Over.mk (homOfLE hW))) ω := by
  exact congrArg (fun f : LocalLinearHom _ (germTwoForms t) (germTarget t) (firstOrderCurveCoordinateOpen t i) =>
    f.val.app (op (Over.mk (homOfLE hW))) ω) ((Classical.choose_spec (existsUnique_evaluation t ht)).1 i)

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

/-- Evaluate absolute two-forms of the smooth time family against its original time tangent. -/
def timeEvaluation :
    familyTwoForms V t ⟶ (Scheme.Modules.pushforward (seedToTime t V hV)).obj (curveDifferentials t) :=
  toGerm t V hV ≫ (Scheme.Modules.pushforward (germToTime t V hV)).map (germEvaluation t ht) ≫
    (Scheme.Modules.pushforwardComp (seedCurveToFirstOrderCurve t) (germToTime t V hV)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (seed_germ_to_time t V hV)).hom.app _

end CycleQ2LiteralAbelJacobiEvaluationGlobal
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationGlobal.germEvaluation_on
#print axioms CycleQ2LiteralAbelJacobiEvaluationGlobal.timeEvaluation
