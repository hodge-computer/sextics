import Proposal.GeometricLiteralThreefoldCurveVertexLifts
import Proposal.GeometricLiteralThreefoldVertexPointBinding
import Proposal.GeometricLiteralAbelJacobiEvaluationNormalized

/-!
# The vertex one-cochain correction for the genuine curve velocity

Each original surface vertex carries an ordinary differential on its
central curve open. It uses the same normalized time velocity as the
sheaf evaluation of the pulled ambient test. Its restrictions to smaller
opens can be computed in the actual homogeneous intersection rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldCurveVertexCochain

open CycleQ2GeometricSheafLocalIso CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2LiteralThreefoldCurveVertexLifts CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPointBinding
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralThreefoldMixedRestriction
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2FiniteInjectiveCech CycleQ2InjectiveCech CycleQ2LiteralMovingResidueCurve
  CycleQ2GeometricSectionDifferentials

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  curveComplexOn

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (s : Finset Vertex)
  (v : Vertex) (hv : v ∈ s) (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s)

private abbrev p := ambientPoint t v W (withinVertex t s v hv W hW)
private abbrev x := curveLift t s v hv W hW v.1 ⟨v.2,hv⟩

private theorem lies : LiesOver (x t s v hv W hW) (p t s v hv W hW) := by
  rw [p, ← ambientPoint_eq_native t s ⟨v,hv⟩ v hv W hW]
  exact curveLift_over t s v hv W hW v.1 ⟨v.2,hv⟩

def rawVertex : KaehlerDifferential ℂ (CurveRingOn t W) :=
  vertexForm (p t s v hv W hW) (canonical _ (p t s v hv W hW)) (x t s v hv W hW)
    (canonical_liesOver _ _) (lies t s v hv W hW)
    (ambientMotion t v W (withinVertex t s v hv W hW) (normalizedVelocity t (chartIndex v) ht))

theorem rawVertex_restrict {Z : (Curve t).Opens} (hZ : Z ≤ W) :
    CycleQ2GeometricAffineOverlap.differentialMap (curveRestriction t hZ) (rawVertex t ht s v hv W hW) =
      rawVertex t ht s v hv Z (hZ.trans hW) := by
  have eqp : (curveRestriction t hZ).comp (p t s v hv W hW) = p t s v hv Z (hZ.trans hW) := by
    apply AlgHom.ext
    intro a
    exact AlgHom.congr_fun (seedSections_restrict t v W (withinVertex t s v hv W hW) hZ) (toCurve t (chartIndex v) a)
  exact vertexForm_restrict_to _ _ _ eqp _ _ _ _ _ _ _ _
    ((mapLift_canonical _ _ _).trans (congrArg (canonical (chartIndex v)) eqp))
    (curveLift_restrict t s v hv W hW v.1 ⟨v.2,hv⟩ hZ) _ _
    (ambientMotion_restrict t v W (withinVertex t s v hv W hW) hZ (normalizedVelocity t (chartIndex v) ht))

def sectionOn : (curveDifferentials t).val.obj (op W) :=
  toSheaf (Curve t).sheaf (curveCoefficient t) W (rawVertex t ht s v hv W hW)

theorem sectionOn_restrict {Z : (Curve t).Opens} (hZ : Z ≤ W) :
    (curveDifferentials t).val.map (homOfLE hZ).op (sectionOn t ht s v hv W hW) =
      sectionOn t ht s v hv Z (hZ.trans hW) := by
  exact (toSheaf_restrict _ _ hZ _).trans
    (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) Z) (rawVertex_restrict t ht s v hv W hW hZ))

private theorem vertexForm_congr {C : Type} [CommRing C] [Algebra ℂ C] {i : Fin 4}
    (f : T i →ₐ[ℂ] C) {a b c : Lift i C} (ha : LiesOver a f) (hb : LiesOver b f) (hc : LiesOver c f)
    (e : b = c) : vertexForm f a b ha hb = vertexForm f a c ha hc := by
  subst c
  rfl

theorem rawVertex_refine {s u : Finset Vertex} (hsu : s ⊆ u) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen u) :
    rawVertex t ht u v (hsu hv) W hW = rawVertex t ht s v hv W
      (hW.trans ((TopologicalSpace.Opens.map (curveToSurface t).base).map
        (homOfLE (CycleQ2LiteralProjectiveIntersectionRestrictions.closedOpen_mono hsu))).le) := by
  unfold rawVertex
  apply congrFun
  apply vertexForm_congr
  exact curveLift_refine t hsu v hv W hW v.1 ⟨v.2,hv⟩

theorem sectionOn_refine {s u : Finset Vertex} (hsu : s ⊆ u) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen u) :
    sectionOn t ht u v (hsu hv) W hW = sectionOn t ht s v hv W
      (hW.trans ((TopologicalSpace.Opens.map (curveToSurface t).base).map
        (homOfLE (CycleQ2LiteralProjectiveIntersectionRestrictions.closedOpen_mono hsu))).le) :=
  congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) W) (rawVertex_refine t ht hsu v hv W hW)

private theorem singletonWithin (t : Fin 3 → ℂ) (v : Vertex) :
    vertexOpen t v ≤ (curveToSurface t) ⁻¹ᵁ closedOpen {v} := by
  change (curveToSurface t) ⁻¹ᵁ cover v ≤ (curveToSurface t) ⁻¹ᵁ closedOpen {v}
  simp [closedOpen_eq, cover]

def corrections : CycleQ2FiniteCechDescent.Zero (curveForms t) (vertexOpen t) := fun v =>
  sectionOn t ht {v} v (by simp) (vertexOpen t v) (singletonWithin t v)

theorem corrections_on_intersection :
    res (curveForms t) (withinVertex t s v hv W hW) (corrections t ht v) = sectionOn t ht s v hv W hW := by
  have sub : ({v} : Finset Vertex) ⊆ s := Finset.singleton_subset_iff.mpr hv
  exact (sectionOn_restrict t ht {v} v (by simp) (vertexOpen t v) (singletonWithin t v) (withinVertex t s v hv W hW)).trans
    (sectionOn_refine t ht sub v (by simp) W hW).symm

end CycleQ2LiteralThreefoldCurveVertexCochain
end

#print axioms CycleQ2LiteralThreefoldCurveVertexCochain.sectionOn_restrict
#print axioms CycleQ2LiteralThreefoldCurveVertexCochain.corrections
