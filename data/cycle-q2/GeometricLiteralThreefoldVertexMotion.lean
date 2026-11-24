import Proposal.GeometricLiteralThreefoldCurveTestSections
import Proposal.GeometricLiteralAbelJacobiEvaluationSeedForms
import Proposal.GeometricLiteralThreefoldMovingVolume

/-!
# The original parameter velocity on every smaller vertex open of the curve

One original affine parameter velocity supplies an ambient vector along the
curve on all subopens of its native vertex. Its values restrict as sections
of the actual structure sheaf of the specialized curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldVertexMotion

open CategoryTheory AlgebraicGeometry Opposite CycleQ2LiteralThreefoldCurveTestSections
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections CycleQ2SeedSectionCurveRows
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2GeometricAffineChartSections CycleQ2ProjectiveCartierIdeal CycleQ2CartierProjectiveCover
  CycleQ2SeedProjectiveImageCocycle CycleQ2SpecializedCurveCoordinateChart
  CycleQ2LiteralAbelJacobiEvaluationSeedForms CycleQ2GeometricSurfaceCoefficients
  CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiEquations

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  curveComplexOn

open scoped DualNumber

variable (t : Fin 3 → ℂ) (p : Vertex)

theorem vertexWithin : vertexOpen t p ≤ specializedCoordinatePatch seed t p.2.succ := by
  rw [← curveToSurface_preimage_patch]
  apply (curveToSurface t).preimage_mono
  change cover p ≤ Patch p.2
  rw [cover, refinedOpen_eq]
  apply inf_le_right.trans
  exact (congrArg (fun j : Fin 5 => Proj.basicOpen (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
    (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (MvPolynomial.X j)))
    (CycleQ2SeedProjectiveImageChart.remainingIndex_eq p.2)).le

variable (W : (Curve t).Opens) (h : W ≤ vertexOpen t p)

private abbrev chart := specializedCoordinateAffineChart seed t p.2.succ
private abbrev within := h.trans (vertexWithin t p)

/-- The real coordinate map from the seed affine curve to sections on an
arbitrary subopen of the given native vertex. -/
def seedSections : A t p.2.succ →ₐ[ℂ] CurveRingOn t W where
  __ := chartSection (chart t p) (Over.mk (homOfLE (within t p W h)))
  commutes' c := by
    apply chartSection_complex (chart t p) ((curveToSurface t) ≫ projectiveToComplex 57 1)
    simpa only [CycleQ2LiteralAbelJacobiEvaluationFiber.seedChart, Category.assoc] using seedChart_structure t p.2.succ

theorem seedSections_restrict {Z : (Curve t).Opens} (hZ : Z ≤ W) :
    (curveRestriction t hZ).comp (seedSections t p W h) = seedSections t p Z (hZ.trans h) := by
  apply AlgHom.ext
  intro a
  exact chartSection_naturality (chart t p) (Over.homMk (homOfLE hZ) (by rfl) :
    Over.mk (homOfLE (within t p Z (hZ.trans h))) ⟶ Over.mk (homOfLE (within t p W h))) a

/-- The ambient point over the actual functions on the vertex subopen. -/
def ambientPoint : T p.2.succ →ₐ[ℂ] CurveRingOn t W := (seedSections t p W h).comp (toCurve t p.2.succ)

abbrev ambientAlgebra : Algebra (T p.2.succ) (CurveRingOn t W) :=
  (ambientPoint t p W h).toRingHom.toAlgebra

/-- The chosen velocity of the actual thick curve, evaluated on the original
ambient chart and then restricted to this subopen of the reduced curve. -/
def ambientMotion (v : Derivation ℂ (B t p.2.succ) (A t p.2.succ)) :
    letI := ambientAlgebra t p W h
    Derivation ℂ (T p.2.succ) (CurveRingOn t W) := by
  letI := (seedSections t p W h).toRingHom.toAlgebra
  letI := ambientAlgebra t p W h
  letI : IsScalarTower (T p.2.succ) (A t p.2.succ) (CurveRingOn t W) := IsScalarTower.of_algebraMap_eq' rfl
  exact ((Algebra.linearMap (A t p.2.succ) (CurveRingOn t W)).restrictScalars (T p.2.succ)).compDer
    (v.compAlgebraMap (T p.2.succ))

theorem ambientMotion_apply (v : Derivation ℂ (B t p.2.succ) (A t p.2.succ)) (r : T p.2.succ) :
    ambientMotion t p W h v r = seedSections t p W h (v (toFamily t p.2.succ r)) := rfl

/-- A true parameter-one velocity evaluates the actual transverse cubic as
the negative of its retained first-order coefficient. -/
theorem chart_velocity_cubic (i : Fin 4) (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) :
    v (toFamily t i (cubicOnT i)) = -(seedChartMap t i (tangentL i)) := by
  change v (chartMap t i (seedH i)) = _
  rw [chartMap_H, map_neg, v.leibniz, Algebra.smul_def, Algebra.smul_def, specialize_epsilon, hv,
    zero_mul, mul_one, zero_add]
  exact congrArg Neg.neg (chartMap_reduction t i (tangentL i))

theorem ambientMotion_cubic (v : Derivation ℂ (B t p.2.succ) (A t p.2.succ))
    (hv : v (algebraMap ℂ[ε] (B t p.2.succ) ε) = 1) :
    ambientMotion t p W h v (cubicOnT p.2.succ) =
      -(seedSections t p W h (seedChartMap t p.2.succ (tangentL p.2.succ))) := by
  rw [ambientMotion_apply, chart_velocity_cubic t p.2.succ v hv, map_neg]

theorem ambientMotion_restrict {Z : (Curve t).Opens} (hZ : Z ≤ W)
    (v : Derivation ℂ (B t p.2.succ) (A t p.2.succ)) (r : T p.2.succ) :
    curveRestriction t hZ (ambientMotion t p W h v r) = ambientMotion t p Z (hZ.trans h) v r :=
  AlgHom.congr_fun (seedSections_restrict t p W h hZ) _

/-- A single parameter-one representative on a native original chart works
on every one of its open subsets, with a functorial ambient motion. -/
theorem independent_vertex_motion (ht : AlgebraicIndependent ℚ t) :
    ∃ v : Derivation ℂ (B t p.2.succ) (A t p.2.succ),
      v (algebraMap ℂ[ε] (B t p.2.succ) ε) = 1 ∧
      ∀ (W Z : (Curve t).Opens) (hW : W ≤ vertexOpen t p) (hZ : Z ≤ W) (r : T p.2.succ),
        curveRestriction t hZ (ambientMotion t p W hW v r) = ambientMotion t p Z (hZ.trans hW) v r := by
  have hc := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := (CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_seed_minors t hc).1
  have := CycleQ2LiteralAbelJacobiSmoothNormal.flat_charts_of_smooth t hs p.2.succ
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t hc p.2.succ
  obtain ⟨v,hv,_⟩ := exists_evaluation t p.2.succ
  exact ⟨v,hv,fun W _ hW hZ r => ambientMotion_restrict t p W hW hZ v r⟩

end CycleQ2LiteralThreefoldVertexMotion
end

#print axioms CycleQ2LiteralThreefoldVertexMotion.ambientMotion_cubic
#print axioms CycleQ2LiteralThreefoldVertexMotion.ambientMotion_restrict
#print axioms CycleQ2LiteralThreefoldVertexMotion.independent_vertex_motion
