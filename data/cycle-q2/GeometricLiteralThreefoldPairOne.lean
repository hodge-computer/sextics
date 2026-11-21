import Proposal.GeometricCurveContractionRestriction
import Proposal.GeometricLiteralAbelJacobiEvaluationFiberVelocity
import Proposal.GeometricLiteralThreefoldGermMotion
import Proposal.GeometricLiteralThreefoldPairMotion
import Proposal.GeometricLiteralAbelJacobiQPairSeedSections

/-!
# Restricting the ordinary pair evaluation to the original curve vertex

On every smaller central-curve open, the one-form realized in the native
pair ring is the intrinsic realization of the ambient contraction there.
The point and its velocity are compared using only original chart functions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

noncomputable section
namespace CycleQ2LiteralThreefoldPairOne

open AlgebraicGeometry CategoryTheory CycleQ2CurveContractionRestriction
  CycleQ2LiteralThreefoldPairMotion CycleQ2LiteralThreefoldGermMotion CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairSeed CycleQ2LiteralAbelJacobiQPairSeedSections
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralProjectiveIntersections CycleQ2GeometricSectionDifferentials
  CycleQ2ActualCubicAdjunctionBinding CycleQ2LiteralThreefoldTestEdges

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower baseAlgebra baseTower baseATower baseBTower
  ambientThickAlgebra ambientThickTower ambientClosedAlgebra ambientClosedTower ambientPairTower
  sourceFixedAlgebra sourceFixedTower sourceFixedLocalization curveComplexOn

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable (t : Fin 3 → ℂ) (p : Vertex) (k : Fin 3) (W : (Curve t).Opens)
private abbrev i := p.2.succ
private abbrev U := FixedOverlap (i p) k
private abbrev P := BPair t (i p) k
private abbrev Q := APair t (i p) k
private abbrev C := CurveRingOn t W

variable (hW : W ≤ vertexOpen t p) (hpair : W ≤ (pairToSeed t (i p) k).opensRange)

private abbrev pairPoint := seedPointAlg t (i p) k W hpair

private theorem pairPoint_source (a : A t (i p)) :
    pairPoint t p k W hpair (algebraMap (A t (i p)) (Q t p k) a) = seedSections t p W hW a :=
  seedRing_base t (i p) k W hpair a

variable [Algebra (U p k) (C t W)] [IsScalarTower ℂ (U p k) (C t W)]
variable (hp : ∀ r : T (i p), algebraMap (U p k) (C t W) (sourceMap (i p) k r) = ambientPoint t p W hW r)
  (v : Derivation ℂ (B t (i p)) (A t (i p))) (w : Derivation ℂ (P t p k) (Q t p k))
  (hw : ∀ b : B t (i p), w (algebraMap (B t (i p)) (P t p k) b) =
    algebraMap (A t (i p)) (Q t p k) (v b))

include hp in
private theorem pairPoint_position (z : U p k) :
    pairPoint t p k W hpair (algebraMap (U p k) (Q t p k) z) = algebraMap (U p k) (C t W) z := by
  have h : (pairPoint t p k W hpair).toRingHom.comp (algebraMap (U p k) (Q t p k)) =
      algebraMap (U p k) (C t W) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q (i p) (MvPolynomial.X (some k))))
    apply RingHom.ext
    intro r
    change pairPoint t p k W hpair (pairMap (i p) k (toCurve t (i p)) (sourceMap (i p) k r)) = _
    rw [pairMap_source, pairPoint_source t p k W hW hpair]
    exact (hp r).symm
  exact RingHom.congr_fun h z

variable (ν : Derivation ℂ (U p k) (C t W))
  (hν : ∀ r : T (i p), ν (sourceMap (i p) k r) = ambientMotion t p W hW v r)

include hp hw hν in
/-- The localized pair-ring expression and the full ambient contraction agree
in the original differential sheaf, for every ambient two-form. -/
theorem pairOne_of_source (ω : ⋀[U p k]^2 (KaehlerDifferential ℂ (U p k))) :
    seedOne t (i p) k W hpair (contractRestrict (w.compAlgebraMap (U p k)) ω) =
      toSheaf (Curve t).sheaf (curveCoefficient t) W (contractRestrict ν ω) := by
  let f := pairPoint t p k W hpair
  have hf := pairPoint_position t p k W hW hpair hp
  have hz (a : T (i p)) : f ((w.compAlgebraMap (U p k)) (sourceMap (i p) k a)) = ν (sourceMap (i p) k a) := by
    rw [pair_velocity_source t (i p) k v w hw, hν a, ambientMotion_apply]
    exact pairPoint_source t p k W hW hpair _
  have hv := velocity_ext f hf (w.compAlgebraMap (U p k)) ν
    (Submonoid.powers (q (i p) (MvPolynomial.X (some k)))) hz
  exact (seedOne_toSheaf t (i p) k W hpair _).trans
    (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) W) (contract_natural f hf _ ν hv ω))

section Germ

open CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveCharts
  CycleQ2FirstOrderCurveSeedFiber CycleQ2GeometricAffineDifferentialSheaf
attribute [local instance] germAlgebra reductionOn CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.sectionTower

variable (G : (firstOrderCurve t).Opens)
private abbrev seedOpen := seedCurveToFirstOrderCurve t ⁻¹ᵁ G
variable (hG : G ≤ firstOrderCurveCoordinateOpen t (i p)) (hV : seedOpen t G ≤ vertexOpen t p)
  (hpV : seedOpen t G ≤ (pairToSeed t (i p) k).opensRange)
  [Algebra (U p k) (GermRing t G)] [Algebra (U p k) (SeedRing t G)]
  [IsScalarTower ℂ (U p k) (GermRing t G)] [IsScalarTower ℂ (U p k) (SeedRing t G)]
  [IsScalarTower (U p k) (GermRing t G) (SeedRing t G)]

include hw in
/-- On the genuine first-order chart this formula uses its original
normalized derivation, acting on the common-open coordinate functions. -/
theorem pairOne_onOpen
    (hpoint : ∀ r : T (i p), algebraMap (U p k) (SeedRing t G) (sourceMap (i p) k r) =
      ambientPoint t p (seedOpen t G) hV r)
    (hgerm : ∀ r : T (i p), (firstOrderChartToCurve t (i p)).app G
      (algebraMap (U p k) (GermRing t G) (sourceMap (i p) k r)) = algebraMap (B t (i p))
        (AffineSections (B t (i p)) ((firstOrderChartToCurve t (i p)) ⁻¹ᵁ G)) (toFamily t (i p) r))
    (ω : ⋀[U p k]^2 (KaehlerDifferential ℂ (U p k))) :
    seedOne t (i p) k (seedOpen t G) hpV (contractRestrict (w.compAlgebraMap (U p k)) ω) =
      toSheaf (Curve t).sheaf (curveCoefficient t) (seedOpen t G)
        (contractRestrict ((onOpen t (i p) v G hG).compAlgebraMap (U p k)) ω) := by
  exact pairOne_of_source t p k (seedOpen t G) hV hpV hpoint v w hw _
    (fun r => onOpen_eq_ambient t p G hG hV v r _ (hgerm r)) ω

end Germ
end CycleQ2LiteralThreefoldPairOne
end

#print axioms CycleQ2LiteralThreefoldPairOne.pairOne_of_source

#print axioms CycleQ2LiteralThreefoldPairOne.pairOne_onOpen
