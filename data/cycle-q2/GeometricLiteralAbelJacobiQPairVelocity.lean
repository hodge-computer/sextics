import Proposal.GeometricLiteralAbelJacobiQPairSeedSections
import Proposal.GeometricLiteralThreefoldPairMotion
import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricLiteralAbelJacobiEvaluationNormalized

/-!
# The localized velocity on the genuine projective seed overlap

The normalized parameter vector extends to the actual first-order chart pair. Its
values on the source threefold coordinates are the original vertex motion on
every smaller open of the projective seed curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQNativeSeedEvaluation

open CategoryTheory AlgebraicGeometry CycleQ2LiteralAbelJacobiQPairSeed
  CycleQ2LiteralAbelJacobiQPairSeedSections CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralThreefoldPairMotion CycleQ2LiteralThreefoldVertexMotion
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationChart
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve
attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyComplexSMul familyComplexModule familyAlgebra familyComplexTower fixedAlgebra fixedTower
  reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower baseAlgebra baseTower baseATower baseBTower
  ambientThickAlgebra ambientThickTower ambientClosedAlgebra ambientClosedTower ambientPairTower
attribute [local instance 2000] Algebra.toSMul Algebra.toModule
attribute [local instance] curveComplexOn

variable (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) (k : Fin 3)

/-- Unique restriction of the original normalized velocity to the actual thick pair. -/
def pairVelocity : Derivation ℂ (BPair t i k) (APair t i k) :=
  Classical.choose (existsUnique_pair_velocity t i k (normalizedVelocity t i ht))

theorem pairVelocity_original (b : B t i) :
    pairVelocity t ht i k (algebraMap (B t i) (BPair t i k) b) =
      algebraMap (A t i) (APair t i k) (normalizedVelocity t i ht b) :=
  (Classical.choose_spec (existsUnique_pair_velocity t i k (normalizedVelocity t i ht))).1 b

abbrev overlapPointOnSeed (W : (Curve t).Opens) (hpair : W ≤ (pairToSeed t i k).opensRange) :=
  (seedPointAlg t i k W hpair).comp (pairMap i k (toCurve t i))

/-- The normalized curve motion as a derivation from the whole original
threefold overlap into regular functions on the chosen projective seed open. -/
def overlapVelocityOnSeed (W : (Curve t).Opens) (hpair : W ≤ (pairToSeed t i k).opensRange) :
    letI := (overlapPointOnSeed t i k W hpair).toRingHom.toAlgebra
    Derivation ℂ (FixedOverlap i k) (CurveRingOn t W) := by
  letI := (seedPointAlg t i k W hpair).toRingHom.toAlgebra
  letI := (overlapPointOnSeed t i k W hpair).toRingHom.toAlgebra
  letI : IsScalarTower (FixedOverlap i k) (APair t i k) (CurveRingOn t W) := IsScalarTower.of_algebraMap_eq' rfl
  exact ((Algebra.linearMap (APair t i k) (CurveRingOn t W)).restrictScalars (FixedOverlap i k)).compDer
    ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k))

/-- The velocity on the localized overlap evaluates each original chart function
at the normalized velocity used by the projective vertex. -/
theorem overlapVelocityOnSeed_source (p : Vertex) (W : (Curve t).Opens)
    (hW : W ≤ vertexOpen t p) (hpair : W ≤ (pairToSeed t p.2.succ k).opensRange) (a : T p.2.succ) :
    overlapVelocityOnSeed t ht p.2.succ k W hpair (sourceMap p.2.succ k a) =
      ambientMotion t p W hW (normalizedVelocity t p.2.succ ht) a := by
  change seedPointAlg t p.2.succ k W hpair
    (((pairVelocity t ht p.2.succ k).compAlgebraMap (FixedOverlap p.2.succ k)) (sourceMap p.2.succ k a)) = _
  rw [pair_velocity_source t p.2.succ k (normalizedVelocity t p.2.succ ht)
    (pairVelocity t ht p.2.succ k) (pairVelocity_original t ht p.2.succ k), ambientMotion_apply]
  exact seedRing_base t p.2.succ k W hpair _

end CycleQ2LiteralAbelJacobiQNativeSeedEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiQNativeSeedEvaluation.overlapVelocityOnSeed_source
