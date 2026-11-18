import Proposal.GeometricLiteralAbelJacobiQPairReduction
import Proposal.GeometricLiteralThreefoldMixedLiftChange
import Proposal.GeometricLiteralThreefoldMovingVolume

/-!
# The actual first-order curve velocity on the threefold projective pair

The original velocity localizes uniquely to the true pair of first-order
and seed curve charts. Its induced ambient vector evaluates the pullback
of the native two-form there, before the moving normal is lost.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldPairMotion

open MvPolynomial CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQPairReduction
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2ThreefoldContractionAlongMap CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldMixedChartChange CycleQ2LiteralThreefoldMixedLiftChange
  CycleQ2ExteriorSectionNaturality CycleQ2CurveCylinderPullback

open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower familyReductionTower

section Pullback
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S]

private theorem exterior_pullTwo :
    exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ R S) 2 = pullTwo R S := by
  unfold exteriorDifferentialMap pullTwo
  congr 1
  apply LinearMap.ext
  exact CycleQ2EtaleExteriorMapBinding.differentialMap_algebraMap

private theorem contract_exterior {C : Type} [CommRing C] [Algebra ℂ C] [Algebra R C]
    [Algebra S C] [IsScalarTower ℂ R C] [IsScalarTower ℂ S C] [IsScalarTower R S C]
    (w : Derivation ℂ S C) (ω : ⋀[R]^2 (KaehlerDifferential ℂ R)) :
    contractRestrict w (exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ R S) 2 ω) =
      contractRestrict (w.compAlgebraMap R) ω := by
  rw [exterior_pullTwo]
  exact contract_pullTwo w ω

end Pullback

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)

private abbrev b := B t i
private abbrev a := A t i
private abbrev u := FixedOverlap i k
private abbrev bp := BPair t i k
private abbrev ap := APair t i k
private abbrev locA := IsScalarTower.toAlgHom ℂ (a t i) (ap t i k)
private abbrev locB := IsScalarTower.toAlgHom ℂ (b t i) (bp t i k)
private abbrev closedPoint := pairMap i k (toCurve t i)
private abbrev thickPoint := pairMap i k (movingMap t i)

local instance reductionPairAlgebra : Algebra (bp t i k) (ap t i k) := (reduce t i k).toRingHom.toAlgebra
local instance reductionPairTower : IsScalarTower ℂ (bp t i k) (ap t i k) := IsScalarTower.of_algHom (reduce t i k)
private abbrev baseReduction := (locA t i k).comp (IsScalarTower.toAlgHom ℂ (b t i) (a t i))
local instance baseAlgebra : Algebra (b t i) (ap t i k) := (baseReduction t i k).toRingHom.toAlgebra
local instance baseTower : IsScalarTower ℂ (b t i) (ap t i k) := IsScalarTower.of_algHom (baseReduction t i k)
local instance baseATower : IsScalarTower (b t i) (a t i) (ap t i k) := IsScalarTower.of_algebraMap_eq' rfl
local instance baseBTower : IsScalarTower (b t i) (bp t i k) (ap t i k) :=
  IsScalarTower.of_algebraMap_eq fun r => (reduce_localize t i k r).symm

local instance ambientThickAlgebra : Algebra (u i k) (bp t i k) := (thickPoint t i k).toRingHom.toAlgebra
local instance ambientThickTower : IsScalarTower ℂ (u i k) (bp t i k) := IsScalarTower.of_algHom (thickPoint t i k)
local instance ambientClosedAlgebra : Algebra (u i k) (ap t i k) := (closedPoint t i k).toRingHom.toAlgebra
local instance ambientClosedTower : IsScalarTower ℂ (u i k) (ap t i k) := IsScalarTower.of_algHom (closedPoint t i k)
local instance ambientPairTower : IsScalarTower (u i k) (bp t i k) (ap t i k) :=
  IsScalarTower.of_algebraMap_eq fun r => (AlgHom.congr_fun (reduce_pairMap t i k) r).symm

private def localizedValues (v : Derivation ℂ (b t i) (a t i)) : Derivation ℂ (b t i) (ap t i k) :=
  ((Algebra.linearMap (a t i) (ap t i k)).restrictScalars (b t i)).compDer v

/-- The affine velocity has a unique extension to the actual moving pair. -/
theorem existsUnique_pair_velocity (v : Derivation ℂ (b t i) (a t i)) :
    ∃! w : Derivation ℂ (bp t i k) (ap t i k), ∀ r : b t i, w (locB t i k r) = locA t i k (v r) := by
  obtain ⟨w,hw,uniq⟩ := existsUnique_localized_vector (U := bp t i k)
    (Submonoid.powers (movingMap t i (ratio i k))) (localizedValues t i k v)
  refine ⟨w,fun r => congrArg (fun d : Derivation ℂ (b t i) (ap t i k) => d r) hw,fun z hz => uniq z ?_⟩
  ext r
  exact hz r

/-- The induced ambient vector on the pair recovers the original normal on
all functions of the source chart, including the transverse cubic. -/
theorem pair_velocity_source (v : Derivation ℂ (b t i) (a t i))
    (w : Derivation ℂ (bp t i k) (ap t i k))
    (hw : ∀ r : b t i, w (locB t i k r) = locA t i k (v r)) (r : T i) :
    (w.compAlgebraMap (u i k)) (sourceMap i k r) = locA t i k (v (toFamily t i r)) := by
  change w (pairMap i k (movingMap t i) (sourceMap i k r)) = _
  rw [pairMap_source]
  exact hw _

/-- Contracting the actual pullback on the moving pair is the mixed part
with its true induced normal along the original ambient projective overlap. -/
theorem pair_contract (w : Derivation ℂ (bp t i k) (ap t i k)) :
    contractRestrict w (edgeAt i k (thickPoint t i k)) =
      contractRestrict (w.compAlgebraMap (u i k)) (nativeEdge i k) := by
  rw [← nativeEdge_restrict]
  change contractRestrict w (exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (u i k) (bp t i k)) 2 _) = _
  exact contract_exterior w (nativeEdge i k)

/-- Actual lifted coordinates, actual first-order specialization, and the
ordinary curve one-form from the two ambient slots on the fixed pair. -/
theorem pair_mixed (w : Derivation ℂ (bp t i k) (ap t i k)) :
    contractRestrict w (edgeAt i k (thickPoint t i k)) = vertexMixed (fixedTargetMap i k)
      (normalizedLift i k (closedPoint t i k)) (canonical _ ((closedPoint t i k).comp (fixedTargetMap i k)))
      (normalizedLift_fst i k (closedPoint t i k)) (canonical_liesOver _ _) (w.compAlgebraMap (u i k)) := by
  rw [pair_contract]
  exact nativeEdge_vertexMixed i k _

/-- Every algebraically independent section has an honest parameter-one
velocity on its original first-order pair, compatible on all fixed-chart functions. -/
theorem independent_pair_velocity (ht : AlgebraicIndependent ℚ t) :
    ∃ (v : Derivation ℂ (b t i) (a t i)) (w : Derivation ℂ (bp t i k) (ap t i k)),
      w (locB t i k (algebraMap ℂ[ε] (b t i) ε)) = 1 ∧
      (∀ r : b t i, w (locB t i k r) = locA t i k (v r)) ∧
      (∀ r : T i, (w.compAlgebraMap (u i k)) (sourceMap i k r) = locA t i k (v (toFamily t i r))) := by
  have hc := CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht
  have hs := (CycleQ2LiteralAbelJacobiSeedLift.smooth_neighborhood_of_seed_minors t hc).1
  have := CycleQ2LiteralAbelJacobiSmoothNormal.flat_charts_of_smooth t hs i
  have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t hc i
  obtain ⟨v,hv,_⟩ := exists_evaluation t i
  obtain ⟨w,hw,_⟩ := existsUnique_pair_velocity t i k v
  refine ⟨v,w,?_,hw,pair_velocity_source t i k v w hw⟩
  rw [hw,hv,map_one]

end CycleQ2LiteralThreefoldPairMotion
end

#print axioms CycleQ2LiteralThreefoldPairMotion.existsUnique_pair_velocity
#print axioms CycleQ2LiteralThreefoldPairMotion.pair_mixed
#print axioms CycleQ2LiteralThreefoldPairMotion.independent_pair_velocity
