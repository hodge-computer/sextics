import Proposal.GeometricLiteralAbelJacobiQPairCharts
import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricLiteralAbelJacobiTimeContraction

/-!
# The genuine affine pair in the projective seed curve

The source weight-one chart and inverse image of the target chart cut
out the localized seed ring. This is an open immersion into the original
projective curve; for independent section parameters its cotangent
exterior square is zero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairSeed

open CategoryTheory Opposite AlgebraicGeometry CycleQ2LiteralAbelJacobiQPairCharts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralThreefoldOverlapAtlas CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiTimeContraction
  CycleQ2LiteralAbelJacobiSeedLiftDimension CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveCoordinateChart CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
open CycleQ2SeedConeSection (seed)

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V)
  (i : Fin 4) (k : Fin 3)

abbrev pairToSeed := pairToChart i k (toCurve t i) ≫ seedChart t i

theorem seedChart_toTime : seedChart t i ≫ seedToTime t V hV = closedChart V t hV i := by
  simp only [closedChart, seedChart, seedToTime, Category.assoc]

theorem pairToSeed_over :
    pairToSeed t i k ≫ seedToTime t V hV ≫ toThreefold V t =
    Spec.map (CommRingCat.ofHom (pairMap i k (toCurve t i)).toRingHom) ≫
      (overlapIso i k).hom ≫ (pairOpen i k).ι := by
  refine Eq.trans ?_ (closedPair_toThreefold V t hV i k)
  simp only [pairToSeed, closedPairChart, closedChart, seedChart, seedToTime, Category.assoc]

theorem pairToSeed_range : (pairToSeed t i k).opensRange =
    (seedChart t i).opensRange ⊓ (seedToTime t V hV ≫ toThreefold V t) ⁻¹ᵁ fixedOpen (i.succAbove k) := by
  have he : closedChart V t hV i ≫ toThreefold V t = seedChart t i ≫ seedToTime t V hV ≫ toThreefold V t := by
    rw [← Category.assoc, seedChart_toTime]
  refine (Scheme.Hom.opensRange_comp (pairToChart i k (toCurve t i)) (seedChart t i)).trans ?_
  rw [closedPair_range V t hV i k, he, Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf]

theorem pairToSeed_overBase : pairToSeed t i k ≫ specializedCurveToBase seed t =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (APair t i k))) := by
  rw [pairToSeed, Category.assoc, seedChart, Category.assoc, specializedCoordinateAffineChart_overBase,
    pairToChart, ← Spec.map_comp]
  rfl

theorem pair_exteriorTwo (ht : AlgebraicIndependent ℚ t) :
    Subsingleton (⋀[APair t i k]^2 (KaehlerDifferential ℂ (APair t i k))) := by
  have hs := smooth_seed_of_seedMinorCover t (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)
  have hc : SmoothOfRelativeDimension 1 (pairToSeed t i k ≫ specializedCurveToBase seed t) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  rw [pairToSeed_overBase] at hc
  exact exteriorTwo_subsingleton_of_curve ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hc)

end CycleQ2LiteralAbelJacobiQPairSeed
end

#print axioms CycleQ2LiteralAbelJacobiQPairSeed.pairToSeed_range
#print axioms CycleQ2LiteralAbelJacobiQPairSeed.pair_exteriorTwo
