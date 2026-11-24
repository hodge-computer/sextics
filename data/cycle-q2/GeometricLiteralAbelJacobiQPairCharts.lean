import Proposal.GeometricLiteralAbelJacobiQChart
import Proposal.GeometricLiteralAbelJacobiQPullbackSections
import Proposal.GeometricLiteralThreefoldLiftTransition

/-!
# The actual germ of the second cylinder projection on two-chart intersections

In the source threefold chart the other chart inverts its weight-one
coordinate ratio. Pulling that principal open back along the moving or
specialized curve equations gives the two literal localized curve rings.
The projection from each localized curve chart factors through both native
threefold charts, with the weighted coordinate change on the second one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairCharts

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldOverlapAtlas
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientChartOverlap
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralThreefoldHodgeCech

attribute [local instance] sourceFixedAlgebra sourceFixedTower

section Pair
variable (i : Fin 4) (k : Fin 3) {S : Type} [CommRing S] [Algebra ℂ S] (f : T i →ₐ[ℂ] S)

abbrev ratio := CycleQ2LiteralThreefoldChartLift.q i (X (some k))
abbrev PairRing := Localization.Away (f (ratio i k))

private abbrev localMap : T i →ₐ[ℂ] PairRing i k f := (IsScalarTower.toAlgHom ℂ S _).comp f

/-- The affine map from the native pair ring, with the exact original denominator. -/
def pairMap : FixedOverlap i k →ₐ[ℂ] PairRing i k f :=
  overlapLift i k (localMap i k f) (IsLocalization.Away.algebraMap_isUnit (f (ratio i k)))

@[simp] theorem pairMap_source (a : T i) :
    pairMap i k f (sourceMap i k a) = algebraMap S (PairRing i k f) (f a) :=
  overlapLift_source i k (localMap i k f) _ a

abbrev pairToChart := Spec.map (CommRingCat.ofHom (algebraMap S (PairRing i k f)))
abbrev pairOpen := fixedOpen i ⊓ fixedOpen (i.succAbove k)

theorem pairToChart_range : (pairToChart i k f).opensRange = PrimeSpectrum.basicOpen (f (ratio i k)) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of S) _

/-- The native pair evaluation agrees with the geometric source chart on the entire pair scheme. -/
@[reassoc] theorem pairMap_toThreefold :
    Spec.map (CommRingCat.ofHom (pairMap i k f).toRingHom) ≫ (overlapIso i k).hom ≫ (pairOpen i k).ι =
    pairToChart i k f ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ≫ chartInclusion i := by
  rw [overlapIso_hom_ι, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  apply congrArg (fun g => Spec.map g ≫ chartInclusion i)
  apply CommRingCat.hom_ext
  exact RingHom.ext (pairMap_source i k f)

@[reassoc] theorem pairMap_target :
    Spec.map (CommRingCat.ofHom ((pairMap i k f).comp (fixedTargetMap i k)).toRingHom) ≫
      chartInclusion (i.succAbove k) = pairToChart i k f ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ≫ chartInclusion i := by
  refine Eq.trans ?_ (pairMap_toThreefold i k f)
  rw [overlapIso_hom_ι_target, ← Spec.map_comp_assoc]
  rfl

end Pair

open CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (hV : seedBasePoint ∈ V) (i : Fin 4) (k : Fin 3)

abbrev movingMap : T i →ₐ[ℂ] B t i := IsScalarTower.toAlgHom ℂ _ _
abbrev BPair := PairRing i k (movingMap t i)
abbrev APair := PairRing i k (toCurve t i)

/-- The inverse image of the second threefold chart on the original first-order curve chart. -/
theorem thick_preimage_other : (thickChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ fixedOpen (i.succAbove k) =
    PrimeSpectrum.basicOpen (movingMap t i (ratio i k)) := by
  rw [show thickChart V t hV i ≫ toThreefold V t = _ from thickChart_toSmoothThreefold V t hV i,
    Scheme.Hom.comp_preimage, chartInclusion_preimage_other]
  rfl

/-- The same pair open on the actual closed seed curve. -/
theorem closed_preimage_other : (closedChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ fixedOpen (i.succAbove k) =
    PrimeSpectrum.basicOpen (toCurve t i (ratio i k)) := by
  rw [show closedChart V t hV i ≫ toThreefold V t = _ from closedChart_toSmoothThreefold V t hV i,
    Scheme.Hom.comp_preimage, chartInclusion_preimage_other]
  rfl

theorem thickPair_range : (pairToChart i k (movingMap t i)).opensRange =
    (thickChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ fixedOpen (i.succAbove k) :=
  (pairToChart_range i k _).trans (thick_preimage_other V t hV i k).symm

theorem closedPair_range : (pairToChart i k (toCurve t i)).opensRange =
    (closedChart V t hV i ≫ toThreefold V t) ⁻¹ᵁ fixedOpen (i.succAbove k) :=
  (pairToChart_range i k _).trans (closed_preimage_other V t hV i k).symm

abbrev thickPairChart := pairToChart i k (movingMap t i) ≫ thickChart V t hV i
abbrev closedPairChart := pairToChart i k (toCurve t i) ≫ closedChart V t hV i

/-- The literal second projection on every first-order pair is the native localization map. -/
@[reassoc] theorem thickPair_toThreefold : thickPairChart V t hV i k ≫ toThreefold V t =
    Spec.map (CommRingCat.ofHom (pairMap i k (movingMap t i)).toRingHom) ≫ (overlapIso i k).hom ≫ (pairOpen i k).ι := by
  rw [thickPairChart, Category.assoc, show thickChart V t hV i ≫ toThreefold V t = _ from
    thickChart_toSmoothThreefold V t hV i]
  exact (pairMap_toThreefold i k (movingMap t i)).symm

/-- On the closed seed pair the same geometric projection evaluates the actual specialized coordinates. -/
@[reassoc] theorem closedPair_toThreefold : closedPairChart V t hV i k ≫ toThreefold V t =
    Spec.map (CommRingCat.ofHom (pairMap i k (toCurve t i)).toRingHom) ≫ (overlapIso i k).hom ≫ (pairOpen i k).ι := by
  rw [closedPairChart, Category.assoc, show closedChart V t hV i ≫ toThreefold V t = _ from
    closedChart_toSmoothThreefold V t hV i]
  exact (pairMap_toThreefold i k (toCurve t i)).symm

theorem thickPair_preimage : (thickPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ pairOpen i k = ⊤ := by
  rw [thickPair_toThreefold]
  simp only [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

theorem closedPair_preimage : (closedPairChart V t hV i k ≫ toThreefold V t) ⁻¹ᵁ pairOpen i k = ⊤ := by
  rw [closedPair_toThreefold]
  simp only [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

end CycleQ2LiteralAbelJacobiQPairCharts
end

#print axioms CycleQ2LiteralAbelJacobiQPairCharts.thickPair_toThreefold
#print axioms CycleQ2LiteralAbelJacobiQPairCharts.closedPair_toThreefold
