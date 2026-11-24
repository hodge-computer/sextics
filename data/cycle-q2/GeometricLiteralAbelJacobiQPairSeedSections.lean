import Proposal.GeometricLiteralAbelJacobiQPairSeed
import Proposal.GeometricLiteralAbelJacobiEvaluationSeedForms
import Proposal.GeometricLiteralAbelJacobiQAffineForms
import Proposal.GeometricCartierNormalConnecting

/-!
# One-forms of a localized seed pair on the original projective curve

The affine pair chart identifies its coordinate ring with regular functions
on the corresponding seed open. The ordinary differential of any element of
this ring thus gives a one-form on every smaller open of the projective seed.
In the source affine seed chart these sections use the canonical localization
at the second weight-one coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQPairSeedSections

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CycleQ2LiteralAbelJacobiQPairSeed
  CycleQ2LiteralAbelJacobiQPairCharts CycleQ2LiteralAbelJacobiQAffineForms
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiEvaluationSeedForms
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralMovingResidueCurve
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
  CycleQ2SpecializedCurveCoordinateChart CycleQ2SeedSectionSheafCurveBinding CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap
open CycleQ2SeedConeSection (seed)

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower fixedAlgebra fixedTower reductionAlgebra fixedCurveTower

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) (W : (Curve t).Opens)
  (hW : W ≤ (pairToSeed t i k).opensRange)

abbrev seedRingMap := chartSection (pairToSeed t i k).isoOpensRange.symm (Over.mk (homOfLE hW))

theorem seedRingMap_self (a : APair t i k) :
    (pairToSeed t i k).app W (seedRingMap t i k W hW a) =
      algebraMap (APair t i k) (AffineSections (APair t i k) ((pairToSeed t i k) ⁻¹ᵁ W)) a := by
  refine chart_app (pairToSeed t i k).isoOpensRange.symm (RingHom.id (APair t i k)) (pairToSeed t i k)
    ?_ W hW a
  rw [Iso.symm_inv, Scheme.Hom.isoOpensRange_hom_ι]
  change pairToSeed t i k = Spec.map (𝟙 (CommRingCat.of (APair t i k))) ≫ pairToSeed t i k
  rw [Spec.map_id, Category.id_comp]

theorem seedRing_constants (z : ℂ) : seedRingMap t i k W hW (algebraMap ℂ (APair t i k) z) =
    coefficientOn (Curve t).sheaf (curveCoefficient t) W z := by
  apply chartSection_complex (pairToSeed t i k).isoOpensRange.symm ((curveToSurface t) ≫ projectiveToComplex 57 1)
  rw [Iso.symm_inv, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, curve_structure, pairToSeed_overBase]

include hW in
theorem seedToAffineOpen : (seedChart t i) ⁻¹ᵁ W ≤ PrimeSpectrum.basicOpen (toCurve t i (ratio i k)) := by
  have h := (seedChart t i).preimage_mono hW
  have he : (pairToSeed t i k).opensRange = _ :=
    Scheme.Hom.opensRange_comp (pairToChart i k (toCurve t i)) (seedChart t i)
  rw [he, Scheme.Hom.preimage_image_eq, pairToChart_range] at h
  exact h

private theorem range_to_chart : (pairToSeed t i k).opensRange ≤ specializedCoordinatePatch seed t i := by
  refine (Scheme.Hom.opensRange_comp (pairToChart i k (toCurve t i)) (seedChart t i)).le.trans ?_
  rw [← seedChart_opensRange t i]
  exact (seedChart t i).image_le_opensRange _

theorem seedRing_base (a : A t i) :
    seedRingMap t i k W hW (algebraMap (A t i) (APair t i k) a) =
      chartSection (specializedCoordinateAffineChart seed t i)
        (Over.mk (homOfLE (hW.trans (range_to_chart t i k)))) a := by
  apply chartSection_compatible (specializedCoordinateAffineChart seed t i)
    (pairToSeed t i k).isoOpensRange.symm (range_to_chart t i k)
    (algebraMap (A t i) (APair t i k)) _ (Over.mk (homOfLE hW)) a
  rw [Iso.symm_inv, Scheme.Hom.isoOpensRange_hom_ι]
  rfl

private theorem seedRing_chartBase (a : A t i) :
    (seedChart t i).app W (seedRingMap t i k W hW (algebraMap (A t i) (APair t i k) a)) =
      algebraMap (A t i) (AffineSections (A t i) ((seedChart t i) ⁻¹ᵁ W)) a := by
  rw [seedRing_base]
  refine chart_app (specializedCoordinateAffineChart seed t i) (RingHom.id (A t i)) (seedChart t i)
    ?_ W _ a
  change seedChart t i = Spec.map (𝟙 (CommRingCat.of (A t i))) ≫ seedChart t i
  rw [Spec.map_id, Category.id_comp]

private abbrev onDistinguished := IsLocalization.algEquiv (Submonoid.powers (toCurve t i (ratio i k)))
  (APair t i k) (AffineSections (A t i) (PrimeSpectrum.basicOpen (toCurve t i (ratio i k))))

def onAffine : APair t i k →+* AffineSections (A t i) ((seedChart t i) ⁻¹ᵁ W) :=
  (((affineScheme (A t i)).presheaf.map (homOfLE (seedToAffineOpen t i k W hW)).op).hom).comp
    (onDistinguished t i k).toRingHom

theorem onAffine_base (a : A t i) :
    onAffine t i k W hW (algebraMap (A t i) (APair t i k) a) =
      algebraMap (A t i) (AffineSections (A t i) ((seedChart t i) ⁻¹ᵁ W)) a := by
  change (affineScheme (A t i)).presheaf.map _ ((onDistinguished t i k) (algebraMap (A t i) (APair t i k) a)) = _
  rw [(onDistinguished t i k).commutes]
  rfl

theorem seedRing_in_chart :
    ((seedChart t i).app W).hom.comp (seedRingMap t i k W hW) = onAffine t i k W hW := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (toCurve t i (ratio i k)))
  apply RingHom.ext
  intro a
  change (seedChart t i).app W (seedRingMap t i k W hW (algebraMap (A t i) (APair t i k) a)) =
    (affineScheme (A t i)).presheaf.map _ ((onDistinguished t i k) (algebraMap (A t i) (APair t i k) a))
  rw [seedRing_chartBase, (onDistinguished t i k).commutes]
  rfl

theorem onAffine_constants (z : ℂ) :
    onAffine t i k W hW (algebraMap ℂ (APair t i k) z) =
      coefficientOn (Spec.structureSheaf (A t i)) (affineCoefficient (A t i)) ((seedChart t i) ⁻¹ᵁ W) z := by
  rw [← seedRing_in_chart]
  exact pulledSection_complex (seedChart t i) _ _ (seedChart_coefficient t i) W
    (seedRingMap t i k W hW) (seedRing_constants t i k W hW) z

/-- The ordinary differential on the pair, as an intrinsic one-form on the projective seed open. -/
abbrev seedOne := sectionLift (Curve t).sheaf (curveCoefficient t) (curveDifferentials t)
  (universalDifferential (Curve t).sheaf (curveCoefficient t)) W
  (seedRingMap t i k W hW) (seedRing_constants t i k W hW)

local instance seedComplexOn : Algebra ℂ Γ(Curve t,W) :=
  sectionAlgebra (Curve t).sheaf (curveCoefficient t) W

def seedPointAlg : APair t i k →ₐ[ℂ] Γ(Curve t,W) where
  toRingHom := seedRingMap t i k W hW
  commutes' := seedRing_constants t i k W hW

theorem seedOne_toSheaf (ω : KaehlerDifferential ℂ (APair t i k)) :
    letI := sectionAlgebra (Curve t).sheaf (curveCoefficient t) W
    seedOne t i k W hW ω =
      toSheaf (Curve t).sheaf (curveCoefficient t) W (differentialMap (seedPointAlg t i k W hW) ω) :=
  CycleQ2ActualCubicAdjunctionBinding.sectionLift_eq_toSheaf (Curve t).sheaf (curveCoefficient t) W
    (seedPointAlg t i k W hW) ω

theorem seedOne_chart (ω : KaehlerDifferential ℂ (APair t i k)) :
    (schemeDifferentialMap (seedChart t i) _ _ (seedChart_coefficient t i)).val.app (op W)
        (seedOne t i k W hW ω) =
      sectionLift (Spec.structureSheaf (A t i)) (affineCoefficient (A t i)) (affineDifferentialSheaf (A t i))
        (affineUniversalDifferential (A t i)) ((seedChart t i) ⁻¹ᵁ W)
        (onAffine t i k W hW) (onAffine_constants t i k W hW) ω := by
  refine (schemeDifferentialMap_sectionLift (seedChart t i) _ _ (seedChart_coefficient t i) W
    (seedRingMap t i k W hW) (seedRing_constants t i k W hW) ω).trans ?_
  have aux (f g : APair t i k →+* AffineSections (A t i) ((seedChart t i) ⁻¹ᵁ W))
      (hf : ∀ z : ℂ, f (algebraMap ℂ (APair t i k) z) =
        coefficientOn (Spec.structureSheaf (A t i)) (affineCoefficient (A t i)) ((seedChart t i) ⁻¹ᵁ W) z)
      (hg : ∀ z : ℂ, g (algebraMap ℂ (APair t i k) z) =
        coefficientOn (Spec.structureSheaf (A t i)) (affineCoefficient (A t i)) ((seedChart t i) ⁻¹ᵁ W) z)
      (h : f = g) :
      sectionLift _ _ _ (affineUniversalDifferential (A t i)) _ f hf ω =
        sectionLift _ _ _ (affineUniversalDifferential (A t i)) _ g hg ω := by
    subst g
    rfl
  exact aux _ _ _ _ (seedRing_in_chart t i k W hW)

end CycleQ2LiteralAbelJacobiQPairSeedSections
end

#print axioms CycleQ2LiteralAbelJacobiQPairSeedSections.seedOne_chart
