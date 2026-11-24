import Proposal.GeometricThreefoldMixedTimeVelocity
import Proposal.GeometricLiteralAbelJacobiEvaluationFiberVelocity
import Proposal.GeometricLiteralAbelJacobiEvaluationNormalized

/-!
# Changing the ambient velocity on a common projective affine curve open

The mixed one-form of an ambient test vector along the central curve is
independent of the normalized velocity chosen in either original projective
chart. The equality takes place in the differentials of the actual seed
sections over the common affine open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldCommonSpeed

open CategoryTheory AlgebraicGeometry CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber
  CycleQ2FirstOrderCurveCharts CycleQ2SpecializedProjectiveCurve CycleQ2SeedConeSection
  CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiEvaluationFiberSections
  CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction CycleQ2LiteralAbelJacobiEvaluationSeedForms
  CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2ThreefoldMixedTimeVelocity
  CycleQ2ThreefoldMixedCurveForm CycleQ2ThreefoldContractionAlongMap

attribute [local instance] germAlgebra seedSectionAlgebra reductionOn
  CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.sectionTower

variable (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens)

private theorem seedAlgebra_eq : targetComplexAlgebra t W = seedSectionAlgebra t W := by
  apply Algebra.algebra_ext
  intro c
  change seedCoefficient t W c = CycleQ2GeometricDifferentialSheaf.coefficientOn
    (specializedCurve seed t).sheaf
    (CycleQ2LiteralMovingResidueAdjunction.AffineFrame.curveCoefficient t)
    (seedCurveToFirstOrderCurve t ⁻¹ᵁ W) c
  rw [CycleQ2LiteralMovingResidueAdjunction.AffineFrame.curveCoefficient, curve_structure]
  rfl

private theorem affine_sections_smooth {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    [Smooth p] (V : X.Opens) (hV : IsAffineOpen V) :
    letI := (baseCoefficient p V).toAlgebra
    Algebra.Smooth ℂ Γ(X,V) := by
  let := (baseCoefficient p V).toAlgebra
  have h : Smooth (hV.fromSpec ≫ p) := inferInstance
  rw [fromSpec_baseCoefficient p hV] at h
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

/-- Smoothness for precisely the complex section algebra used by the velocity. -/
theorem seedSections_smooth (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t) :
    Algebra.Smooth ℂ (SeedRing t W) := by
  rw [← seedAlgebra_eq t W]
  let p := specializedCurveToBase seed t
  have : SmoothOfRelativeDimension 1 p :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  exact affine_sections_smooth p (seedCurveToFirstOrderCurve t ⁻¹ᵁ W)
    (hW.preimage (seedCurveToFirstOrderCurve t))

/-- The actual affine seed section algebra has vanishing exterior square. -/
theorem seedSections_exteriorTwo (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t) :
    Subsingleton (Forms (SeedRing t W) 2) := by
  change Subsingleton (⋀[SeedRing t W]^2 (KaehlerDifferential ℂ (SeedRing t W)))
  rw [← seedAlgebra_eq t W]
  exact seed_sections_exterior_two t W hW ht

variable {T : Type} [CommRing T] [Algebra ℂ T] [Algebra T (GermRing t W)] [Algebra T (SeedRing t W)]
  [IsScalarTower ℂ T (GermRing t W)] [IsScalarTower ℂ T (SeedRing t W)]
  [IsScalarTower T (GermRing t W) (SeedRing t W)]

/-- Change of speed on the first-order open for an arbitrary test tangent
along its closed curve and an arbitrary ambient three-form. -/
theorem common_speed (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t)
    (κ : Derivation ℂ T (SeedRing t W)) (v w : Derivation ℂ (GermRing t W) (SeedRing t W))
    (hvw : v (epsilonSection t W) = w (epsilonSection t W)) (ω : Forms T 3) :
    mixed κ (v.compAlgebraMap T) ω = mixed κ (w.compAlgebraMap T) ω := by
  have := seedSections_smooth t W hW ht
  have := seedSections_exteriorTwo t W hW ht
  exact mixed_eq_of_speed (epsilonSection t W) (restriction_surjective t W hW)
    (restriction_kernel t W hW) κ v w hvw ω

/-- The two original chart velocities induce the same form when the ambient
three-form and the test tangent are expressed on the common affine open. -/
theorem common_normalized (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t)
    (i j : Fin 4) (hi : W ≤ firstOrderCurveCoordinateOpen t i) (hj : W ≤ firstOrderCurveCoordinateOpen t j)
    (κ : Derivation ℂ T (SeedRing t W)) (ω : Forms T 3) :
    mixed κ ((onOpen t i (normalizedVelocity t i ht) W hi).compAlgebraMap T) ω =
      mixed κ ((onOpen t j (normalizedVelocity t j ht) W hj).compAlgebraMap T) ω := by
  apply common_speed t W hW ht
  exact (onOpen_epsilon t i _ (normalizedVelocity_epsilon t i ht) W hi).trans
    (onOpen_epsilon t j _ (normalizedVelocity_epsilon t j ht) W hj).symm

end CycleQ2LiteralThreefoldCommonSpeed
end

#print axioms CycleQ2LiteralThreefoldCommonSpeed.common_normalized
