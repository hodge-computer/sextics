import Proposal.GeometricLiteralAbelJacobiEvaluationFiberSectionsContraction
import Proposal.GeometricLiteralAbelJacobiEvaluationVelocity
import Proposal.GeometricLiteralAbelJacobiEvaluationOverlap

/-!
# Independence of the normalized velocity on an affine germ open

Sections of the first-order curve and its seed carry the complex coefficients
used by the projective differential sheaves. On each affine open, two velocities
normalized on the time parameter induce the same contraction in these rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationFiberVelocity

open AlgebraicGeometry CycleQ2FirstOrderCurve
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEvaluationOverlap
  CycleQ2LiteralAbelJacobiEvaluationFiberSections CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction
  CycleQ2LiteralAbelJacobiEvaluationVelocity CycleQ2LiteralAbelJacobiEvaluationSeedForms

attribute [local instance] CycleQ2LiteralAbelJacobiEvaluationVelocity.germAlgebra
  CycleQ2LiteralAbelJacobiEvaluationVelocity.seedSectionAlgebra
  CycleQ2LiteralAbelJacobiEvaluationVelocity.reductionOn

variable (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens)

local instance sectionTower : IsScalarTower ℂ (GermRing t W) (SeedRing t W) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := GermRing t W) (A := SeedRing t W)
    fun c => (reduction_compatible t W c).symm

private theorem seedAlgebra_eq : targetComplexAlgebra t W = seedSectionAlgebra t W := by
  apply Algebra.algebra_ext
  intro c
  change seedCoefficient t W c = CycleQ2GeometricDifferentialSheaf.coefficientOn
    (CycleQ2SpecializedProjectiveCurve.specializedCurve CycleQ2SeedConeSection.seed t).sheaf
    (CycleQ2LiteralMovingResidueAdjunction.AffineFrame.curveCoefficient t)
    (CycleQ2FirstOrderCurveSeedFiber.seedCurveToFirstOrderCurve t ⁻¹ᵁ W) c
  rw [CycleQ2LiteralMovingResidueAdjunction.AffineFrame.curveCoefficient, curve_structure]
  rfl

/-- The actual chart-section algebras with the original projective complex coefficients. -/
theorem contraction_unique (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t)
    (v w : Derivation ℂ (GermRing t W) (SeedRing t W))
    (hv : v (epsilonSection t W) = 1) (hw : w (epsilonSection t W) = 1) :
    contractRestrict v = contractRestrict w := by
  have : Subsingleton (⋀[SeedRing t W]^2 (KaehlerDifferential ℂ (SeedRing t W))) := by
    rw [← seedAlgebra_eq t W]
    exact seed_sections_exterior_two t W hW ht
  exact contract_eq_of_epsilon (epsilonSection t W) (restriction_surjective t W hW)
    (restriction_kernel t W hW) v w hv hw

end CycleQ2LiteralAbelJacobiEvaluationFiberVelocity
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationFiberVelocity.contraction_unique
