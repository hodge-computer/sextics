import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Proposal.GeometricLiteralMovingResidueCurve
import Proposal.GeometricOpenDifferentialSheaf

/-!
# The ordinary differentials on the seed of the time family

The four affine seed charts carry the same complex structure as the
projective curve used for the residue trace. Restriction of the curve's
Kähler sheaf to each chart is its ordinary affine Kähler sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationSeedForms

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2LiteralAbelJacobiEvaluationFiber CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2SeedSectionCurveRows CycleQ2SeedSectionSheafCurveBinding
  CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricOpenDifferentialSheaf
  CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricSurfaceAdjunction
  CycleQ2SpecializedCurveCoordinateChart CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidenceFamilyContainment CycleQ2IncidenceDehomogenizedChart

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2RelativeCurveChart.pointSurfaceCommRing CycleQ2RelativeCurveChart.coordinateRingCommRing
  CycleQ2RelativeCurveChart.dehomogenizedCommRing

private theorem literalIso_toComplex :
    literalCartierProjectiveIso.hom ≫ projectiveToComplex 57 1 =
      CycleQ2GeometricIncidenceProj.surfaceToBase seed := by
  apply projectiveMap_coefficientBase literalFromCartierGraded literalOriginal_irrelevant_le_map
  ext c
  exact literalFromCartierGraded_polynomial (MvPolynomial.C c)

variable (t : Fin 3 → ℂ) (i : Fin 4)

theorem curve_structure :
    curveToSurface t ≫ projectiveToComplex 57 1 = specializedCurveToBase seed t := by
  rw [curveToSurface, Category.assoc, literalIso_toComplex]
  rfl

theorem seedChart_structure :
    seedChart t i ≫ curveToSurface t ≫ projectiveToComplex 57 1 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (A t i))) := by
  rw [curve_structure, seedChart, Category.assoc]
  exact specializedCoordinateAffineChart_overBase seed t i

theorem seedChart_coefficient (U : (specializedCurve seed t).Opens) (c : ℂ) :
    (seedChart t i).app U (coefficientOn (specializedCurve seed t).sheaf (curveCoefficient t) U c) =
      coefficientOn (Spec.structureSheaf (A t i)) (affineCoefficient (A t i)) ((seedChart t i) ⁻¹ᵁ U) c := by
  refine (coefficientOn_app (seedChart t i) (curveToSurface t ≫ projectiveToComplex 57 1) U c).trans ?_
  apply congrArg (fun φ => coefficientOn (Spec.structureSheaf (A t i)) φ _ c)
  exact (congrArg schemeCoefficient (seedChart_structure t i)).trans
    (congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism (A t i)).symm)

/-- The seed differentials in the traced class and the native affine differential model. -/
def seedChartDifferentials :
    (Scheme.Modules.restrictFunctor (seedChart t i)).obj (curveDifferentials t) ≅ affineDifferentialSheaf (A t i) :=
  openDifferentialIso (seedChart t i) _ _ (seedChart_coefficient t i)

end CycleQ2LiteralAbelJacobiEvaluationSeedForms
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationSeedForms.seedChartDifferentials
