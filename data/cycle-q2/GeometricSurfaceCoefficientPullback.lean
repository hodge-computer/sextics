/-
SOURCE-ONLY DRAFT: unverified.
Compilation and independent kernel replay were deferred at the user's request.
The proof terms below have not been accepted as a checked certificate.
-/

import Proposal.GeometricChartSectionPullback
import Proposal.GeometricSurfaceResidueOverlap

/-!
# Actual restriction of the original cubic coefficients

The surface and curve Jacobian charts form the original Cartesian square.
Consequently the actual pullback of each dehomogeneous surface coefficient
is the already defined curve coefficient on every compatible subopen.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceCoefficientPullback

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2CartierProjectiveCover CycleQ2GeometricLiteralSurface
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceNormalCover
  CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineChartSections
  CycleQ2CurveCubicCoefficients CycleQ2ChartSectionPullback

private theorem first_chart_square (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (firstNormalCurveChart r θ i j).inv ≫ (firstNormalCurveOpen r θ i j).ι ≫
        curveToSurface r θ =
      Spec.map (CommRingCat.ofHom (firstNormalCurveMap r θ i j).toRingHom) ≫
        (firstNormalChart r θ i j).inv ≫ (firstNormalOpen r θ i j).ι := by
  calc
    _ = firstNormalCurveImmersion r θ i j ≫ curveToSurface r θ := by
      rw [← Category.assoc, firstNormalCurveChart_inv_ι]
    _ = Spec.map (CommRingCat.ofHom (firstNormalCurveMap r θ i j).toRingHom) ≫
        principalImmersion (firstAffineChart r θ) (firstJacobian r θ i j) :=
      (firstNormalCurve_isPullback r θ i j).w.symm
    _ = _ := by
      change _ = _ ≫ (principalChart (firstAffineChart r θ) (firstJacobian r θ i j)).inv ≫ _
      rw [Category.assoc, principalChart_inv_ι]

private theorem second_chart_square (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    (secondNormalCurveChart r θ i j).inv ≫ (secondNormalCurveOpen r θ i j).ι ≫
        curveToSurface r θ =
      Spec.map (CommRingCat.ofHom (secondNormalCurveMap r θ i j).toRingHom) ≫
        (secondNormalChart r θ i j).inv ≫ (secondNormalOpen r θ i j).ι := by
  calc
    _ = secondNormalCurveImmersion r θ i j ≫ curveToSurface r θ := by
      rw [← Category.assoc, secondNormalCurveChart_inv_ι]
    _ = Spec.map (CommRingCat.ofHom (secondNormalCurveMap r θ i j).toRingHom) ≫
        principalImmersion (secondAffineChart r θ) (secondJacobian r θ i j) :=
      (secondNormalCurve_isPullback r θ i j).w.symm
    _ = _ := by
      change _ = _ ≫ (principalChart (secondAffineChart r θ) (secondJacobian r θ i j)).inv ≫ _
      rw [Category.assoc, principalChart_inv_ι]

theorem first_coefficient_pullback (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (p : MvPolynomial (Fin 5) ℂ)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ firstNormalOpen r θ i j)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ firstNormalCurveOpen r θ i j)
    (hWO : W ≤ curveToSurface r θ ⁻¹ᵁ O) :
    (curveToSurface r θ).appLE O W hWO
        (chartSection (firstNormalChart r θ i j) (Over.mk (homOfLE hO))
          (algebraMap SurfacePoly (FirstNormalRing r θ i j) (firstSurfaceDehomogenize p))) =
      chartSection (firstNormalCurveChart r θ i j) (Over.mk (homOfLE hW))
        (firstCurveCoefficient r θ i j p) := by
  have h := chartSection_pullback (curveToSurface r θ) (firstNormalChart r θ i j)
    (firstNormalCurveChart r θ i j) (firstNormalCurveMap r θ i j).toRingHom
    (firstNormalOpen_preimage r θ i j).ge (first_chart_square r θ i j)
    O hO W hW hWO
    (algebraMap SurfacePoly (FirstNormalRing r θ i j) (firstSurfaceDehomogenize p))
  have ha : (firstNormalCurveMap r θ i j).toRingHom
      (algebraMap SurfacePoly (FirstNormalRing r θ i j) (firstSurfaceDehomogenize p)) =
      firstCurveCoefficient r θ i j p :=
    normalAlgebraMap_polynomial (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (CycleQ2SeedTrace.originalG1 r))
      (firstSurfaceDehomogenize CycleQ2SeedTrace.originalG2)
      (firstSurfaceDehomogenize (thetaK θ)) i j (firstSurfaceDehomogenize p)
  exact h.trans (congrArg
    (chartSection (firstNormalCurveChart r θ i j) (Over.mk (homOfLE hW))) ha)

theorem second_coefficient_pullback (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (p : MvPolynomial (Fin 5) ℂ)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ secondNormalOpen r θ i j)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ secondNormalCurveOpen r θ i j)
    (hWO : W ≤ curveToSurface r θ ⁻¹ᵁ O) :
    (curveToSurface r θ).appLE O W hWO
        (chartSection (secondNormalChart r θ i j) (Over.mk (homOfLE hO))
          (algebraMap SurfacePoly (SecondNormalRing r θ i j) (secondSurfaceDehomogenize p))) =
      chartSection (secondNormalCurveChart r θ i j) (Over.mk (homOfLE hW))
        (secondCurveCoefficient r θ i j p) := by
  have h := chartSection_pullback (curveToSurface r θ) (secondNormalChart r θ i j)
    (secondNormalCurveChart r θ i j) (secondNormalCurveMap r θ i j).toRingHom
    (secondNormalOpen_preimage r θ i j).ge (second_chart_square r θ i j)
    O hO W hW hWO
    (algebraMap SurfacePoly (SecondNormalRing r θ i j) (secondSurfaceDehomogenize p))
  have ha : (secondNormalCurveMap r θ i j).toRingHom
      (algebraMap SurfacePoly (SecondNormalRing r θ i j) (secondSurfaceDehomogenize p)) =
      secondCurveCoefficient r θ i j p :=
    normalAlgebraMap_polynomial (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (CycleQ2SeedTrace.originalG1 r))
      (secondSurfaceDehomogenize CycleQ2SeedTrace.originalG2)
      (secondSurfaceDehomogenize (thetaK θ)) i j (secondSurfaceDehomogenize p)
  exact h.trans (congrArg
    (chartSection (secondNormalCurveChart r θ i j) (Over.mk (homOfLE hW))) ha)

#print axioms first_coefficient_pullback
#print axioms second_coefficient_pullback

end CycleQ2SurfaceCoefficientPullback

end
