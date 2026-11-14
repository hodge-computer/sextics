import Proposal.GeometricSurfaceResidueOverlap

/-!
# The third literal surface chart

The chart is x₃ ≠ 0. Its affine coordinates are
`(z,a,b,c) = ((w+x₂²)/x₃²,x₀/x₃,x₁/x₃,x₂/x₃)`.
The raw determinant residue has positive projective orientation on this chart.
All objects below are the existing literal projective surface, its original
coefficient morphism, and its actual exterior differential sheaf.

This is source-only work: verification was explicitly deferred by the user.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2ThirdSurfaceChart

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceCoefficients
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricAffineChartSections
open CycleQ2SurfaceResidueSheafOverlap CycleQ2ChartResidueTransport
open CycleQ2GeometricExteriorSheaf

abbrev thirdDehomogenize : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] SurfacePoly :=
  dehomogenize 3

/-- The normal coordinate is still the fixed equation f₂, with its actual
weight-two denominator. -/
theorem thirdDehomogenize_eq :
    thirdDehomogenize =
      aeval ![X (some 0), X (some 1), X (some 2), 1,
        X none - X (some 2) ^ 2] := by
  apply MvPolynomial.algHom_ext
  intro j
  induction j using Fin.lastCases with
  | last =>
      rw [thirdDehomogenize, dehomogenize_last]
      simp [linearCoordinate, Fin.insertNth, Fin.succAboveCases]
  | cast j =>
      rw [thirdDehomogenize, dehomogenize_castSucc]
      fin_cases j <;> simp [linearCoordinate, Fin.insertNth, Fin.succAboveCases]

abbrev thirdEquations (r θ : ℂ) : Fin 2 → SurfacePoly :=
  dehomogenizedEquations r θ 3

abbrev ThirdChartRing (r θ : ℂ) := SurfaceChartRing (thirdEquations r θ)

abbrev thirdAffineChart (r θ : ℂ) :
    (coordinatePatch r θ 3).toScheme ≅ Spec (CommRingCat.of (ThirdChartRing r θ)) :=
  CycleQ2GeometricSurfaceDehomogenizedCharts.coordinateAffineChart r θ 3

theorem thirdAffineChart_overComplex (r θ : ℂ) :
    (thirdAffineChart r θ).inv ≫ (coordinatePatch r θ 3).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ThirdChartRing r θ))) :=
  coordinateAffineChart_overComplex r θ 3

def thirdPatchOpen (r θ : ℂ) (n t : SurfacePoly) : (projectiveSurface r θ).Opens :=
  principalOpen (thirdAffineChart r θ) (augmentedJacobian (thirdEquations r θ) n t)

def thirdPatchChart (r θ : ℂ) (n t : SurfacePoly) :
    (thirdPatchOpen r θ n t).toScheme ≅
      Spec (CommRingCat.of (AdjunctionPatch (thirdEquations r θ) n t)) :=
  principalChart (thirdAffineChart r θ) (augmentedJacobian (thirdEquations r θ) n t)

theorem thirdPatchOpen_le (r θ : ℂ) (n t : SurfacePoly) :
    thirdPatchOpen r θ n t ≤ coordinatePatch r θ 3 :=
  CycleQ2GeometricPrincipalChartSections.principalOpen_le _ _

theorem thirdPatchChart_overComplex (r θ : ℂ) (n t : SurfacePoly) :
    (thirdPatchChart r θ n t).inv ≫ (thirdPatchOpen r θ n t).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (AdjunctionPatch (thirdEquations r θ) n t))) :=
  principalChart_overComplex (thirdAffineChart r θ)
    (augmentedJacobian (thirdEquations r θ) n t)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (thirdAffineChart_overComplex r θ)

/-- A polynomial coefficient times the genuine determinant residue on an
arbitrary augmented Jacobian patch of the third chart. -/
def thirdCubicSection (r θ : ℂ) (n t : SurfacePoly)
    (p : MvPolynomial (Fin 5) ℂ) (V : Over (thirdPatchOpen r θ n t)) :
    (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  chartSection (thirdPatchChart r θ n t) V
      (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations r θ) n t)
        (thirdDehomogenize p)) •
    chartResidueSheafSection
      (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
      (thirdEquations r θ) n t (thirdPatchChart r θ n t)
      (thirdPatchChart_overComplex r θ n t) V

end CycleQ2ThirdSurfaceChart

end
