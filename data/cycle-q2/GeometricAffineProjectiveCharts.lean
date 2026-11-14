import Proposal.GeometricProjectiveCharts
import Proposal.GeometricDehomogenizedCharts

/-!
# The actual projective coordinate opens as the affine equation schemes

The proved dehomogenization ring equivalences are composed with Mathlib's
actual Proj affine-chart isomorphisms. Thus the affine equations used for
the local differential calculations are coordinate rings of these exact
open subschemes, for the same parameters r and theta.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricAffineProjectiveCharts

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricDehomogenizedCharts

def coordinateAffineChart (r θ : ℂ) (i : Fin 4) :
    (coordinateProjectivePatch r θ i).toScheme ≅
      Spec (CommRingCat.of (DehomogenizedRing r θ i)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveMap r θ (X i))
      (coordinate_mem_grade r θ i) (by decide) ≪≫
    Scheme.Spec.mapIso (coordinateChartEquiv r θ i).toCommRingCatIso.symm.op

def firstAffineChart (r θ : ℂ) :
    (coordinateProjectivePatch r θ 1).toScheme ≅
      Spec (CommRingCat.of (ChartRing ![firstQuadric r, firstCubic θ])) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveMap r θ (X 1))
      (coordinate_mem_grade r θ 1) (by decide) ≪≫
    Scheme.Spec.mapIso (firstChartEquiv r θ).toCommRingCatIso.symm.op

def secondAffineChart (r θ : ℂ) :
    (coordinateProjectivePatch r θ 2).toScheme ≅
      Spec (CommRingCat.of (ChartRing ![secondQuadric r, secondCubic θ])) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveMap r θ (X 2))
      (coordinate_mem_grade r θ 2) (by decide) ≪≫
    Scheme.Spec.mapIso (secondChartEquiv r θ).toCommRingCatIso.symm.op

/-- The same construction identifies the actual structure-sheaf sections. -/
def coordinateSectionsEquiv (r θ : ℂ) (i : Fin 4) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ i) ≃+*
      DehomogenizedRing r θ i :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (curveMap r θ (X i))
    (coordinate_mem_grade r θ i) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (coordinateChartEquiv r θ i)

def firstSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) ≃+*
      ChartRing ![firstQuadric r, firstCubic θ] :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (curveMap r θ (X 1))
    (coordinate_mem_grade r θ 1) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (firstChartEquiv r θ)

def secondSectionsEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) ≃+*
      ChartRing ![secondQuadric r, secondCubic θ] :=
  (Proj.basicOpenIsoAway (curveGrade r θ) (curveMap r θ (X 2))
    (coordinate_mem_grade r θ 2) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (secondChartEquiv r θ)

end CycleQ2GeometricAffineProjectiveCharts

end
