import Proposal.GeometricCubicAdjunction
import Proposal.GeometricSurfaceExteriorFrameBinding
import Proposal.GeometricSurfaceCoefficientPullback

/-!
# Actual cubic contraction in the surface exterior frame

The contraction by any original cubic surface section is the contraction
by the actual local exterior generator multiplied by that section's
actual frame coordinate pulled back along the original curve immersion.
The signs agree with the fixed first and second residue orientations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CubicAdjunctionFrameBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricAffineCurveCharts (ChartRing)
open CycleQ2GeometricLiteralSurface CycleQ2CartierProjectiveCover
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfacePrincipalCurveCharts
  CycleQ2GeometricSurfaceNormalCover CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricAffineChartSections CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2SurfaceCubicGluing CycleQ2CurveCubicCoefficients
  CycleQ2GlobalCubicAdjunction CycleQ2SurfaceExteriorFrameBinding
  CycleQ2SurfaceCoefficientPullback

local instance normalSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Normal.val.obj (op W)) :=
  (Normal.val.obj (op W)).isModule

local instance differentialSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Differentials.val.obj (op W)) :=
  (Differentials.val.obj (op W)).isModule

private theorem firstAdjunction_factor (p : WeightedCubic) (i : Fin 2) (j : Fin 3) :
    firstNormalAdjunction 57 1 i j (firstRestrictedPolynomialForm 57 1 i j p.val) =
      firstCurveCoefficient 57 1 i j p.val •
        firstNormalAdjunction 57 1 i j
          (firstRestrictedPolynomialForm 57 1 i j firstFrameCubic.val) := by
  have hframe : firstCurveCoefficient 57 1 i j firstFrameCubic.val = 1 := by
    have hpoly : firstSurfaceDehomogenize firstFrameCubic.val = 1 := by
      simp only [firstFrameCubic, map_pow, firstSurfaceDehomogenize, aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_zero, one_pow]
    change normalCoefficientMap (CycleQ2GeometricAffineCurveCharts.firstQuadric 57)
      (CycleQ2GeometricAffineCurveCharts.firstCubic 1)
      (firstSurfaceDehomogenize (CycleQ2SeedTrace.originalG1 57))
      (firstSurfaceDehomogenize CycleQ2SeedTrace.originalG2)
      (firstSurfaceDehomogenize (CycleQ2NormalConnecting.thetaK 1)) i j
      (firstSurfaceDehomogenize firstFrameCubic.val) = 1
    rw [hpoly, map_one]
  let c := firstCurveCoefficient 57 1 i j p.val
  let ω := KaehlerDifferential.map ℂ ℂ
    (ChartRing ![CycleQ2GeometricAffineCurveCharts.firstQuadric 57,
      CycleQ2GeometricAffineCurveCharts.firstCubic 1]) (FirstNormalCurveRing 57 1 i j)
    (CycleQ2GeometricChartKaehler.globalForm
      ![CycleQ2GeometricAffineCurveCharts.firstQuadric 57,
        CycleQ2GeometricAffineCurveCharts.firstCubic 1]
      CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top)
  have hf : firstNormalAdjunction 57 1 i j
      (firstRestrictedPolynomialForm 57 1 i j firstFrameCubic.val) = -ω :=
    (literal_first_normalAdjunction i j firstFrameCubic.val).trans
      ((congrArg (fun z : FirstNormalCurveRing 57 1 i j => -z • ω) hframe).trans
        (neg_one_smul (FirstNormalCurveRing 57 1 i j) ω))
  calc
    firstNormalAdjunction 57 1 i j (firstRestrictedPolynomialForm 57 1 i j p.val) =
        -c • ω := literal_first_normalAdjunction i j p.val
    _ = c • (-ω) := (neg_smul c ω).trans (smul_neg c ω).symm
    _ = c • firstNormalAdjunction 57 1 i j
        (firstRestrictedPolynomialForm 57 1 i j firstFrameCubic.val) :=
      congrArg (fun v : KaehlerDifferential ℂ (FirstNormalCurveRing 57 1 i j) => c • v) hf.symm

private theorem secondAdjunction_factor (p : WeightedCubic) (i : Fin 2) (j : Fin 3) :
    secondNormalAdjunction 57 1 i j (-(secondRestrictedPolynomialForm 57 1 i j p.val)) =
      -(secondCurveCoefficient 57 1 i j p.val) •
        secondNormalAdjunction 57 1 i j
          (-(secondRestrictedPolynomialForm 57 1 i j secondFrameCubic.val)) := by
  have hframe : secondCurveCoefficient 57 1 i j secondFrameCubic.val = -1 := by
    have hpoly : secondSurfaceDehomogenize secondFrameCubic.val = -1 := by
      simp only [secondFrameCubic, map_neg, map_pow, secondSurfaceDehomogenize,
        aeval_X]
      change -(1 : SurfacePoly) ^ 3 = -1
      rw [one_pow]
    change normalCoefficientMap (CycleQ2GeometricAffineCurveCharts.secondQuadric 57)
      (CycleQ2GeometricAffineCurveCharts.secondCubic 1)
      (secondSurfaceDehomogenize (CycleQ2SeedTrace.originalG1 57))
      (secondSurfaceDehomogenize CycleQ2SeedTrace.originalG2)
      (secondSurfaceDehomogenize (CycleQ2NormalConnecting.thetaK 1)) i j
      (secondSurfaceDehomogenize secondFrameCubic.val) = -1
    rw [hpoly, map_neg, map_one]
  let c := secondCurveCoefficient 57 1 i j p.val
  let ω := KaehlerDifferential.map ℂ ℂ
    (ChartRing ![CycleQ2GeometricAffineCurveCharts.secondQuadric 57,
      CycleQ2GeometricAffineCurveCharts.secondCubic 1]) (SecondNormalCurveRing 57 1 i j)
    (CycleQ2GeometricChartKaehler.globalForm
      ![CycleQ2GeometricAffineCurveCharts.secondQuadric 57,
        CycleQ2GeometricAffineCurveCharts.secondCubic 1]
      CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top)
  have hf : secondNormalAdjunction 57 1 i j
      (-(secondRestrictedPolynomialForm 57 1 i j secondFrameCubic.val)) = -ω :=
    (literal_second_normalAdjunction i j secondFrameCubic.val).trans
      ((congrArg (fun z : SecondNormalCurveRing 57 1 i j => z • ω) hframe).trans
        (neg_one_smul (SecondNormalCurveRing 57 1 i j) ω))
  calc
    secondNormalAdjunction 57 1 i j (-(secondRestrictedPolynomialForm 57 1 i j p.val)) =
        c • ω := literal_second_normalAdjunction i j p.val
    _ = (-c) • (-ω) := (neg_smul_neg c ω).symm
    _ = (-c) • secondNormalAdjunction 57 1 i j
        (-(secondRestrictedPolynomialForm 57 1 i j secondFrameCubic.val)) :=
      congrArg (fun v : KaehlerDifferential ℂ (SecondNormalCurveRing 57 1 i j) => (-c) • v) hf.symm

def curveCoefficient (p : WeightedCubic) (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ CycleQ2GlobalCubicAdjunction.patchOpen a) : Γ(Curve, W) :=
  match a with
  | .inl a =>
      chartSection (firstNormalCurveChart 57 1 a.1 a.2)
        (Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (firstNormalOpen_preimage 57 1 a.1 a.2).le)))
        (firstCurveCoefficient 57 1 a.1 a.2 p.val)
  | .inr a =>
      -(chartSection (secondNormalCurveChart 57 1 a.1 a.2)
        (Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (secondNormalOpen_preimage 57 1 a.1 a.2).le)))
        (secondCurveCoefficient 57 1 a.1 a.2 p.val))

theorem patchForm_factor (p : WeightedCubic) (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ CycleQ2GlobalCubicAdjunction.patchOpen a) :
    patchForm p a W hW =
      curveCoefficient p a W hW • patchForm (frameCubic a) a W hW := by
  cases a with
  | inl a =>
      let V : Over (firstNormalCurveOpen (57 : ℂ) 1 a.1 a.2) :=
        Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (firstNormalOpen_preimage 57 1 a.1 a.2).le))
      change chartKaehlerSection (firstNormalCurveChart 57 1 a.1 a.2)
        (CycleQ2GeometricDifferentialSheaf.projectiveToComplex 57 1)
        (firstNormalCurveChart_overComplex 57 1 a.1 a.2) V
        (firstNormalAdjunction 57 1 a.1 a.2
          (firstRestrictedPolynomialForm 57 1 a.1 a.2 p.val)) = _
      rw [firstAdjunction_factor]
      exact sectionLift_smul Curve.sheaf (projectiveGlobalCoefficient 57 1)
        Differentials (projectiveUniversalDifferential 57 1) W
        (chartSection (firstNormalCurveChart 57 1 a.1 a.2) V)
        (chartSection_complex _ _ (firstNormalCurveChart_overComplex 57 1 a.1 a.2) V)
        (firstCurveCoefficient 57 1 a.1 a.2 p.val)
        (firstNormalAdjunction 57 1 a.1 a.2
          (firstRestrictedPolynomialForm 57 1 a.1 a.2 firstFrameCubic.val))
  | inr a =>
      let V : Over (secondNormalCurveOpen (57 : ℂ) 1 a.1 a.2) :=
        Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (secondNormalOpen_preimage 57 1 a.1 a.2).le))
      change chartKaehlerSection (secondNormalCurveChart 57 1 a.1 a.2)
        (CycleQ2GeometricDifferentialSheaf.projectiveToComplex 57 1)
        (secondNormalCurveChart_overComplex 57 1 a.1 a.2) V
        (secondNormalAdjunction 57 1 a.1 a.2
          (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 p.val))) = _
      rw [secondAdjunction_factor]
      have h := sectionLift_smul Curve.sheaf (projectiveGlobalCoefficient 57 1)
        Differentials (projectiveUniversalDifferential 57 1) W
        (chartSection (secondNormalCurveChart 57 1 a.1 a.2) V)
        (chartSection_complex _ _ (secondNormalCurveChart_overComplex 57 1 a.1 a.2) V)
        (-(secondCurveCoefficient 57 1 a.1 a.2 p.val))
        (secondNormalAdjunction 57 1 a.1 a.2
          (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 secondFrameCubic.val)))
      change chartKaehlerSection (secondNormalCurveChart 57 1 a.1 a.2)
          (CycleQ2GeometricDifferentialSheaf.projectiveToComplex 57 1)
          (secondNormalCurveChart_overComplex 57 1 a.1 a.2) V
          (-(secondCurveCoefficient 57 1 a.1 a.2 p.val) •
            secondNormalAdjunction 57 1 a.1 a.2
              (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 secondFrameCubic.val))) =
        (chartSection (secondNormalCurveChart 57 1 a.1 a.2) V)
          (-(secondCurveCoefficient 57 1 a.1 a.2 p.val)) •
          chartKaehlerSection (secondNormalCurveChart 57 1 a.1 a.2)
            (CycleQ2GeometricDifferentialSheaf.projectiveToComplex 57 1)
            (secondNormalCurveChart_overComplex 57 1 a.1 a.2) V
            (secondNormalAdjunction 57 1 a.1 a.2
              (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 secondFrameCubic.val))) at h
      let ω : Differentials.val.obj (op W) :=
        chartKaehlerSection (secondNormalCurveChart 57 1 a.1 a.2)
          (CycleQ2GeometricDifferentialSheaf.projectiveToComplex 57 1)
          (secondNormalCurveChart_overComplex 57 1 a.1 a.2) V
          (secondNormalAdjunction 57 1 a.1 a.2
            (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 secondFrameCubic.val)))
      exact h.trans (congrArg (fun z : Γ(Curve,W) => z • ω)
        ((chartSection (secondNormalCurveChart 57 1 a.1 a.2) V).map_neg
          (secondCurveCoefficient 57 1 a.1 a.2 p.val)))

theorem surfaceCoordinate_pullback (p : WeightedCubic)
    (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (O : (projectiveSurface (57 : ℂ) 1).Opens)
    (hO : O ≤ CycleQ2SurfaceCubicGluing.patchOpen 57 1 a)
    (W : Curve.Opens) (hW : W ≤ CycleQ2GlobalCubicAdjunction.patchOpen a)
    (hWO : W ≤ curveToSurface (57 : ℂ) 1 ⁻¹ᵁ O) :
    (curveToSurface (57 : ℂ) 1).appLE O W hWO
        (frameCoordinate (exteriorFrame 57 1 a) O hO
          (localSectionOn 57 1 p.val a O hO)) =
      curveCoefficient p a W hW := by
  cases a with
  | inl a =>
      change (curveToSurface (57 : ℂ) 1).appLE O W hWO
        (frameCoordinate (firstExteriorFrame 57 1 a.1 a.2) O hO
          (localSectionOn 57 1 p.val (.inl a) O hO)) = _
      rw [first_localSection_coordinate]
      exact first_coefficient_pullback 57 1 a.1 a.2 p.val O hO W
        ((hW.trans inf_le_left).trans (firstNormalOpen_preimage 57 1 a.1 a.2).le) hWO
  | inr a =>
      change (curveToSurface (57 : ℂ) 1).appLE O W hWO
        (frameCoordinate (secondExteriorFrame 57 1 a.1 a.2) O hO
          (localSectionOn 57 1 p.val (.inr a) O hO)) = _
      rw [second_localSection_coordinate, map_neg]
      exact congrArg (fun z : Γ(Curve, W) => -z)
        (second_coefficient_pullback 57 1 a.1 a.2 p.val O hO W
          ((hW.trans inf_le_left).trans (secondNormalOpen_preimage 57 1 a.1 a.2).le) hWO)

/-- The original contraction by an arbitrary cubic is multiplication of
the frame-cubic contraction by its actual surface frame coordinate,
pulled back using the original curve immersion on the given subopens. -/
theorem contraction_formula (p : WeightedCubic)
    (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (O : (projectiveSurface (57 : ℂ) 1).Opens)
    (hO : O ≤ CycleQ2SurfaceCubicGluing.patchOpen 57 1 a)
    (W : Curve.Opens) (hW : W ≤ CycleQ2GlobalCubicAdjunction.patchOpen a)
    (hWO : W ≤ curveToSurface (57 : ℂ) 1 ⁻¹ᵁ O)
    (s : Normal.val.obj (op W)) :
    (literalCubicAdjunction p).val.app (op W) s =
      (curveToSurface (57 : ℂ) 1).appLE O W hWO
        (frameCoordinate (exteriorFrame 57 1 a) O hO
          (localSectionOn 57 1 p.val a O hO)) •
        (literalCubicAdjunction (frameCubic a)).val.app (op W) s := by
  rw [literalCubicAdjunction_on_patch p a W hW,
    literalCubicAdjunction_on_patch (frameCubic a) a W hW]
  change (show Γ(Curve,W) from (patchFrame a).app W hW s) • patchForm p a W hW =
    (show Γ(Curve,W) from (curveToSurface (57 : ℂ) 1).appLE O W hWO
      (frameCoordinate (exteriorFrame 57 1 a) O hO
        (localSectionOn 57 1 p.val a O hO))) •
      ((show Γ(Curve,W) from (patchFrame a).app W hW s) •
        patchForm (frameCubic a) a W hW)
  rw [patchForm_factor, surfaceCoordinate_pullback p a O hO W hW hWO]
  exact smul_comm _ _ _

#print axioms patchForm_factor
#print axioms surfaceCoordinate_pullback
#print axioms contraction_formula

end CycleQ2CubicAdjunctionFrameBinding

end
