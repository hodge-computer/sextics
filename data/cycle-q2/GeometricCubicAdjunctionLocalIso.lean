import Proposal.GeometricCubicAdjunctionFrameBinding

/-!
# The actual frame-cubic contraction is a local isomorphism

The original normal frame and the established canonical sheaf isomorphism
show that contraction by the actual local surface exterior generator is
invertible on every subopen of the original Jacobian/quartic refinement.
The resulting local isomorphism has the original contraction as its map.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CubicAdjunctionLocalIso

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfacePrincipalCurveCharts
  CycleQ2GeometricSurfaceNormalCover CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricAffineChartSections CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricCanonicalSheaf CycleQ2GeometricProjectiveFrameRestriction
  CycleQ2GeometricIncidenceJacobianCover CycleQ2CurveCubicCoefficients
  CycleQ2ActualCubicAdjunctionBinding CycleQ2GlobalCubicAdjunction
  CycleQ2SurfaceExteriorFrameBinding

local instance normalSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Normal.val.obj (op W)) :=
  (Normal.val.obj (op W)).isModule

local instance differentialSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Differentials.val.obj (op W)) :=
  (Differentials.val.obj (op W)).isModule

def firstModelFrame :
    LocalFrame Curve.sheaf (degreeOneModuleSheaf 57 1) (firstProjectivePatch 57 1) :=
  twistedFirstFrame Curve.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    (overlapProjectivePatch 57 1) (overlapProjectivePatch_eq 57 1) (projectiveTransitionUnit 57 1)

def secondModelFrame :
    LocalFrame Curve.sheaf (degreeOneModuleSheaf 57 1) (secondProjectivePatch 57 1) :=
  twistedSecondFrame Curve.sheaf (firstProjectivePatch 57 1) (secondProjectivePatch 57 1)
    (overlapProjectivePatch 57 1) (overlapProjectivePatch_eq 57 1) (projectiveTransitionUnit 57 1)

def firstDifferentialEquiv (W : Curve.Opens) (hW : W ≤ firstProjectivePatch 57 1) :
    Γ(Curve, W) ≃ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  let e : (degreeOneModuleSheaf 57 1).val.obj (op W) ≃ₗ[Γ(Curve,W)] Γ(Curve,W) :=
    firstModelFrame.app W hW
  let k : (degreeOneModuleSheaf 57 1).val.obj (op W) ≃ₗ[Γ(Curve,W)]
      Differentials.val.obj (op W) :=
    ((SheafOfModules.evaluation (ringSheaf Curve.sheaf) (op W)).mapIso
      incidenceCanonicalSheafIso).toLinearEquiv
  e.symm.trans k

def secondDifferentialEquiv (W : Curve.Opens) (hW : W ≤ secondProjectivePatch 57 1) :
    Γ(Curve, W) ≃ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  let e : (degreeOneModuleSheaf 57 1).val.obj (op W) ≃ₗ[Γ(Curve,W)] Γ(Curve,W) :=
    secondModelFrame.app W hW
  let k : (degreeOneModuleSheaf 57 1).val.obj (op W) ≃ₗ[Γ(Curve,W)]
      Differentials.val.obj (op W) :=
    ((SheafOfModules.evaluation (ringSheaf Curve.sheaf) (op W)).mapIso
      incidenceCanonicalSheafIso).toLinearEquiv
  e.symm.trans k

theorem firstDifferentialEquiv_apply (W : Curve.Opens)
    (hW : W ≤ firstProjectivePatch 57 1) (a : Γ(Curve, W)) :
    firstDifferentialEquiv W hW a =
      a • Differentials.val.map (homOfLE hW).op
        (firstDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top
          second_chart_jacobianIdeal_eq_top) := by
  change incidenceCanonicalSheafIso.hom.val.app (op W)
    ((firstModelFrame.app W hW).symm a) = _
  rw [show incidenceCanonicalSheafIso.hom =
      canonicalSheafMap 57 1 (by norm_num) first_chart_jacobianIdeal_eq_top
        second_chart_jacobianIdeal_eq_top from rfl,
    canonicalSheafMap_first_local]
  change (firstModelFrame.app W hW ((firstModelFrame.app W hW).symm a)) • _ = _
  rw [LinearEquiv.apply_symm_apply]

theorem secondDifferentialEquiv_apply (W : Curve.Opens)
    (hW : W ≤ secondProjectivePatch 57 1) (a : Γ(Curve, W)) :
    secondDifferentialEquiv W hW a =
      a • Differentials.val.map (homOfLE hW).op
        (secondDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top
          second_chart_jacobianIdeal_eq_top) := by
  change incidenceCanonicalSheafIso.hom.val.app (op W)
    ((secondModelFrame.app W hW).symm a) = _
  rw [show incidenceCanonicalSheafIso.hom =
      canonicalSheafMap 57 1 (by norm_num) first_chart_jacobianIdeal_eq_top
        second_chart_jacobianIdeal_eq_top from rfl,
    canonicalSheafMap_second_local]
  change (secondModelFrame.app W hW ((secondModelFrame.app W hW).symm a)) • _ = _
  rw [LinearEquiv.apply_symm_apply]

private def firstCanonicalGenerator :
    Differentials.val.obj (op (firstProjectivePatch 57 1)) :=
  firstDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top second_chart_jacobianIdeal_eq_top

private def secondCanonicalGenerator :
    Differentials.val.obj (op (secondProjectivePatch 57 1)) :=
  secondDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top second_chart_jacobianIdeal_eq_top

private def firstCanonicalRestriction (W : Curve.Opens) (hW : W ≤ firstProjectivePatch 57 1) :
    Differentials.val.obj (op W) :=
  Differentials.val.map (homOfLE hW).op firstCanonicalGenerator

private def secondCanonicalRestriction (W : Curve.Opens) (hW : W ≤ secondProjectivePatch 57 1) :
    Differentials.val.obj (op W) :=
  Differentials.val.map (homOfLE hW).op secondCanonicalGenerator

theorem first_patchForm_frame (i : Fin 2) (j : Fin 3) (W : Curve.Opens)
    (hW : W ≤ patchOpen (.inl (i,j))) :
    (show Differentials.val.obj (op W) from patchForm firstFrameCubic (.inl (i,j)) W hW) =
      firstCanonicalRestriction W (hW.trans inf_le_right) := by
  let V : Over (firstNormalCurveOpen (57 : ℂ) 1 i j) :=
    Over.mk (homOfLE ((hW.trans inf_le_left).trans (firstNormalOpen_preimage 57 1 i j).le))
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
  have h := firstAdjunctionSection_eq 57 1 first_chart_jacobianIdeal_eq_top
    second_chart_jacobianIdeal_eq_top i j V (hW.trans inf_le_right) firstFrameCubic.val
  let f : FirstNormalCurveRing 57 1 i j →+* Γ(Curve,W) :=
    chartSection (firstNormalCurveChart 57 1 i j) V
  have hc := (firstCurveCoefficient_section 57 1 i j V firstFrameCubic.val).symm.trans
    ((congrArg f hframe).trans f.map_one)
  exact h.trans ((congrArg
    (fun z : Γ(Curve,W) => z • firstCanonicalRestriction W (hW.trans inf_le_right)) hc).trans
      (one_smul Γ(Curve,W) (firstCanonicalRestriction W (hW.trans inf_le_right))))

theorem second_patchForm_frame (i : Fin 2) (j : Fin 3) (W : Curve.Opens)
    (hW : W ≤ patchOpen (.inr (i,j))) :
    (show Differentials.val.obj (op W) from patchForm secondFrameCubic (.inr (i,j)) W hW) =
      -secondCanonicalRestriction W (hW.trans inf_le_right) := by
  let V : Over (secondNormalCurveOpen (57 : ℂ) 1 i j) :=
    Over.mk (homOfLE ((hW.trans inf_le_left).trans (secondNormalOpen_preimage 57 1 i j).le))
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
  have h := secondAdjunctionSection_eq 57 1 first_chart_jacobianIdeal_eq_top
    second_chart_jacobianIdeal_eq_top i j V (hW.trans inf_le_right) secondFrameCubic.val
  let f : SecondNormalCurveRing 57 1 i j →+* Γ(Curve,W) :=
    chartSection (secondNormalCurveChart 57 1 i j) V
  have hc := (secondCurveCoefficient_section 57 1 i j V secondFrameCubic.val).symm.trans
    ((congrArg f hframe).trans ((f.map_neg 1).trans
      (congrArg (fun z : Γ(Curve,W) => -z) f.map_one)))
  exact h.trans ((congrArg
    (fun z : Γ(Curve,W) => z • secondCanonicalRestriction W (hW.trans inf_le_right)) hc).trans
      (neg_one_smul Γ(Curve,W) (secondCanonicalRestriction W (hW.trans inf_le_right))))

def contractionEquiv (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) :
    Normal.val.obj (op W) ≃ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  match a with
  | .inl b =>
      (show Normal.val.obj (op W) ≃ₗ[Γ(Curve,W)] Γ(Curve,W) from
        (patchFrame (.inl b)).app W hW).trans
        (firstDifferentialEquiv W (hW.trans inf_le_right))
  | .inr b =>
      (show Normal.val.obj (op W) ≃ₗ[Γ(Curve,W)] Γ(Curve,W) from
        (patchFrame (.inr b)).app W hW).trans
        ((LinearEquiv.neg Γ(Curve,W) : Γ(Curve,W) ≃ₗ[Γ(Curve,W)] Γ(Curve,W)).trans
          (secondDifferentialEquiv W (hW.trans inf_le_right)))

theorem contractionEquiv_apply (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) (s : Normal.val.obj (op W)) :
    contractionEquiv a W hW s =
      (literalCubicAdjunction (frameCubic a)).val.app (op W) s := by
  rw [literalCubicAdjunction_on_patch (frameCubic a) a W hW]
  cases a with
  | inl a =>
      change firstDifferentialEquiv W (hW.trans inf_le_right)
        ((patchFrame (.inl a)).app W hW s) = _
      rw [firstDifferentialEquiv_apply]
      let c : Γ(Curve,W) := (patchFrame (.inl a)).app W hW s
      change c • firstCanonicalRestriction W (hW.trans inf_le_right) =
        c • patchForm firstFrameCubic (.inl a) W hW
      exact congrArg (fun ω : Differentials.val.obj (op W) => c • ω)
        (first_patchForm_frame a.1 a.2 W hW).symm
  | inr a =>
      change secondDifferentialEquiv W (hW.trans inf_le_right)
        (-((patchFrame (.inr a)).app W hW s)) = _
      rw [secondDifferentialEquiv_apply]
      let c : Γ(Curve,W) := (patchFrame (.inr a)).app W hW s
      change (-c) • secondCanonicalRestriction W (hW.trans inf_le_right) =
        c • patchForm secondFrameCubic (.inr a) W hW
      exact ((neg_smul c (secondCanonicalRestriction W (hW.trans inf_le_right))).trans
        (smul_neg c (secondCanonicalRestriction W (hW.trans inf_le_right))).symm).trans
          (congrArg (fun ω : Differentials.val.obj (op W) => c • ω)
            (second_patchForm_frame a.1 a.2 W hW).symm)

theorem frameCubicAdjunction_bijective (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) :
    Function.Bijective ((literalCubicAdjunction (frameCubic a)).val.app (op W)) := by
  change Function.Bijective (fun s : Normal.val.obj (op W) =>
    (literalCubicAdjunction (frameCubic a)).val.app (op W) s)
  have he : (fun s => (literalCubicAdjunction (frameCubic a)).val.app (op W) s) =
      contractionEquiv a W hW := funext (fun s => (contractionEquiv_apply a W hW s).symm)
  rw [he]
  exact (contractionEquiv a W hW).bijective

/-- The actual contraction itself, with its proved inverse on every subopen. -/
def frameCubicAdjunctionIso (a : CycleQ2GlobalCubicAdjunction.PatchIndex) :
    PatchIso Normal Differentials (patchOpen a) where
  app W hW := LinearEquiv.ofBijective
    ((literalCubicAdjunction (frameCubic a)).val.app (op W)).hom
    (frameCubicAdjunction_bijective a W hW)
  naturality hVW hW s :=
    (PresheafOfModules.naturality_apply (literalCubicAdjunction (frameCubic a)).val
      (homOfLE hVW).op s).symm

@[simp] theorem frameCubicAdjunctionIso_apply (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) (s : Normal.val.obj (op W)) :
    (frameCubicAdjunctionIso a).app W hW s =
      (literalCubicAdjunction (frameCubic a)).val.app (op W) s := rfl

#print axioms first_patchForm_frame
#print axioms second_patchForm_frame
#print axioms frameCubicAdjunction_bijective
#print axioms frameCubicAdjunctionIso

end CycleQ2CubicAdjunctionLocalIso

end
