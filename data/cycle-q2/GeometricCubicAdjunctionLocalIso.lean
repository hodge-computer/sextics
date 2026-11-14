/-
SOURCE-ONLY DRAFT: unverified.
Compilation and independent kernel replay were deferred at the user's request.
The proof terms below have not been accepted as a checked certificate.
-/

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
  ((firstModelFrame.app W hW).symm).trans
    (((SheafOfModules.evaluation (ringSheaf Curve.sheaf) (op W)).mapIso
      incidenceCanonicalSheafIso).toLinearEquiv)

def secondDifferentialEquiv (W : Curve.Opens) (hW : W ≤ secondProjectivePatch 57 1) :
    Γ(Curve, W) ≃ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  ((secondModelFrame.app W hW).symm).trans
    (((SheafOfModules.evaluation (ringSheaf Curve.sheaf) (op W)).mapIso
      incidenceCanonicalSheafIso).toLinearEquiv)

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

theorem first_patchForm_frame (i : Fin 2) (j : Fin 3) (W : Curve.Opens)
    (hW : W ≤ patchOpen (.inl (i,j))) :
    patchForm firstFrameCubic (.inl (i,j)) W hW =
      Differentials.val.map (homOfLE (hW.trans inf_le_right)).op
        (firstDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top
          second_chart_jacobianIdeal_eq_top) := by
  let V : Over (firstNormalCurveOpen (57 : ℂ) 1 i j) :=
    Over.mk (homOfLE ((hW.trans inf_le_left).trans (firstNormalOpen_preimage 57 1 i j).le))
  have hframe : firstCurveCoefficient 57 1 i j firstFrameCubic.val = 1 := by
    simp [firstCurveCoefficient, firstFrameCubic, firstSurfaceDehomogenize]
  have h := firstAdjunctionSection_eq 57 1 first_chart_jacobianIdeal_eq_top
    second_chart_jacobianIdeal_eq_top i j V (hW.trans inf_le_right) firstFrameCubic.val
  rw [← firstCurveCoefficient_section 57 1 i j V firstFrameCubic.val,
    hframe, map_one, one_smul] at h
  exact h

theorem second_patchForm_frame (i : Fin 2) (j : Fin 3) (W : Curve.Opens)
    (hW : W ≤ patchOpen (.inr (i,j))) :
    patchForm secondFrameCubic (.inr (i,j)) W hW =
      -(Differentials.val.map (homOfLE (hW.trans inf_le_right)).op
        (secondDenominatorFrame 57 1 first_chart_jacobianIdeal_eq_top
          second_chart_jacobianIdeal_eq_top)) := by
  let V : Over (secondNormalCurveOpen (57 : ℂ) 1 i j) :=
    Over.mk (homOfLE ((hW.trans inf_le_left).trans (secondNormalOpen_preimage 57 1 i j).le))
  have hframe : secondCurveCoefficient 57 1 i j secondFrameCubic.val = -1 := by
    simp [secondCurveCoefficient, secondFrameCubic, secondSurfaceDehomogenize]
  have h := secondAdjunctionSection_eq 57 1 first_chart_jacobianIdeal_eq_top
    second_chart_jacobianIdeal_eq_top i j V (hW.trans inf_le_right) secondFrameCubic.val
  rw [← secondCurveCoefficient_section 57 1 i j V secondFrameCubic.val,
    hframe, map_neg, map_one, neg_smul, one_smul] at h
  exact h

def contractionEquiv (a : CycleQ2GlobalCubicAdjunction.PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) :
    Normal.val.obj (op W) ≃ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  match a with
  | .inl _ => ((patchFrame a).app W hW).trans
      (firstDifferentialEquiv W (hW.trans inf_le_right))
  | .inr _ => ((patchFrame a).app W hW).trans
      ((LinearEquiv.neg Γ(Curve, W)).trans
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
      rw [firstDifferentialEquiv_apply, first_patchForm_frame]
  | inr a =>
      change secondDifferentialEquiv W (hW.trans inf_le_right)
        (-((patchFrame (.inr a)).app W hW s)) = _
      rw [secondDifferentialEquiv_apply, second_patchForm_frame]
      simp only [neg_smul, smul_neg]

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
