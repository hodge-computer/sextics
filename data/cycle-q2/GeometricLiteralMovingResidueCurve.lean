import Proposal.GeometricLiteralMovingResidueAffineCurve
import Proposal.GeometricSurfaceNormalCharts
import Proposal.GeometricLiteralNativeChernCocycle
import Proposal.GeometricAffineOpenOrdinaryDifferentials
import Proposal.GeometricLiteralMovingResidueGluing

/-!
# Poincaré adjunction for the literal moving curve

Ordinary Kähler differentials of the closed curve give sections of its
pole quotient on the ambient surface. On every framed affine chart this
is the conormal wedge for the original curve ring. The composition with the
scheme's canonical pullback is the global surface residue morphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section
namespace CycleQ2LiteralMovingResidueCurve
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralMovingResidueAdjunction
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame
open CycleQ2GeometricModuleLocalIso (addSheaf)
attribute [local instance] AffineFrame.surfaceAlgebra AffineFrame.curveAlgebra

variable (t : Fin 3 → ℂ)

abbrev curveDifferentials := differentialSheaf (Curve t).sheaf (curveCoefficient t)
abbrev curveForms := addSheaf (curveDifferentials t)
abbrev imageCurveForms := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface t).base).obj (curveForms t)

/-- The actual pullback of complex one-forms along the moving closed immersion. -/
def pullbackForms : differentialAddSheaf ⟶ imageCurveForms t :=
  (SheafOfModules.toSheaf Surface.ringCatSheaf).map (schemeDifferentialMap (curveToSurface t)
    (curveCoefficient t) globalCoefficient (fun _ c => curveMap_constants t c))

theorem pullbackForms_toSheaf (W : Surface.Opens) (ω : KaehlerDifferential ℂ Γ(Surface,W)) :
    (pullbackForms t).hom.app (op W) (toSheaf Surface.sheaf globalCoefficient W ω) =
      toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W)
        (differentialMap (curveAppHom t W) ω) := by
  let f := schemeDifferentialMap (curveToSurface t) (curveCoefficient t) globalCoefficient
    (fun _ c => curveMap_constants t c)
  let m := differentialMap (curveAppHom t W)
  let d := toSheaf Surface.sheaf globalCoefficient W
  let p := toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W)
  change f.val.app (op W) (d ω) = p (m ω)
  have h : ω ∈ Submodule.span Γ(Surface,W) (Set.range (KaehlerDifferential.D ℂ Γ(Surface,W))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction h using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [show m (KaehlerDifferential.D ℂ _ x) = KaehlerDifferential.D ℂ _ ((curveToSurface t).app W x) from
      differentialMap_D (curveAppHom t W) x]
    exact schemeDifferentialMap_D (curveToSurface t) (curveCoefficient t) globalCoefficient _ W x
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [show m (r • x) = (curveToSurface t).app W r • m x from differentialMap_smul (curveAppHom t W) r x]
    exact ((congrArg (f.val.app (op W)) (d.map_smul r x)).trans
      (((f.val.app (op W)).hom.map_smul r (d x)).trans
        ((congrArg (fun y : (curveDifferentials t).val.obj (op ((curveToSurface t) ⁻¹ᵁ W)) =>
          ((curveToSurface t).app W r : SectionRing (Curve t).sheaf _) • y) hx).trans
          (p.map_smul ((curveToSurface t).app W r) (m x)).symm)))

open CycleQ2LiteralMovingResidueBasis (FramedAffine)
open CycleQ2LiteralMovingResidueExact (residueQuotient)
open CycleQ2LiteralMovingResidueGluing (surfaceResidue)
open CycleQ2LiteralMovingResidueFaces (OneForms)
open CycleQ2AffineOpenOrdinaryDifferentials (toSheaf_bijective_of_isAffineOpen)

private def nativeCurveEquiv (W : FramedAffine) :=
  LinearEquiv.ofBijective
    (toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W.carrier))
    (toSheaf_bijective_of_isAffineOpen (curveCoefficient t) _
      (W.affine.preimage (curveToSurface t)))

theorem pullbackForms_surjective (W : FramedAffine) :
    Function.Surjective ((pullbackForms t).hom.app (op W.carrier)) := by
  intro β
  obtain ⟨ω, rfl⟩ := (nativeCurveEquiv t W).surjective β
  obtain ⟨α, hα⟩ := pullback_surjective t W.affine ω
  exact ⟨toSheaf Surface.sheaf globalCoefficient W.carrier α,
    (pullbackForms_toSheaf t W.carrier α).trans
      (congrArg (toSheaf (Curve t).sheaf (curveCoefficient t) _) hα)⟩

variable (ht : ∀ i, ChartRegular t i)

private def onFramed (W : FramedAffine) :
    (imageCurveForms t).obj.obj (op W.carrier) →+ (residueQuotient t).obj.obj (op W.carrier) :=
  (curveAdjunction W.affine t ht W.frame).comp
    (nativeCurveEquiv t W).symm.toLinearMap.toAddMonoidHom

private theorem onFramed_pullback (W : FramedAffine) (β : OneForms W.carrier) :
    onFramed t ht W ((pullbackForms t).hom.app (op W.carrier) β) =
      (surfaceResidue t ht).hom.app (op W.carrier) β := by
  obtain ⟨ω,rfl⟩ := (toSheaf_bijective_of_isAffineOpen globalCoefficient W.carrier W.affine).surjective β
  rw [pullbackForms_toSheaf]
  let E := nativeCurveEquiv t W
  change curveAdjunction W.affine t ht W.frame (E.symm (E (differentialMap (curveAppHom t W.carrier) ω))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (curveAdjunction_pullback W.affine t ht W.frame ω).trans
    (CycleQ2LiteralMovingResidueGluing.surfaceResidue_basis t ht W _).symm

private theorem onFramed_restrict (W V : FramedAffine) (j : V.carrier ≤ W.carrier)
    (s : (imageCurveForms t).obj.obj (op W.carrier)) :
    onFramed t ht V ((imageCurveForms t).obj.map (homOfLE j).op s) =
      (residueQuotient t).obj.map (homOfLE j).op (onFramed t ht W s) := by
  obtain ⟨β,rfl⟩ := pullbackForms_surjective t W s
  rw [← NatTrans.naturality_apply, onFramed_pullback, onFramed_pullback, NatTrans.naturality_apply]

/-- Adjunction of ordinary Kähler forms on the actual moving Cartier curve.
The smoothness of the curve is unnecessary for the existence of this map. -/
def curveResidue : imageCurveForms t ⟶ residueQuotient t :=
  CycleQ2LiteralMovingResidueBasis.extend (onFramed t ht) (onFramed_restrict t ht)

theorem curveResidue_basis (W : FramedAffine) (ω : KaehlerDifferential ℂ (CurveRing t W.carrier)) :
    (curveResidue t ht).hom.app (op W.carrier)
      (toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W.carrier) ω) =
      curveAdjunction W.affine t ht W.frame ω := by
  rw [curveResidue, CycleQ2LiteralMovingResidueBasis.extend_apply]
  let E := nativeCurveEquiv t W
  exact congrArg (curveAdjunction W.affine t ht W.frame) (E.symm_apply_apply ω)

/-- The global surface pole class is the adjunction of the actual
scheme-theoretic restriction of the surface differential to its curve. -/
theorem pullbackForms_curveResidue : pullbackForms t ≫ curveResidue t ht = surfaceResidue t ht := by
  apply CycleQ2LiteralMovingResidueBasis.extend_unique
  intro W β
  change (curveResidue t ht).hom.app (op W.carrier) ((pullbackForms t).hom.app (op W.carrier) β) = _
  rw [curveResidue, CycleQ2LiteralMovingResidueBasis.extend_apply]
  exact (onFramed_pullback t ht W β).trans (CycleQ2LiteralMovingResidueGluing.surfaceResidue_basis t ht W β)

end CycleQ2LiteralMovingResidueCurve
end

#print axioms CycleQ2LiteralMovingResidueCurve.pullbackForms_toSheaf

#print axioms CycleQ2LiteralMovingResidueCurve.curveResidue_basis
#print axioms CycleQ2LiteralMovingResidueCurve.pullbackForms_curveResidue
