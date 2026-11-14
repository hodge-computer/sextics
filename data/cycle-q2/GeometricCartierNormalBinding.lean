import Proposal.GeometricNormalSheafComparison
import Proposal.GeometricSurfaceNormalSections
import Proposal.GeometricCartierNormalConnecting
import Proposal.GeometricGradedCechDescent

/-! Checked components of the original normalized intrinsic normal class
and its actual Cartier boundary. Every component body is retained verbatim. -/

section CheckedCartierNormalPart01

/-! The normalized source-normal frames have exactly the already glued
intrinsic direct-image coordinate vectors. Both maps retain their original
adjunction and restriction components. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2IntrinsicNormalCoordinateBinding

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalVectors CycleQ2GeometricCanonicalGluing

section General
variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  {W : X.Opens} (e : LocalFrame X.sheaf (sourceNormal j) W)

def frameImage (U : Y.Opens) (hU : j ⁻¹ᵁ U ≤ W) :
    Γ((show Y.Modules from normalDirectImageSheaf j), U) :=
  sectionEquiv j U (frameGenerator e (j ⁻¹ᵁ U) hU)

theorem frameImage_restrict {U V : Y.Opens} (hVU : V ≤ U) (hU : j ⁻¹ᵁ U ≤ W) :
    normalSectionRestrict j hVU (frameImage j e U hU) =
      frameImage j e V ((show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from fun _ hx => hVU hx).trans hU) := by
  exact (sectionEquiv_restrict j (homOfLE hVU)
    (frameGenerator e (j ⁻¹ᵁ U) hU)).symm.trans
      (congrArg (sectionEquiv j V) (frameGenerator_naturality e _ hU))

end General

open CycleQ2GeometricLiteralSurface CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricNormalCharts CycleQ2IntrinsicNormalModel
  CycleQ2NormalVectorOnCurve CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricSurfaceOverlap

private abbrev j := curveToSurface (57 : ℂ) 1

def firstFrameImage :
    Γ((show (projectiveSurface 57 1).Modules from normalDirectImageSheaf j),
      coordinatePatch 57 1 1) :=
  frameImage j firstCoordinateFrame (coordinatePatch 57 1 1)
    (coordinateCurvePreimage 57 1 (1 : Fin 4)).le

def secondFrameImage :
    Γ((show (projectiveSurface 57 1).Modules from normalDirectImageSheaf j),
      coordinatePatch 57 1 2) :=
  frameImage j secondCoordinateFrame (coordinatePatch 57 1 2)
    (coordinateCurvePreimage 57 1 (2 : Fin 4)).le

theorem firstFrameImage_eq : firstFrameImage = firstCoordinateNormalVector := by
  apply firstCoordinateNormalVector_unique
  intro p
  have hr : normalSectionRestrict j (firstNormalOpen_le 57 1 p.1 p.2) firstFrameImage =
      frameImage j firstCoordinateFrame (firstNormalOpen 57 1 p.1 p.2) (firstFamily_le p) :=
    frameImage_restrict j firstCoordinateFrame (firstNormalOpen_le 57 1 p.1 p.2)
      (coordinateCurvePreimage 57 1 (1 : Fin 4)).le
  have hg := firstCoordinateFrame_generator p (firstFamily p) le_rfl
  have hv : firstVectorAt 57 1 p.1 p.2 (firstFamily p) le_rfl =
      firstSourceNormalVector 57 1 p.1 p.2 := by
    change (actualNormal 57 1).presheaf.map (𝟙 _) _ = _
    exact ConcreteCategory.congr_hom ((actualNormal 57 1).presheaf.map_id _) _
  exact hr.trans ((congrArg (sectionEquiv j (firstNormalOpen 57 1 p.1 p.2))
    (hg.trans hv)).trans ((sectionEquiv j (firstNormalOpen 57 1 p.1 p.2)).apply_symm_apply _))

theorem secondFrameImage_eq : secondFrameImage = secondCoordinateNormalVector := by
  apply secondCoordinateNormalVector_unique
  intro p
  have hr : normalSectionRestrict j (secondNormalOpen_le 57 1 p.1 p.2) secondFrameImage =
      frameImage j secondCoordinateFrame (secondNormalOpen 57 1 p.1 p.2) (secondFamily_le p) :=
    frameImage_restrict j secondCoordinateFrame (secondNormalOpen_le 57 1 p.1 p.2)
      (coordinateCurvePreimage 57 1 (2 : Fin 4)).le
  have hg := secondCoordinateFrame_generator p (secondFamily p) le_rfl
  have hv : secondVectorAt 57 1 p.1 p.2 (secondFamily p) le_rfl =
      secondSourceNormalVector 57 1 p.1 p.2 := by
    change (actualNormal 57 1).presheaf.map (𝟙 _) _ = _
    exact ConcreteCategory.congr_hom ((actualNormal 57 1).presheaf.map_id _) _
  exact hr.trans ((congrArg (sectionEquiv j (secondNormalOpen 57 1 p.1 p.2))
    (hg.trans hv)).trans ((sectionEquiv j (secondNormalOpen 57 1 p.1 p.2)).apply_symm_apply _))

theorem firstFrameImage_subopen (U : (projectiveSurface 57 1).Opens)
    (hU : U ≤ coordinatePatch 57 1 1) :
    frameImage j firstCoordinateFrame U
        ((show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ coordinatePatch 57 1 1 from fun _ hx => hU hx).trans
          (coordinateCurvePreimage 57 1 (1 : Fin 4)).le) =
      normalSectionRestrict j hU firstCoordinateNormalVector := by
  exact (frameImage_restrict j firstCoordinateFrame hU
    (coordinateCurvePreimage 57 1 (1 : Fin 4)).le).symm.trans
      (congrArg (normalSectionRestrict j hU) firstFrameImage_eq)

theorem secondFrameImage_subopen (U : (projectiveSurface 57 1).Opens)
    (hU : U ≤ coordinatePatch 57 1 2) :
    frameImage j secondCoordinateFrame U
        ((show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ coordinatePatch 57 1 2 from fun _ hx => hU hx).trans
          (coordinateCurvePreimage 57 1 (2 : Fin 4)).le) =
      normalSectionRestrict j hU secondCoordinateNormalVector := by
  exact (frameImage_restrict j secondCoordinateFrame hU
    (coordinateCurvePreimage 57 1 (2 : Fin 4)).le).symm.trans
      (congrArg (normalSectionRestrict j hU) secondFrameImage_eq)

end CycleQ2IntrinsicNormalCoordinateBinding
end

end CheckedCartierNormalPart01

section CheckedCartierNormalPart02

/-! The genuine internal-Hom adjunction preserves arbitrary coefficients
on the curve preimage, through the pointwise coefficient action on the
intrinsic normal direct image. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalImageCoefficients

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricIntrinsicNormal CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalVectors

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

theorem sectionEquiv_curve_smul (U : Y.Opens) (a : Γ(X, j ⁻¹ᵁ U))
    (f : Γ(sourceNormal j, j ⁻¹ᵁ U)) :
    sectionEquiv j U (a • f) = normalImageScalar j U a (sectionEquiv j U f) := by
  apply localLinearHom_ext Y.sheaf (kernelIdealSheaf j) (imageStructureModule j)
  intro V m
  rfl

theorem sectionEquiv_symm_curve_smul (U : Y.Opens) (a : Γ(X, j ⁻¹ᵁ U))
    (f : Γ((show Y.Modules from normalDirectImageSheaf j), U)) :
    (sectionEquiv j U).symm (normalImageScalar j U a f) =
      a • (sectionEquiv j U).symm f := by
  apply (sectionEquiv j U).injective
  exact ((sectionEquiv j U).apply_symm_apply _).trans
    ((sectionEquiv_curve_smul j U a ((sectionEquiv j U).symm f)).trans
      (congrArg (normalImageScalar j U a) ((sectionEquiv j U).apply_symm_apply f))).symm

/-- The canonical section comparison is linear over the actual curve
section ring; its forward and inverse maps remain the original adjunction. -/
def sectionLinearEquiv (U : Y.Opens) :
    letI := normalImageModule j U
    Γ(sourceNormal j, j ⁻¹ᵁ U) ≃ₗ[Γ(X, j ⁻¹ᵁ U)]
      (normalDirectImageSheaf j).val.obj (op U) := by
  letI := normalImageModule j U
  let e : Γ(sourceNormal j, j ⁻¹ᵁ U) ≃+ (normalDirectImageSheaf j).val.obj (op U) :=
    sectionEquiv j U
  exact e.toLinearEquiv (sectionEquiv_curve_smul j U)

@[simp] theorem sectionLinearEquiv_apply (U : Y.Opens)
    (f : Γ(sourceNormal j, j ⁻¹ᵁ U)) :
    sectionLinearEquiv j U f = sectionEquiv j U f := rfl

end CycleQ2NormalImageCoefficients
end

end CheckedCartierNormalPart02

section CheckedCartierNormalPart03

/-! The unchanged original normal overlap section has the original
degree-zero fraction as coefficient in the normalized intrinsic frame.
The formula uses the actual adjunction and restriction maps. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2IntrinsicOverlapCoordinates

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveCurve
  CycleQ2ProjectiveCurveSurface CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricCanonicalGluing CycleQ2GeometricProjectiveAffine
  CycleQ2NormalVectorOnCurve CycleQ2SourceNormalSheaf
  CycleQ2SourceNormalVectors CycleQ2GeometricIntrinsicNormal
  CycleQ2IntrinsicNormalModel CycleQ2IntrinsicNormalBoundary
  CycleQ2IntrinsicNormalCoordinateBinding CycleQ2NormalImageCoefficients
  CycleQ2SurfaceNormalTransport CycleQ2SurfaceNormalCohomology
  CycleQ2ClosedSupportCohomology CycleQ2SeedTrace

private abbrev C := projectiveCurve (57 : ℂ) 1
private abbrev j := curveToSurface (57 : ℂ) 1
private abbrev O := overlapProjectivePatch (57 : ℂ) 1
private abbrev N := actualNormal (57 : ℂ) 1

local instance normalSectionModule (W : C.Opens) :
    Module Γ(C, W) (N.val.obj (op W)) := (N.val.obj (op W)).isModule

theorem overlap_le_first : O ≤ firstProjectivePatch 57 1 :=
  (overlapProjectivePatch_eq 57 1).le.trans inf_le_left

theorem overlap_le_first_coordinate : O ≤ coordinateProjectivePatch 57 1 1 :=
  overlap_le_first.trans (firstProjectivePatch_le_firstCoordinate 57 1)

def overlapCoefficient (p : Poly) (hp : p.IsHomogeneous 6) : Γ(C, O) :=
  (overlapProjectiveSectionsIso 57 1).hom (normalOverlapCoordinate 57 1 p hp)

theorem inverseNormalOverlapSection (p : Poly) (hp : p.IsHomogeneous 6) :
    intrinsicNormalIso.inv.app O (normalOverlapSection 57 1 p hp) =
      overlapCoefficient p hp • frameGenerator firstCoordinateFrame O
        overlap_le_first_coordinate := by
  let x := normalOverlapSection 57 1 p hp
  have hi : intrinsicNormalIso.hom.app O (intrinsicNormalIso.inv.app O x) = x :=
    ConcreteCategory.congr_hom
      (congrArg (fun f => f.app O) intrinsicNormalIso.inv_hom_id) x
  have hc := intrinsicNormalIso_first O overlap_le_first (intrinsicNormalIso.inv.app O x)
  change firstModelCoordinate O overlap_le_first
      (intrinsicNormalIso.hom.app O (intrinsicNormalIso.inv.app O x)) = _ at hc
  rw [hi] at hc
  have hvalue : firstQuarticFrame.app O overlap_le_first
      (intrinsicNormalIso.inv.app O x) = overlapCoefficient p hp :=
    hc.symm.trans ((normalOverlapFrame 57 1).apply_symm_apply _)
  let e := firstQuarticFrame.app O overlap_le_first
  have hback : intrinsicNormalIso.inv.app O x = e.symm (overlapCoefficient p hp) :=
    (e.symm_apply_apply _).symm.trans (congrArg e.symm hvalue)
  have hs := e.symm.map_smul (overlapCoefficient p hp) (1 : Γ(C, O))
  change e.symm (overlapCoefficient p hp * (1 : Γ(C, O))) =
    overlapCoefficient p hp • e.symm (1 : Γ(C, O)) at hs
  rw [mul_one] at hs
  exact hback.trans hs

theorem inverseNormalOverlapSection_subopen (W : C.Opens) (hW : W ≤ O)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    intrinsicNormalIso.inv.app W
        ((normalModuleSheaf 57 1).val.map (homOfLE hW).op
          (normalOverlapSection 57 1 p hp)) =
      C.presheaf.map (homOfLE hW).op (overlapCoefficient p hp) •
        frameGenerator firstCoordinateFrame W (hW.trans overlap_le_first_coordinate) := by
  have hn := ConcreteCategory.congr_hom
    (intrinsicNormalIso.inv.mapPresheaf.naturality (homOfLE hW).op)
      (normalOverlapSection 57 1 p hp)
  change intrinsicNormalIso.inv.app W
      ((normalModuleSheaf 57 1).val.map (homOfLE hW).op
        (normalOverlapSection 57 1 p hp)) =
    N.val.map (homOfLE hW).op
      (intrinsicNormalIso.inv.app O (normalOverlapSection 57 1 p hp)) at hn
  rw [inverseNormalOverlapSection] at hn
  have hs := sectionRes_smul N hW (overlapCoefficient p hp)
    (frameGenerator firstCoordinateFrame O overlap_le_first_coordinate)
  have hg := frameGenerator_naturality firstCoordinateFrame hW overlap_le_first_coordinate
  exact hn.trans (hs.trans (congrArg
    (fun n : Γ(N, W) => C.presheaf.map (homOfLE hW).op (overlapCoefficient p hp) • n) hg))

/-- The inverse sheaf isomorphism acts through the genuine normal
adjunction, after the original inverse normal-model map. -/
theorem surfaceNormalAdditiveIso_inv_app (U : (projectiveSurface 57 1).Opens)
    (x : (pushedNormalSheaf 57 1).obj.obj (op U)) :
    (surfaceNormalAdditiveIso 57 1 intrinsicNormalIso).inv.hom.app (op U) x =
      sectionEquiv j U (intrinsicNormalIso.inv.app (j ⁻¹ᵁ U) x) := rfl

theorem modelOverlapSection_restrict (U : (projectiveSurface 57 1).Opens)
    (hU : U ≤ normalTargetOverlap 57 1) (hpre : j ⁻¹ᵁ U ≤ O)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    (pushedNormalSheaf 57 1).obj.map (homOfLE hU).op
        (modelOverlapSection 57 1 p hp) =
      (normalAdditiveSheaf 57 1).obj.map (homOfLE hpre).op
        (normalOverlapSection 57 1 p hp) := by
  let F := normalAdditiveSheaf 57 1
  have hstart : sectionsEq F
      (preimage_extendedOpen j.base (curveClosedEmbedding 57 1) O)
      (modelOverlapSection 57 1 p hp) = normalOverlapSection 57 1 p hp :=
    (pushedSectionsEquiv j.base (curveClosedEmbedding 57 1) F O).apply_symm_apply _
  have hr := sectionsEq_restrict F
    (preimage_extendedOpen j.base (curveClosedEmbedding 57 1) O)
    (rfl : j ⁻¹ᵁ U = j ⁻¹ᵁ U)
    (show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ normalTargetOverlap 57 1 from fun _ hx => hU hx)
    hpre (modelOverlapSection 57 1 p hp)
  have hi : sectionsEq F (rfl : j ⁻¹ᵁ U = j ⁻¹ᵁ U)
      ((pushedNormalSheaf 57 1).obj.map (homOfLE hU).op
        (modelOverlapSection 57 1 p hp)) =
      (pushedNormalSheaf 57 1).obj.map (homOfLE hU).op
        (modelOverlapSection 57 1 p hp) :=
    ConcreteCategory.congr_hom (F.obj.map_id _) _
  exact hi.symm.trans (hr.trans
    (congrArg (F.obj.map (homOfLE hpre).op) hstart))

theorem intrinsicOverlapSection_restrict (U : (projectiveSurface 57 1).Opens)
    (hU : U ≤ normalTargetOverlap 57 1) (hpre : j ⁻¹ᵁ U ≤ O)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    normalSectionRestrict j hU
        (intrinsicOverlapSection 57 1 intrinsicNormalIso p hp) =
      normalImageScalar j U
        (C.presheaf.map (homOfLE hpre).op (overlapCoefficient p hp))
        (frameImage j firstCoordinateFrame U (hpre.trans overlap_le_first_coordinate)) := by
  have hn : sectionEquiv j U (intrinsicNormalIso.inv.app (j ⁻¹ᵁ U)
        ((pushedNormalSheaf 57 1).obj.map (homOfLE hU).op
          (modelOverlapSection 57 1 p hp))) =
      normalSectionRestrict j hU
        (intrinsicOverlapSection 57 1 intrinsicNormalIso p hp) :=
    ConcreteCategory.congr_hom
      ((surfaceNormalAdditiveIso 57 1 intrinsicNormalIso).inv.hom.naturality
        (homOfLE hU).op) (modelOverlapSection 57 1 p hp)
  have hm := congrArg
    (fun x : (normalModuleSheaf 57 1).val.obj (op (j ⁻¹ᵁ U)) =>
      sectionEquiv j U (intrinsicNormalIso.inv.app (j ⁻¹ᵁ U) x))
    (modelOverlapSection_restrict U hU hpre p hp)
  have hv := congrArg (sectionEquiv j U)
    (inverseNormalOverlapSection_subopen (j ⁻¹ᵁ U) hpre p hp)
  exact hn.symm.trans (hm.trans (hv.trans (sectionEquiv_curve_smul j U _ _)))

theorem productOverlapPreimage : j ⁻¹ᵁ coverPatch 57 1 {0, 1} = O := by
  rw [coverPatch_pair, Scheme.Hom.preimage_inf,
    curveToSurface_preimage_cover_zero, curveToSurface_preimage_cover_one]
  exact (overlapProjectivePatch_eq 57 1).symm

theorem productOverlap_le_target : coverPatch 57 1 {0, 1} ≤ normalTargetOverlap 57 1 :=
  (CycleQ2CechOneMayerVietoris.le_extendedOpen_iff j.base
    (curveClosedEmbedding 57 1) (coverPatch 57 1 {0, 1}) O).mpr productOverlapPreimage.le

/-- On the actual product patch, the original normal section has precisely
the original normalOverlapCoordinate coefficient in the fixed intrinsic frame. -/
theorem intrinsicOverlapSection_product (p : Poly) (hp : p.IsHomogeneous 6) :
    normalSectionRestrict j productOverlap_le_target
        (intrinsicOverlapSection 57 1 intrinsicNormalIso p hp) =
      normalImageScalar j (coverPatch 57 1 {0, 1})
        (C.presheaf.map (homOfLE productOverlapPreimage.le).op (overlapCoefficient p hp))
        (frameImage j firstCoordinateFrame (coverPatch 57 1 {0, 1})
          (productOverlapPreimage.le.trans overlap_le_first_coordinate)) :=
  intrinsicOverlapSection_restrict (coverPatch 57 1 {0, 1})
    productOverlap_le_target productOverlapPreimage.le p hp

end CycleQ2IntrinsicOverlapCoordinates
end

end CheckedCartierNormalPart03

section CheckedCartierNormalPart04

/-! The degree-zero lift is compared with the fixed intrinsic normal
frame using actual equation values.  The coordinate refinement is only
used along the closed curve; it is not asserted to cover the surface. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProjectiveInverseIdealReduction

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial HomogeneousLocalization CycleQ2GradedLocalizationProjection
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierHomogeneousCech CycleQ2CartierProjectiveCover
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricNormalCharts
open CycleQ2GeometricLiteralSurface (curveGradedMap curveToSurface)
open CycleQ2ProjectiveInverseIdeal

section Restriction

open CycleQ2SourceNormalSheaf CycleQ2SourceNormalVectors

/-- A direct-image normal section is detected after any restriction
which leaves its actual curve preimage unchanged. -/
theorem normalRestriction_injective {X Y : Scheme.{0}} (j : X ⟶ Y)
    {U V : Y.Opens} (h : V ⟶ U) (he : j ⁻¹ᵁ V = j ⁻¹ᵁ U) :
    Function.Injective ((normalDirectImageSheaf j).val.map h.op) := by
  have hi : Function.Injective
      ((sourceNormal j).presheaf.map ((Opens.map j.base).map h).op) := by
    have hm : ((Opens.map j.base).map h).op = (eqToIso he).hom.op :=
      Subsingleton.elim _ _
    rw [hm]
    exact (((sourceNormal j).presheaf.mapIso (eqToIso he).op).addCommGroupIsoToAddEquiv).injective
  intro a b hab
  apply (sectionEquiv j U).symm.injective
  apply hi
  exact (sectionEquiv_symm_restrict j h a).symm.trans
    ((congrArg (sectionEquiv j V).symm hab).trans (sectionEquiv_symm_restrict j h b))

end Restriction

section FractionAlgebra

variable {R : Type*} [CommRing R]

private theorem equation_fraction_identity (s x p a m q : R)
    (hs : IsUnit s) (hx : IsUnit x)
    (ha : a * s = p * x ^ 6) (hm : m * s = x ^ 8) (hq : q * x ^ 2 = p) :
    a = m * q := by
  apply (hs.mul (hx.pow 2)).mul_right_cancel
  calc
    a * (s * x ^ 2) = (a * s) * x ^ 2 := by ring
    _ = (p * x ^ 6) * x ^ 2 := congrArg (fun y => y * x ^ 2) ha
    _ = x ^ 8 * p := by ring
    _ = (m * s) * (q * x ^ 2) := by rw [hm, hq]
    _ = (m * q) * (s * x ^ 2) := by ring

private theorem value_fraction_identity (s x n g v m c q : R)
    (hs : IsUnit s) (hx : IsUnit x)
    (hv : v * s ^ 2 = n * g * x ^ 6) (hm : m * s = x ^ 8)
    (hc : c * s = n * x ^ 2) (hq : q * x ^ 4 = g) :
    v = m * c * q := by
  apply ((hs.pow 2).mul (hx.pow 4)).mul_right_cancel
  calc
    v * (s ^ 2 * x ^ 4) = (v * s ^ 2) * x ^ 4 := by ring
    _ = (n * g * x ^ 6) * x ^ 4 := congrArg (fun y => y * x ^ 4) hv
    _ = x ^ 8 * (n * x ^ 2) * g := by ring
    _ = (m * s) * (c * s) * (q * x ^ 4) := by rw [hm, hc, hq]
    _ = (m * c * q) * (s ^ 2 * x ^ 4) := by ring

end FractionAlgebra

section Algebra

/-- The canonical homogeneous affine section equivalence, with the
actual surface section ring written explicitly. -/
def projectiveSectionRingEquiv (r θ : ℂ) (s : SurfaceRing r θ) {d : ℕ}
    (hs : s ∈ surfaceGrade r θ d) (hd : 0 < d) :
    Away (surfaceGrade r θ) s ≃+*
      Γ(projectiveSurface r θ, Proj.basicOpen (surfaceGrade r θ) s) :=
  CycleQ2GeometricLiteralSurface.projChartSectionsEquiv (surfaceGrade r θ) s hs hd

private theorem x1_homogeneous :
    (X (1 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (1 : Fin 5)

private theorem overlapDegree : coverProductDegree {0,1} = 8 := by decide

/-- The unaltered degree-zero coefficient of the original normal lift. -/
def connectingCoefficient : HomogeneousCoverLocal 57 1 {0,1} :=
  Away.mk (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
    (surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2)) (by
      simpa [overlapDegree] using
        surfaceQuotient_mem_grade 57 1 (derivativeA_homogeneous.neg.mul (x1_homogeneous.pow 2)))

/-- This coefficient becomes a unit on the first-coordinate refinement. -/
def coordinateMultiplier : HomogeneousCoverLocal 57 1 {0,1} :=
  Away.mk (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
    (surfaceQuotient 57 1 (X 1 ^ 8)) (by
      simpa [overlapDegree] using
        surfaceQuotient_mem_grade 57 1 (x1_homogeneous.pow 8))

/-- A genuine degree-zero ideal element whose equation survives in the
conormal quotient.  No power of the defining equation is used. -/
def equationTest (i : Fin 2) :
    HomogeneousCurveIdeal 57 1 {0,1} :=
  ⟨Away.mk (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
    (surfaceQuotient 57 1 (coordinateEquationPolynomial 57 i * X 1 ^ 6)) (by
      simpa [overlapDegree] using surfaceQuotient_mem_grade 57 1
        ((coordinateEquationPolynomial_homogeneous 57 i).mul (x1_homogeneous.pow 6))), by
    have hz : curveGradedMap 57 1
        (surfaceQuotient 57 1 (coordinateEquationPolynomial 57 i)) = 0 := by
      rcases normalIndex_cases i with rfl | rfl
      · exact ambientCurveMap_f1 57 1
      · exact ambientCurveMap_f2 57 1
    apply HomogeneousLocalization.val_injective
    simp only [Away.map_mk, Away.val_mk,
      map_mul, hz, zero_mul, Localization.mk_zero, HomogeneousLocalization.val_zero]⟩

/-- The exact degree-zero value of the original cone functional on the
test equation. -/
def equationValue (i : Fin 2) : HomogeneousCoverLocal 57 1 {0,1} :=
  Away.mk (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 2
    (surfaceQuotient 57 1
      ((-derivativeA * normalCoefficientPolynomial 57 i) * X 1 ^ 6)) (by
        simpa [overlapDegree] using surfaceQuotient_mem_grade 57 1
          ((derivativeA_homogeneous.neg.mul (normalCoefficientPolynomial_homogeneous 57 i)).mul
            (x1_homogeneous.pow 6)))

theorem fraction_mul_denominator {R σ : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {s : R} {d : ℕ} (hs : s ∈ 𝒜 d) (n : ℕ) (p : R) (hp : p ∈ 𝒜 (n • d)) :
    (Away.mk 𝒜 hs n p hp).val *
      algebraMap R (Localization.Away s) (s ^ n) =
        algebraMap R (Localization.Away s) p := by
  simpa only [Away.val_mk, Localization.mk_eq_mk', powerDenominator] using
    (IsLocalization.mk'_spec (Localization.Away s) p (powerDenominator s n))

theorem connectingCoefficient_mul_denominator :
    connectingCoefficient.val *
      algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1}) =
        overlapPolyMap 57 1 (-derivativeA * X 1 ^ 2) := by
  simpa only [connectingCoefficient, pow_one, overlapPolyMap, RingHom.comp_apply] using
    fraction_mul_denominator (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
      (surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2)) _

theorem coordinateMultiplier_mul_denominator :
    coordinateMultiplier.val *
      algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1}) =
        overlapPolyMap 57 1 (X 1 ^ 8) := by
  simpa only [coordinateMultiplier, pow_one, overlapPolyMap, RingHom.comp_apply] using
    fraction_mul_denominator (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
      (surfaceQuotient 57 1 (X 1 ^ 8)) _

theorem equationTest_mul_denominator (i : Fin 2) :
    (equationTest i : HomogeneousCoverLocal 57 1 {0,1}).val *
      algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1}) =
        overlapPolyMap 57 1 (coordinateEquationPolynomial 57 i * X 1 ^ 6) := by
  simpa only [equationTest, pow_one, overlapPolyMap, RingHom.comp_apply] using
    fraction_mul_denominator (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 1
      (surfaceQuotient 57 1 (coordinateEquationPolynomial 57 i * X 1 ^ 6)) _

theorem equationValue_mul_denominator (i : Fin 2) :
    (equationValue i).val *
      (algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1})) ^ 2 =
        overlapPolyMap 57 1 ((-derivativeA * normalCoefficientPolynomial 57 i) * X 1 ^ 6) := by
  simpa only [equationValue, map_pow, overlapPolyMap, RingHom.comp_apply] using
    fraction_mul_denominator (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1}) 2
      (surfaceQuotient 57 1 ((-derivativeA * normalCoefficientPolynomial 57 i) * X 1 ^ 6)) _

/-- The original two inverse factors combine to the actual overlap
product, with the original negative numerator retained. -/
theorem surfaceNormalCoefficient_mul_denominator :
    surfaceNormalCoefficient 57 1 derivativeA 0 *
      algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1}) =
        -overlapPolyMap 57 1 derivativeA := by
  have hd : algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1)
      (coverProduct 57 1 {0,1}) =
        (coverUnit 57 1 {0,1} 0 (by simp) : SurfaceOverlap 57 1) *
          (coverUnit 57 1 {0,1} 1 (by simp) : SurfaceOverlap 57 1) := by
    have hu0 : (coverUnit 57 1 {0,1} 0 (by simp) : SurfaceOverlap 57 1) =
        algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1)
          (surfaceQuotient 57 1 (originalG1 57)) := coverUnit_value 57 1 {0,1} 0 (by simp)
    have hu1 : (coverUnit 57 1 {0,1} 1 (by simp) : SurfaceOverlap 57 1) =
        algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1)
          (surfaceQuotient 57 1 originalG2) := coverUnit_value 57 1 {0,1} 1 (by simp)
    exact (congrArg (algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1))
      (coverProduct_pair 57 1)).trans
        ((map_mul (algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1)) _ _).trans
          (congrArg₂ (fun x y : SurfaceOverlap 57 1 => x * y) hu0.symm hu1.symm))
  rw [surfaceNormalCoefficient, map_zero, mul_zero, zero_sub, hd]
  calc
    _ = -overlapPolyMap 57 1 derivativeA *
        ((↑((coverUnit 57 1 {0,1} 0 (by simp))⁻¹) : SurfaceOverlap 57 1) *
          (coverUnit 57 1 {0,1} 0 (by simp) : SurfaceOverlap 57 1)) *
        ((↑((coverUnit 57 1 {0,1} 1 (by simp))⁻¹) : SurfaceOverlap 57 1) *
          (coverUnit 57 1 {0,1} 1 (by simp) : SurfaceOverlap 57 1)) := by ring
    _ = _ := by rw [Units.inv_mul, Units.inv_mul, mul_one, mul_one]

private theorem overlapEquation_value (i : Fin 2) :
    (overlapEquation 57 1 i.castSucc : SurfaceOverlap 57 1) =
      overlapPolyMap 57 1 (coordinateEquationPolynomial 57 i) := by
  rcases normalIndex_cases i with rfl | rfl <;> rfl

private theorem kernelVector_value (i : Fin 2) :
    kernelVector (overlapPolyMap 57 1 (originalG1 57))
      (overlapPolyMap 57 1 originalG2) i.castSucc =
        overlapPolyMap 57 1 (normalCoefficientPolynomial 57 i) := by
  rcases normalIndex_cases i with rfl | rfl
  · rfl
  · exact (map_neg (overlapPolyMap 57 1) (originalG1 57)).symm

/-- The cone functional on these genuine first-order equation tests is
already homogeneous of degree zero, with the exact displayed value. -/
def equationConeElement (i : Fin 2) : overlapCurveIdeal 57 1 :=
  contractedIdealVal (surfaceGrade 57 1) _
    (homogeneousCurveIdealToContracted 57 1 {0,1} (equationTest i))

theorem connectingLift_cone_equation (i : Fin 2) :
    inverseIdealConnectingLift 57 1 derivativeA 0 (equationConeElement i) =
      (equationValue i).val := by
  let d : SurfaceOverlap 57 1 :=
    algebraMap (SurfaceRing 57 1) (SurfaceOverlap 57 1) (coverProduct 57 1 {0,1})
  let a := equationConeElement i
  let φ := inverseIdealConnectingLift 57 1 derivativeA 0
  have he : d • a = overlapPolyMap 57 1 (X 1 ^ 6) • overlapEquation 57 1 i.castSucc := by
    apply Subtype.ext
    change d * (equationTest i : HomogeneousCoverLocal 57 1 {0,1}).val =
      overlapPolyMap 57 1 (X 1 ^ 6) * (overlapEquation 57 1 i.castSucc : SurfaceOverlap 57 1)
    rw [mul_comm, equationTest_mul_denominator, map_mul, overlapEquation_value, mul_comm]
  have hv := congrArg φ he
  rw [map_smul, map_smul, inverseIdealConnectingLift_equation, kernelVector_value] at hv
  change d * φ a = overlapPolyMap 57 1 (X 1 ^ 6) *
    (surfaceNormalCoefficient 57 1 derivativeA 0 *
      overlapPolyMap 57 1 (normalCoefficientPolynomial 57 i)) at hv
  have hd : IsUnit d := IsLocalization.Away.algebraMap_isUnit
    (S := SurfaceOverlap 57 1) (coverProduct 57 1 {0,1})
  apply (hd.pow 2).mul_right_cancel
  change φ a * d ^ 2 = (equationValue i).val * d ^ 2
  calc
    _ = (d * φ a) * d := by ring
    _ = (overlapPolyMap 57 1 (X 1 ^ 6) *
        (surfaceNormalCoefficient 57 1 derivativeA 0 *
          overlapPolyMap 57 1 (normalCoefficientPolynomial 57 i))) * d :=
      congrArg (fun x : SurfaceOverlap 57 1 => x * d) hv
    _ = (surfaceNormalCoefficient 57 1 derivativeA 0 * d) *
        overlapPolyMap 57 1 (normalCoefficientPolynomial 57 i) *
          overlapPolyMap 57 1 (X 1 ^ 6) := by ring
    _ = -overlapPolyMap 57 1 derivativeA *
        overlapPolyMap 57 1 (normalCoefficientPolynomial 57 i) *
          overlapPolyMap 57 1 (X 1 ^ 6) := by rw [surfaceNormalCoefficient_mul_denominator]
    _ = overlapPolyMap 57 1
        ((-derivativeA * normalCoefficientPolynomial 57 i) * X 1 ^ 6) := by
      rw [map_mul, map_mul, map_neg]
    _ = _ := (equationValue_mul_denominator i).symm

/-- Projection does not alter the actual equation values. -/
theorem literalProjectedConnectingLift_equation (i : Fin 2) :
    literalProjectedConnectingLift (equationTest i) = equationValue i := by
  change CycleQ2GradedLocalizationProjection.degreeZero (surfaceGrade 57 1)
    (coverProduct_mem_grade 57 1 {0,1})
    (inverseIdealConnectingLift 57 1 derivativeA 0 (equationConeElement i)) = equationValue i
  rw [connectingLift_cone_equation]
  exact CycleQ2GradedLocalizationProjection.degreeZero_val _ _ _

/-- The genuine projective inverse-ideal section has the original
first-order equation values in the canonical section ring. -/
theorem connectingLift_evaluate_equation (i : Fin 2) :
    inverseIdealSectionEvaluate (curveToSurface 57 1) (coverPatch 57 1 {0,1})
      literalConnectingEdge
      (coverIdealSection 57 1 {0,1} (by simp) (equationTest i)) =
      coverSectionsEquiv 57 1 {0,1} (by simp) (equationValue i) :=
  (projectiveInverseIdealSection_evaluate 57 1 {0,1} (by simp)
    literalProjectedConnectingLift (equationTest i)).trans
      (congrArg (coverSectionsEquiv 57 1 {0,1} (by simp))
        (literalProjectedConnectingLift_equation i))

/-- Reduction to the actual normal sheaf uses the original scheme map
on those exact section values. -/
theorem reducedConnectingLift_evaluate_equation (i : Fin 2) :
    (normalSectionEvaluate (curveToSurface 57 1) (coverPatch 57 1 {0,1})
      ((CycleQ2GeometricIntrinsicCartierSequence.inverseIdealReduction (curveToSurface 57 1)).val.app
        (op (coverPatch 57 1 {0,1})) literalConnectingEdge)).toFun
      (coverIdealSection 57 1 {0,1} (by simp) (equationTest i)) =
      (curveToSurface 57 1).app (coverPatch 57 1 {0,1})
        (coverSectionsEquiv 57 1 {0,1} (by simp) (equationValue i)) :=
  congrArg ((curveToSurface 57 1).app (coverPatch 57 1 {0,1}))
    (connectingLift_evaluate_equation i)

end Algebra

section CoordinateRefinement

open CycleQ2GeometricSurfaceDehomogenizedCharts

abbrev coordinateElement : SurfaceRing 57 1 := surfaceQuotient 57 1 (X 1)

def refinementDenominator : SurfaceRing 57 1 :=
  coverProduct 57 1 {0,1} * coordinateElement

theorem refinementDenominator_mem_grade :
    refinementDenominator ∈ surfaceGrade 57 1 9 := by
  exact SetLike.mul_mem_graded
    (show coverProduct 57 1 {0,1} ∈ surfaceGrade 57 1 8 by
      simpa only [overlapDegree] using coverProduct_mem_grade 57 1 {0,1})
    (surfaceQuotient_mem_grade 57 1 x1_homogeneous)

def refinedOverlap : (projectiveSurface 57 1).Opens :=
  Proj.basicOpen (surfaceGrade 57 1) refinementDenominator

theorem refinedOverlap_eq :
    refinedOverlap = coverPatch 57 1 {0,1} ⊓ coordinatePatch 57 1 1 :=
  Proj.basicOpen_mul (surfaceGrade 57 1) (coverProduct 57 1 {0,1}) coordinateElement

theorem refinedOverlap_le_overlap : refinedOverlap ≤ coverPatch 57 1 {0,1} :=
  Proj.basicOpen_mono (surfaceGrade 57 1) _ _ ⟨coordinateElement, rfl⟩

theorem refinedOverlap_le_coordinate : refinedOverlap ≤ coordinatePatch 57 1 1 :=
  Proj.basicOpen_mono (surfaceGrade 57 1) _ _
    ⟨coverProduct 57 1 {0,1}, mul_comm _ _⟩

abbrev RefinedRing := Away (surfaceGrade 57 1) refinementDenominator

def sourceRestriction : HomogeneousCoverLocal 57 1 {0,1} →+* RefinedRing :=
  HomogeneousLocalization.awayMap (surfaceGrade 57 1)
    (surfaceQuotient_mem_grade 57 1 x1_homogeneous) rfl

def coordinateRestriction : CoordinateRing 57 1 1 →+* RefinedRing :=
  HomogeneousLocalization.awayMap (surfaceGrade 57 1)
    (coverProduct_mem_grade 57 1 {0,1}) (mul_comm _ _)

abbrev refinedSectionsEquiv := projectiveSectionRingEquiv 57 1 refinementDenominator
  refinementDenominator_mem_grade (by decide : 0 < 9)

theorem sourceRestriction_section (z : HomogeneousCoverLocal 57 1 {0,1}) :
    (projectiveSurface 57 1).presheaf.map (homOfLE refinedOverlap_le_overlap).op
      (coverSectionsEquiv 57 1 {0,1} (by simp) z) =
        refinedSectionsEquiv (sourceRestriction z) :=
  congrArg (fun k => k z)
    (Proj.awayMap_awayToSection (surfaceGrade 57 1)
      (surfaceQuotient_mem_grade 57 1 x1_homogeneous)
      (show refinementDenominator = coverProduct 57 1 {0,1} * coordinateElement from rfl)).symm

theorem coordinateRestriction_section (z : CoordinateRing 57 1 1) :
    (projectiveSurface 57 1).presheaf.map (homOfLE refinedOverlap_le_coordinate).op
      (projectiveSectionRingEquiv 57 1 coordinateElement
        (surfaceQuotient_mem_grade 57 1 x1_homogeneous) (by decide : 0 < 1) z) =
        refinedSectionsEquiv (coordinateRestriction z) :=
  congrArg (fun k => k z)
    (Proj.awayMap_awayToSection (surfaceGrade 57 1)
      (coverProduct_mem_grade 57 1 {0,1})
      (show refinementDenominator = coordinateElement * coverProduct 57 1 {0,1}
        from mul_comm _ _)).symm

/-- The published dehomogeneous coefficient is the same canonical
homogeneous fraction on the actual coordinate refinement. -/
theorem firstCoefficientSection_refined (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    CycleQ2GeometricSurfaceCubicResidues.firstCoefficientSection 57 1
      refinedOverlap refinedOverlap_le_coordinate p =
        refinedSectionsEquiv (coordinateRestriction (homogeneousFraction 57 1 1 n p hp)) := by
  have hc : (firstSectionsEquiv 57 1).symm
      (algebraMap CycleQ2GeometricSurfaceAdjunction.SurfacePoly
        (CycleQ2GeometricSurfaceAdjunction.SurfaceChartRing (firstEquations 57 1))
        (CycleQ2GeometricSurfaceAdjunction.firstSurfaceDehomogenize p)) =
      projectiveSectionRingEquiv 57 1 coordinateElement
        (surfaceQuotient_mem_grade 57 1 x1_homogeneous) (by decide : 0 < 1)
        (homogeneousFraction 57 1 1 n p hp) := by
    apply (firstSectionsEquiv 57 1).injective
    rw [RingEquiv.apply_symm_apply]
    change _ = firstChartEquiv 57 1
      ((Proj.basicOpenIsoAway (surfaceGrade 57 1) coordinateElement
        (surfaceQuotient_mem_grade 57 1 x1_homogeneous) (by decide : 0 < 1)).inv
        ((Proj.basicOpenIsoAway (surfaceGrade 57 1) coordinateElement
          (surfaceQuotient_mem_grade 57 1 x1_homogeneous) (by decide : 0 < 1)).hom
          (homogeneousFraction 57 1 1 n p hp)))
    rw [Iso.hom_inv_id_apply]
    exact (firstChartEquiv_homogeneousFraction 57 1 n p hp).symm
  exact (CycleQ2GeometricSurfaceOverlap.first_chartSection_subopen 57 1
    (Over.mk (homOfLE refinedOverlap_le_coordinate)) _).trans
      ((congrArg ((projectiveSurface 57 1).presheaf.map
        (homOfLE refinedOverlap_le_coordinate).op) hc).trans
          (coordinateRestriction_section (homogeneousFraction 57 1 1 n p hp)))

abbrev RefinedLocalization := Localization.Away refinementDenominator

instance refinedLocalization_away :
    IsLocalization.Away (coverProduct 57 1 {0,1} * coordinateElement) RefinedLocalization :=
  inferInstanceAs (IsLocalization.Away refinementDenominator RefinedLocalization)

def sourceLocalization : SurfaceOverlap 57 1 →ₐ[SurfaceRing 57 1] RefinedLocalization where
  __ := IsLocalization.Away.awayToAwayRight (coverProduct 57 1 {0,1}) coordinateElement
  commutes' a := IsLocalization.Away.awayToAwayRight_eq _ _ a

def coordinateLocalization : Localization.Away coordinateElement →ₐ[SurfaceRing 57 1]
    RefinedLocalization where
  __ := IsLocalization.Away.awayToAwayLeft coordinateElement (coverProduct 57 1 {0,1})
  commutes' a := IsLocalization.Away.awayToAwayLeft_eq _ _ a

theorem sourceRestriction_val (z : HomogeneousCoverLocal 57 1 {0,1}) :
    (sourceRestriction z).val = sourceLocalization z.val :=
  CycleQ2GradedLocalizationProjection.homogeneousRestriction_val (surfaceGrade 57 1)
    (surfaceQuotient_mem_grade 57 1 x1_homogeneous) rfl sourceLocalization z

theorem coordinateRestriction_val (z : CoordinateRing 57 1 1) :
    (coordinateRestriction z).val = coordinateLocalization z.val :=
  CycleQ2GradedLocalizationProjection.homogeneousRestriction_val (surfaceGrade 57 1)
    (coverProduct_mem_grade 57 1 {0,1}) (mul_comm _ _) coordinateLocalization z

abbrev refinedPolyMap : WeightedPoly →+* RefinedLocalization :=
  (algebraMap (SurfaceRing 57 1) RefinedLocalization).comp (surfaceQuotient 57 1)

abbrev refinedDen : RefinedLocalization :=
  algebraMap (SurfaceRing 57 1) RefinedLocalization (coverProduct 57 1 {0,1})

abbrev refinedCoordinate : RefinedLocalization := refinedPolyMap (X 1)

private theorem refined_den_coordinate_units : IsUnit refinedDen ∧ IsUnit refinedCoordinate := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := RefinedLocalization) refinementDenominator
  change IsUnit (algebraMap (SurfaceRing 57 1) RefinedLocalization
    (coverProduct 57 1 {0,1} * coordinateElement)) at h
  rw [map_mul, IsUnit.mul_iff] at h
  exact h

private theorem coordinateFraction_mul_denominator (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    (coordinateRestriction (homogeneousFraction 57 1 1 n p hp)).val *
      refinedCoordinate ^ n = refinedPolyMap p := by
  have h := fraction_mul_denominator (surfaceGrade 57 1)
    (surfaceQuotient_mem_grade 57 1 x1_homogeneous) n
    (surfaceQuotient 57 1 p) (by simpa using surfaceQuotient_mem_grade 57 1 hp)
  have hm := congrArg coordinateLocalization h
  simpa only [coordinateRestriction_val, homogeneousFraction, map_mul, map_pow,
    AlgHom.commutes, refinedCoordinate, refinedPolyMap, RingHom.comp_apply] using hm

private theorem sourceMultiplier_mul_denominator :
    (sourceRestriction coordinateMultiplier).val * refinedDen = refinedCoordinate ^ 8 := by
  have h := congrArg sourceLocalization coordinateMultiplier_mul_denominator
  simpa only [sourceRestriction_val, map_mul, AlgHom.commutes, overlapPolyMap,
    refinedPolyMap, refinedCoordinate, refinedDen, RingHom.comp_apply, map_pow] using h

private theorem sourceCoefficient_mul_denominator :
    (sourceRestriction connectingCoefficient).val * refinedDen =
      -refinedPolyMap derivativeA * refinedCoordinate ^ 2 := by
  have h := congrArg sourceLocalization connectingCoefficient_mul_denominator
  simpa only [sourceRestriction_val, map_mul, AlgHom.commutes, overlapPolyMap,
    refinedPolyMap, refinedCoordinate, refinedDen, RingHom.comp_apply, map_pow, map_neg] using h

/-- The actual source test restricts to a unit times the original
normalized first-coordinate ideal generator. -/
theorem equationTest_coordinate (i : Fin 2) :
    sourceRestriction (equationTest i : HomogeneousCoverLocal 57 1 {0,1}) =
      sourceRestriction coordinateMultiplier *
        coordinateRestriction (homogeneousFraction 57 1 1 2
          (coordinateEquationPolynomial 57 i) (coordinateEquationPolynomial_homogeneous 57 i)) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  have ht := congrArg sourceLocalization (equationTest_mul_denominator i)
  have ht' : (sourceRestriction (equationTest i : HomogeneousCoverLocal 57 1 {0,1})).val *
      refinedDen = refinedPolyMap (coordinateEquationPolynomial 57 i) * refinedCoordinate ^ 6 := by
    simpa only [sourceRestriction_val, map_mul, AlgHom.commutes, overlapPolyMap,
      refinedPolyMap, refinedCoordinate, refinedDen, RingHom.comp_apply, map_pow] using ht
  exact equation_fraction_identity _ _ _ _ _ _
    refined_den_coordinate_units.1 refined_den_coordinate_units.2 ht'
    sourceMultiplier_mul_denominator
    (coordinateFraction_mul_denominator 2 (coordinateEquationPolynomial 57 i)
      (coordinateEquationPolynomial_homogeneous 57 i))

/-- The displayed functional value has exactly the same scalar factor
as the actual normalized coordinate normal frame. -/
theorem equationValue_coordinate (i : Fin 2) :
    sourceRestriction (equationValue i) =
      sourceRestriction coordinateMultiplier * sourceRestriction connectingCoefficient *
        coordinateRestriction (homogeneousFraction 57 1 1 4
          (normalCoefficientPolynomial 57 i) (normalCoefficientPolynomial_homogeneous 57 i)) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul]
  have ht := congrArg sourceLocalization (equationValue_mul_denominator i)
  have ht' : (sourceRestriction (equationValue i)).val * refinedDen ^ 2 =
      -refinedPolyMap derivativeA * refinedPolyMap (normalCoefficientPolynomial 57 i) *
        refinedCoordinate ^ 6 := by
    simpa only [sourceRestriction_val, map_mul, AlgHom.commutes, overlapPolyMap,
      refinedPolyMap, refinedCoordinate, refinedDen, RingHom.comp_apply, map_pow, map_neg] using ht
  exact value_fraction_identity _ _ _ _ _ _ _ _
    refined_den_coordinate_units.1 refined_den_coordinate_units.2 ht'
    sourceMultiplier_mul_denominator sourceCoefficient_mul_denominator
    (coordinateFraction_mul_denominator 4 (normalCoefficientPolynomial 57 i)
      (normalCoefficientPolynomial_homogeneous 57 i))

theorem sourceMultiplier_isUnit : IsUnit (sourceRestriction coordinateMultiplier) := by
  apply isUnit_of_isUnit_val (surfaceGrade 57 1) refinementDenominator_mem_grade
  exact (IsUnit.mul_iff.mp
    (sourceMultiplier_mul_denominator.symm ▸ refined_den_coordinate_units.2.pow 8)).1

end CoordinateRefinement

end CycleQ2ProjectiveInverseIdealReduction
end

end CheckedCartierNormalPart04

section CheckedCartierNormalPart05

/-! Exact reduction of the original projective inverse-ideal lift,
measured on the original normalized intrinsic normal equations. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProjectiveInverseIdealNormalValue

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedTrace CycleQ2NormalConnecting
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricNormalCharts CycleQ2GeometricLiteralSurface
open CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading
  CycleQ2GeometricCartierNormalLift CycleQ2CartierHomogeneousCech
open CycleQ2ProjectiveInverseIdeal CycleQ2ProjectiveInverseIdealReduction
open CycleQ2GeometricSurfaceCubicResidues
  CycleQ2GeometricCoordinateNormalSections

private abbrev j := curveToSurface (57 : ℂ) 1
private abbrev U := coverPatch (57 : ℂ) 1 {0,1}
private abbrev V := refinedOverlap
private abbrev h : V ⟶ U := homOfLE refinedOverlap_le_overlap

abbrev reducedLift : (normalDirectImageSheaf j).val.obj (op U) :=
  (CycleQ2GeometricIntrinsicCartierSequence.inverseIdealReduction j).val.app (op U)
    literalConnectingEdge

abbrev liftedCoefficient : Γ(projectiveSurface 57 1, U) :=
  coverSectionsEquiv 57 1 {0,1} (by simp) connectingCoefficient

abbrev refinedMultiplier : Γ(projectiveSurface 57 1, V) :=
  refinedSectionsEquiv (sourceRestriction coordinateMultiplier)

abbrev refinedCoefficient : Γ(projectiveSurface 57 1, V) :=
  refinedSectionsEquiv (sourceRestriction connectingCoefficient)

abbrev testIdeal (i : Fin 2) : RingHom.ker (j.app U).hom :=
  coverIdealSection 57 1 {0,1} (by simp) (equationTest i)

abbrev coordinateIdeal (i : Fin 2) : RingHom.ker (j.app V).hom :=
  kernelSectionRestrict j (homOfLE refinedOverlap_le_coordinate)
    (firstCoordinateIdealEquation 57 1 i)

theorem testIdeal_restrict (i : Fin 2) :
    kernelSectionRestrict j h (testIdeal i) = refinedMultiplier • coordinateIdeal i := by
  apply Subtype.ext
  rw [kernelSectionRestrict_coe]
  rw [show (testIdeal i : Γ(projectiveSurface 57 1,U)) =
    coverSectionsEquiv 57 1 {0,1} (by simp) (equationTest i) from
      coverIdealSection_coe 57 1 {0,1} (by simp) (equationTest i)]
  change (projectiveSurface 57 1).presheaf.map h.op
      (coverSectionsEquiv 57 1 {0,1} (by simp)
        (equationTest i : HomogeneousCoverLocal 57 1 {0,1})) =
    refinedMultiplier * (coordinateIdeal i : Γ(projectiveSurface 57 1,V))
  rw [sourceRestriction_section, equationTest_coordinate, map_mul]
  exact congrArg (fun x : Γ(projectiveSurface 57 1,V) => refinedMultiplier * x)
    ((firstCoefficientSection_refined 2 (coordinateEquationPolynomial 57 i)
      (coordinateEquationPolynomial_homogeneous 57 i)).symm.trans
        (firstCoordinateIdealEquation_coefficient 57 1 V refinedOverlap_le_coordinate i).symm)

theorem equationValue_section (i : Fin 2) :
    refinedSectionsEquiv (sourceRestriction (equationValue i)) =
      refinedMultiplier * refinedCoefficient *
        firstCoefficientSection 57 1 V refinedOverlap_le_coordinate
          (normalCoefficientPolynomial 57 i) := by
  rw [equationValue_coordinate, map_mul, map_mul]
  exact congrArg (fun x : Γ(projectiveSurface 57 1,V) => refinedMultiplier * refinedCoefficient * x)
    (firstCoefficientSection_refined 4 (normalCoefficientPolynomial 57 i)
      (normalCoefficientPolynomial_homogeneous 57 i)).symm

theorem reducedLift_restrict_test (i : Fin 2) :
    (normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map h.op reducedLift)).toFun
      (kernelSectionRestrict j h (testIdeal i)) =
      j.app V (refinedMultiplier * refinedCoefficient *
        firstCoefficientSection 57 1 V refinedOverlap_le_coordinate
          (normalCoefficientPolynomial 57 i)) := by
  exact (normalSectionEvaluate_restrict_coefficient j h reducedLift
    ((normalDirectImageSheaf j).val.map h.op reducedLift) rfl (testIdeal i)
    (coverSectionsEquiv 57 1 {0,1} (by simp) (equationValue i))
    (refinedSectionsEquiv (sourceRestriction (equationValue i)))
    (sourceRestriction_section (equationValue i))
    (reducedConnectingLift_evaluate_equation i)).trans
      (congrArg (j.app V) (equationValue_section i))

/-- The reduction has exactly the original normalized coordinate normal
values after the genuine first-coordinate refinement. -/
theorem reducedLift_restrict_coordinate_value (i : Fin 2) :
    (normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map h.op reducedLift)).toFun
      (coordinateIdeal i) =
      j.app V refinedCoefficient * j.app V
        (firstCoefficientSection 57 1 V refinedOverlap_le_coordinate
          (normalCoefficientPolynomial 57 i)) := by
  have hu : IsUnit (j.app V refinedMultiplier) :=
    (sourceMultiplier_isUnit.map refinedSectionsEquiv.toMonoidHom).map (j.app V).hom.toMonoidHom
  apply hu.mul_left_cancel
  have he := reducedLift_restrict_test i
  have ht := congrArg
    (normalSectionEvaluate j V ((normalDirectImageSheaf j).val.map h.op reducedLift)).toFun
    (testIdeal_restrict i)
  have hs := normalSectionEvaluate_smul_ideal j V refinedMultiplier
    ((normalDirectImageSheaf j).val.map h.op reducedLift) (coordinateIdeal i)
  have hm : j.app V (refinedMultiplier * refinedCoefficient *
      firstCoefficientSection 57 1 V refinedOverlap_le_coordinate
        (normalCoefficientPolynomial 57 i)) =
      j.app V refinedMultiplier * (j.app V refinedCoefficient *
        j.app V (firstCoefficientSection 57 1 V refinedOverlap_le_coordinate
          (normalCoefficientPolynomial 57 i))) := by
    rw [map_mul, map_mul, mul_assoc]
  exact hs.symm.trans (ht.symm.trans (he.trans hm))

/-- Actual equality of the two intrinsic normal sections on the
coordinate refinement, with the original coefficient and no rescaling. -/
theorem reducedLift_restrict_eq :
    (normalDirectImageSheaf j).val.map h.op reducedLift =
      normalImageScalar j V (j.app V refinedCoefficient)
        (normalSectionRestrict j refinedOverlap_le_coordinate firstCoordinateNormalVector) := by
  apply firstCoordinateNormal_subopen_ext 57 1 V refinedOverlap_le_coordinate
  intro i
  exact (reducedLift_restrict_coordinate_value i).trans
    ((congrArg (fun z : Γ(CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1,j ⁻¹ᵁ V) =>
      j.app V refinedCoefficient * z)
      (firstCoordinateNormalVector_evaluate_coefficient V refinedOverlap_le_coordinate i).symm).trans
        (normalImageScalar_evaluate j V (j.app V refinedCoefficient)
          (normalSectionRestrict j refinedOverlap_le_coordinate firstCoordinateNormalVector)
          (coordinateIdeal i)).symm)

open CycleQ2IntrinsicNormalRefinement CycleQ2IntrinsicNormalCoordinateBinding
  CycleQ2IntrinsicNormalModel CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricSurfaceCurveCharts

/-- The first coordinate open is required only over the original curve
on this overlap. -/
theorem overlap_preimage_le_first : j ⁻¹ᵁ U ≤ coordinateProjectivePatch 57 1 1 :=
  (normalCoverOverlap_preimage 57 1).le.trans
    (((overlapProjectivePatch_eq 57 1).le.trans inf_le_left).trans
      (firstProjectivePatch_le_firstCoordinate 57 1))

theorem refinedOverlap_preimage : j ⁻¹ᵁ V = j ⁻¹ᵁ U := by
  change j ⁻¹ᵁ refinedOverlap = j ⁻¹ᵁ coverPatch 57 1 {0,1}
  rw [refinedOverlap_eq, Scheme.Hom.preimage_inf]
  exact inf_eq_left.mpr (overlap_preimage_le_first.trans
    (coordinateCurvePreimage 57 1 (1 : Fin 4)).ge)

abbrev firstFrameOnOverlap : (normalDirectImageSheaf j).val.obj (op U) :=
  frameImage j firstCoordinateFrame U overlap_preimage_le_first

theorem firstFrameOnOverlap_restrict :
    (normalDirectImageSheaf j).val.map h.op firstFrameOnOverlap =
      normalSectionRestrict j refinedOverlap_le_coordinate firstCoordinateNormalVector :=
  (frameImage_restrict j firstCoordinateFrame refinedOverlap_le_overlap
    overlap_preimage_le_first).trans
      (firstFrameImage_subopen V refinedOverlap_le_coordinate)

/-- The original cone lift reduces to the fixed intrinsic projective
normal frame with its original degree-zero coefficient. -/
theorem connectingLift_reduction_frame :
    reducedLift = normalImageScalar j U (j.app U liftedCoefficient) firstFrameOnOverlap := by
  apply normalRestriction_injective j h refinedOverlap_preimage
  have hc : (projectiveCurve 57 1).presheaf.map ((Opens.map j.base).map h).op
      (j.app U liftedCoefficient) = j.app V refinedCoefficient :=
    (ConcreteCategory.congr_hom (j.naturality h.op) liftedCoefficient).symm.trans
      (congrArg (j.app V) (sourceRestriction_section connectingCoefficient))
  have hr := normalImageScalar_restrict j h (j.app U liftedCoefficient) firstFrameOnOverlap
  exact reducedLift_restrict_eq.trans
    (hr.trans (congrArg₂ (normalImageScalar j V) hc firstFrameOnOverlap_restrict)).symm

end CycleQ2ProjectiveInverseIdealNormalValue
end

end CheckedCartierNormalPart05

section CheckedCartierNormalPart06

/-! The coefficient of the actual inverse-ideal lift is precisely the
original homogeneous normal-overlap coordinate after pullback to the curve. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProjectiveInverseIdealCoefficient

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomogeneousLocalization
open Graded MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricLiteralCanonicalClass CycleQ2GeometricLiteralDirection
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2IntrinsicNormalRefinement CycleQ2ProjectiveInverseIdealReduction
  CycleQ2ProjectiveInverseIdealNormalValue

open CycleQ2GeometricLiteralSurface
  (curveGradedMap curveToSurface curve_irrelevant_le projMap_app_basicOpen)

section Generic
variable {R σ : Type*} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Changing only the equal denominator/numerator presentations leaves
the actual homogeneous section and its canonical restriction unchanged. -/
theorem section_mk_congr {f g : R} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : f = g) (hopen : Proj.basicOpen 𝒜 f ≤ Proj.basicOpen 𝒜 g)
    (n : ℕ) (p q : R) (hp : p ∈ 𝒜 (n • d)) (hq : q ∈ 𝒜 (n • e)) (hpq : p = q) :
    (Proj 𝒜).presheaf.map (homOfLE hopen).op
      (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg n q hq)) =
        Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf n p hp) := by
  subst g
  subst q
  have hi : (homOfLE hopen : Proj.basicOpen 𝒜 f ⟶ Proj.basicOpen 𝒜 f) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hi, op_id]
  calc
    _ = Proj.awayToSection 𝒜 f (Away.mk 𝒜 hg n p hq) :=
      ConcreteCategory.congr_hom ((Proj 𝒜).presheaf.map_id _) _
    _ = Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf n p hp) := by
      apply congrArg (Proj.awayToSection 𝒜 f)
      apply HomogeneousLocalization.val_injective
      rw [Away.val_mk, Away.val_mk]

end Generic

private abbrev U := coverPatch (57 : ℂ) 1 {0,1}
private abbrev j := curveToSurface (57 : ℂ) 1
private abbrev s := coverProduct (57 : ℂ) 1 {0,1}
private abbrev f := curveGradedMap (57 : ℂ) 1

private theorem denominator_eq : f s = curveG1 57 1 * curveG2 57 1 := by
  change f (coverProduct 57 1 {0,1}) = curveG1 57 1 * curveG2 57 1
  rw [coverProduct_pair, map_mul]
  rfl

private theorem numerator_eq :
    f (surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2)) =
      curveMap 57 1 (ambientNormalNumerator * X 1 ^ 2) := by
  change curveMap 57 1 (substitute (-derivativeA * X 1 ^ 2)) = _
  apply congrArg (curveMap 57 1)
  rw [map_mul, map_neg, map_pow]
  have ha : substitute derivativeA = -(X 2 ^ 3 * X 3 ^ 3) := substitute_ambientTest
  have hx : substitute (X (1 : Fin 5)) = X (1 : Fin 4) := by simp [substitute]
  rw [ha, hx, neg_neg]
  rfl

private theorem x1_homogeneous :
    (X (1 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (1 : Fin 5)

private theorem sourceDenominator_degree : s ∈ surfaceGrade 57 1 8 := by
  simpa only [show coverProductDegree {0,1} = 8 by decide] using
    coverProduct_mem_grade 57 1 {0,1}

private theorem sourceNumerator_degree :
    surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2) ∈ surfaceGrade 57 1 8 :=
  surfaceQuotient_mem_grade 57 1 (derivativeA_homogeneous.neg.mul (x1_homogeneous.pow 2))

/-- The original coefficient on the original quartic overlap is retained
exactly by the actual scheme section map. -/
theorem liftedCoefficient_pullback :
    j.app U liftedCoefficient =
      (projectiveCurve 57 1).presheaf.map
        (homOfLE (normalCoverOverlap_preimage 57 1).le).op
        ((overlapProjectiveSectionsIso 57 1).hom
          (normalOverlapCoordinate 57 1 ambientNormalNumerator ambientNormalNumerator_homogeneous)) := by
  have hp : curveMap 57 1 (ambientNormalNumerator * X 1 ^ 2) ∈ curveGrade 57 1 8 :=
    curveMap_mem_grade 57 1
      (ambientNormalNumerator_homogeneous.mul ((isHomogeneous_X ℂ (1 : Fin 4)).pow 2))
  have hmap : Away.map f s connectingCoefficient =
      Away.mk (curveGrade 57 1) (map_mem f sourceDenominator_degree) 1
        (f (surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2)))
        (by simpa only [one_smul] using map_mem f sourceNumerator_degree) := by
    apply HomogeneousLocalization.val_injective
    simp only [connectingCoefficient, Away.map_mk, Away.val_mk]
  have happ := projMap_app_basicOpen (surfaceGrade 57 1) (curveGrade 57 1)
    f (curve_irrelevant_le 57 1) s (coverProduct_mem_grade 57 1 {0,1})
    (coverProductDegree_pos (by simp)) connectingCoefficient
  have hsec := section_mk_congr (curveGrade 57 1)
    (map_mem f sourceDenominator_degree) (curveG12_mem_grade 57 1)
    denominator_eq (normalCoverOverlap_preimage 57 1).le 1
    (f (surfaceQuotient 57 1 (-derivativeA * X 1 ^ 2)))
    (curveMap 57 1 (ambientNormalNumerator * X 1 ^ 2))
    (by simpa only [one_smul] using map_mem f sourceNumerator_degree)
    (by simpa only [one_smul] using hp) numerator_eq
  exact happ.trans ((congrArg (Proj.awayToSection (curveGrade 57 1) (f s)) hmap).trans hsec.symm)

end CycleQ2ProjectiveInverseIdealCoefficient
end

end CheckedCartierNormalPart06

section CheckedCartierNormalPart07

/-! The original inverse-ideal lift reduces to the unchanged intrinsic
normal overlap section. Every map is the actual projective sheaf map. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProjectiveInverseIdealBinding

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2NormalConnecting CycleQ2GeometricLiteralSurface
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2CartierProjectiveCover CycleQ2IntrinsicNormalModel
  CycleQ2IntrinsicNormalBoundary CycleQ2IntrinsicNormalRefinement
  CycleQ2IntrinsicNormalCoordinateBinding CycleQ2IntrinsicOverlapCoordinates
  CycleQ2ProjectiveInverseIdeal CycleQ2ProjectiveInverseIdealNormalValue
  CycleQ2ProjectiveInverseIdealCoefficient

private abbrev j := curveToSurface (57 : ℂ) 1
private abbrev U := coverPatch (57 : ℂ) 1 {0,1}

/-- Exact reduction on the actual product patch, with the original
normal-class numerator and its fixed intrinsic normalization. -/
theorem connectingLift_reduction :
    (inverseIdealReduction j).val.app (op U) literalConnectingEdge =
      (normalDirectImageSheaf j).val.map
        (homOfLE (normalCoverOverlap_le_target 57 1)).op
        (intrinsicOverlapSection 57 1 intrinsicNormalIso
          ambientNormalNumerator ambientNormalNumerator_homogeneous) := by
  have hc := congrArg
    (fun c : Γ(projectiveCurve 57 1, j ⁻¹ᵁ U) =>
      normalImageScalar j U c firstFrameOnOverlap)
    liftedCoefficient_pullback
  have hp := (intrinsicOverlapSection_product ambientNormalNumerator
    ambientNormalNumerator_homogeneous).symm
  exact connectingLift_reduction_frame.trans (hc.trans hp)

end CycleQ2ProjectiveInverseIdealBinding
end

end CheckedCartierNormalPart07

section CheckedCartierNormalPart08

/-!
# The original normalized normal class and the Cartier connecting map

The incoming actual inverse-ideal one-cochain has positive edge 01.  Its
reduction is identified with the unchanged intrinsic normal overlap
section.  The proved four-to-two refinement supplies the negative sign
between this positive-edge Cech class and the original Mayer--Vietoris
normal class.  The coefficient boundary is the original short-exact
sequence's extension class, without choosing a new connecting map.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2OriginalCartierConnecting

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechOneConnecting CycleQ2CechOneMayerVietoris
  CycleQ2IntrinsicNormalBoundary CycleQ2IntrinsicNormalRefinement
  CycleQ2IntrinsicNormalModel CycleQ2IntrinsicSurfaceNormalCohomology
  CycleQ2SurfaceNormalTransport CycleQ2CartierProjectiveCover
  CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricLiteralDirection CycleQ2SeedTrace
  CycleQ2ProjectiveInverseIdeal CycleQ2ProjectiveInverseIdealBinding
  CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2GeometricSheafCohomologyRestriction

open CycleQ2ProjectiveCartierIntersections (literal_cover sectionEquivOfOpenEq)
open CycleQ2ProjectiveCartierDerived
  (literalCocycle literalCocycle_closed literalDerivedClassAtTop
   literalDerivedClassAtTop_ne_zero literalTerminalCohomologyEquiv
   literalDerivedClass literalDerivedClass_ne_zero)

local instance : HasExt.{1} (AbSheaf (projectiveSurface 57 1)) := HasExt.standard _

/-- The actual geometric reduction, proved by evaluating the original
inverse-ideal lift on the genuine chart equations. -/
theorem originalReduction : CycleQ2OriginalCartierConnectingCore.ReductionHolds :=
  connectingLift_reduction

abbrev originalCocycle := CycleQ2OriginalCartierConnectingCore.originalCocycle

theorem originalCocycle_closed :
    d1 literalSequence.X₃ (coverFamily 57 1) originalCocycle = 0 :=
  CycleQ2OriginalCartierConnectingCore.originalCocycle_closed

theorem originalCocycle_class :
    CycleQ2CechOneConnecting.cechOneClass (coverFamily 57 1) literal_cover
      originalCocycle originalCocycle_closed = -literalIntrinsicNormalClass :=
  CycleQ2OriginalCartierConnectingCore.originalCocycle_class

theorem literalConnectingOne_reduction :
    mapOne (coverFamily 57 1) literalSequence.g literalConnectingOne = originalCocycle :=
  CycleQ2OriginalCartierConnectingCore.literalConnectingOne_reduction originalReduction

theorem literalReducedCocycle_class :
    CycleQ2CechOneConnecting.cechOneClass (coverFamily 57 1) literal_cover
      (mapOne (coverFamily 57 1) literalSequence.g literalConnectingOne)
      (reduction_closed (coverFamily 57 1) literalConnectingOne literalCocycle
        literalConnectingOne_boundary) = -literalIntrinsicNormalClass :=
  CycleQ2OriginalCartierConnectingCore.literalReducedCocycle_class originalReduction

/-- The original intrinsic normal class has exactly the negative of the
unchanged literal Cartier class as its actual coefficient boundary. -/
theorem literalOpenConnecting_originalClass :
    literalOpenConnecting ⊤ literalIntrinsicNormalClass = -literalDerivedClassAtTop :=
  CycleQ2OriginalCartierConnectingCore.literalOpenConnecting_originalClass originalReduction

theorem literalOpenConnecting_originalClass_ne_zero :
    literalOpenConnecting ⊤ literalIntrinsicNormalClass ≠ 0 :=
  CycleQ2OriginalCartierConnectingCore.literalOpenConnecting_originalClass_ne_zero originalReduction

/-- The same formula in ordinary derived sheaf cohomology. -/
theorem literalConnecting_originalClass :
    literalConnecting
      (terminalCohomologyEquiv
        (Opens.grothendieckTopology (projectiveSurface 57 1)) literalSequence.X₃
        ⊤ isTerminalTop 1 literalIntrinsicNormalClass) = -literalDerivedClass :=
  CycleQ2OriginalCartierConnectingCore.literalConnecting_originalClass originalReduction

end CycleQ2OriginalCartierConnecting
end

end CheckedCartierNormalPart08
