import Proposal.GeometricCubicAdjunctionFrameBinding
import Proposal.GeometricLocalHomFrame

/-!
# The actual canonical residue morphism

Status: source-only proof draft; compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

On a Jacobian/quartic surface patch, the actual exterior frame identifies
`Hom(I, Ω²)` with the original inverse-ideal sheaf. Reduction by the original
Cartier map followed by contraction with that frame defines the local
residue. The original cubic overlap identities cancel the change of frame.
Together with zero on the complement of the curve, these local morphisms
glue in the genuine internal-Hom sheaf on the entire surface.

The construction keeps the original kernel ideal, exterior sheaf, curve
immersion, and curve differentials. No global cubic extension, cohomology
vanishing, or trace comparison is asserted here.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalResidueSheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricCanonicalGluing CycleQ2LocalHomFrame
  CycleQ2GeometricExteriorSheaf CycleQ2SourceNormalSheaf CycleQ2NormalPushforwardIso
  CycleQ2SurfaceExteriorFrameBinding CycleQ2ClosedSupportCohomology

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

abbrev Surface := CycleQ2CartierProjectiveCover.projectiveSurface (57 : ℂ) 1
abbrev Curve := CycleQ2GlobalCubicAdjunction.Curve
abbrev immersion := CycleQ2GeometricLiteralSurface.curveToSurface (57 : ℂ) 1
abbrev CanonicalForms :=
  CycleQ2SurfaceResidueSheafOverlap.surfaceExteriorSheaf (57 : ℂ) 1
abbrev IdealSheaf := kernelIdealSheaf immersion
abbrev PoleForms := moduleHomSheaf Surface.sheaf IdealSheaf CanonicalForms
abbrev CurveForms := CycleQ2GlobalCubicAdjunction.Differentials
abbrev ResidueTarget := (Scheme.Modules.pushforward immersion).obj CurveForms
abbrev PatchIndex := CycleQ2GlobalCubicAdjunction.PatchIndex

abbrev surfacePatch (a : PatchIndex) : Surface.Opens :=
  CycleQ2SurfaceCubicGluing.patchOpen 57 1 a

/-- The existing normal cover is refined by the existing quartic cover. -/
def refinedPatch : PatchIndex → Surface.Opens
  | .inl a => surfacePatch (.inl a) ⊓ CycleQ2CartierProjectiveCover.coverFamily 57 1 0
  | .inr a => surfacePatch (.inr a) ⊓ CycleQ2CartierProjectiveCover.coverFamily 57 1 1

theorem refinedPatch_le (a : PatchIndex) : refinedPatch a ≤ surfacePatch a := by
  cases a <;> exact inf_le_left

theorem preimage_refinedPatch (a : PatchIndex) :
    immersion ⁻¹ᵁ refinedPatch a = CycleQ2GlobalCubicAdjunction.patchOpen a := by
  cases a with
  | inl a =>
      change immersion ⁻¹ᵁ (surfacePatch (.inl a) ⊓
        CycleQ2CartierProjectiveCover.coverFamily 57 1 0) = _
      rw [Scheme.Hom.preimage_inf,
        CycleQ2ProjectiveCurveSurface.curveToSurface_preimage_cover_zero]
      rfl
  | inr a =>
      change immersion ⁻¹ᵁ (surfacePatch (.inr a) ⊓
        CycleQ2CartierProjectiveCover.coverFamily 57 1 1) = _
      rw [Scheme.Hom.preimage_inf,
        CycleQ2ProjectiveCurveSurface.curveToSurface_preimage_cover_one]
      rfl

/-- The actual open complement of the original closed curve. -/
def offCurve : Surface.Opens :=
  extendedOpen immersion.base (CycleQ2SurfaceNormalCohomology.curveClosedEmbedding 57 1) ⊥

theorem preimage_offCurve : immersion ⁻¹ᵁ offCurve = ⊥ :=
  preimage_extendedOpen immersion.base
    (CycleQ2SurfaceNormalCohomology.curveClosedEmbedding 57 1) ⊥

def residueCover : Option PatchIndex → Surface.Opens
  | none => offCurve
  | some a => refinedPatch a

theorem residueCover_top : (⨆ a, residueCover a) = ⊤ := by
  apply le_antisymm le_top
  intro y _
  by_cases hy : ∃ x : Curve, immersion x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ ⨆ a, CycleQ2GlobalCubicAdjunction.patchOpen a := by
      rw [CycleQ2GlobalCubicAdjunction.patchOpen_cover]
      trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    apply (le_iSup residueCover (some a))
    change x ∈ immersion ⁻¹ᵁ refinedPatch a
    rw [preimage_refinedPatch]
    exact ha
  · apply (le_iSup residueCover none)
    change y ∉ immersion.base '' ((⊥ : Curve.Opens) : Set Curve)ᶜ
    rintro ⟨x, _, hxy⟩
    exact hy ⟨x, hxy⟩

theorem target_empty (O : Surface.Opens) (hO : immersion ⁻¹ᵁ O = ⊥) :
    Subsingleton (ResidueTarget.val.obj (op O)) := by
  change Subsingleton (CurveForms.val.obj (op (immersion ⁻¹ᵁ O)))
  rw [hO]
  have ht : IsTerminal ((addSheaf CurveForms).obj.obj (op (⊥ : Curve.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (addSheaf CurveForms)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp ht.isZero

theorem target_empty_of_le {O : Surface.Opens} (hO : O ≤ offCurve) :
    Subsingleton (ResidueTarget.val.obj (op O)) := by
  apply target_empty
  apply le_antisymm _ bot_le
  exact (immersion.preimage_mono hO).trans preimage_offCurve.le

/-- The actual contraction expressed on the original surface-side normal sheaf. -/
def normalContraction (p : CycleQ2SurfaceCubicGluing.WeightedCubic) :
    normalDirectImageSheaf immersion ⟶ ResidueTarget :=
  (actualNormalPushforwardIso 57 1).inv ≫
    (Scheme.Modules.pushforward immersion).map
      (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction p)

/-- This is the unchanged Cartier reduction followed by the actual contraction. -/
def reducedContraction (p : CycleQ2SurfaceCubicGluing.WeightedCubic) :
    inverseIdealSheaf immersion ⟶ ResidueTarget :=
  inverseIdealReduction immersion ≫ normalContraction p

def localResidue (a : PatchIndex) (O : Surface.Opens) (hO : O ≤ refinedPatch a) :
    PoleForms.val.obj (op O) →ₗ[Γ(Surface, O)] ResidueTarget.val.obj (op O) :=
  ((reducedContraction (frameCubic a)).val.app (op O)).hom.comp
    ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
      O (hO.trans (refinedPatch_le a))).toLinearMap

theorem localResidue_restrict (a : PatchIndex) {O P : Surface.Opens}
    (hPO : P ≤ O) (hO : O ≤ refinedPatch a) (H : PoleForms.val.obj (op O)) :
    ResidueTarget.val.map (homOfLE hPO).op (localResidue a O hO H) =
      localResidue a P (hPO.trans hO) (PoleForms.val.map (homOfLE hPO).op H) := by
  change ResidueTarget.val.map (homOfLE hPO).op
    ((reducedContraction (frameCubic a)).val.app (op O)
      ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
        O (hO.trans (refinedPatch_le a)) H)) = _
  rw [← PresheafOfModules.naturality_apply,
    (internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).naturality]
  rfl

private theorem frameTransition (a b : PatchIndex) (O : Surface.Opens)
    (ha : O ≤ surfacePatch a) (hb : O ≤ surfacePatch b)
    (H : PoleForms.val.obj (op O)) :
    (internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app O ha H =
      frameCoordinate (exteriorFrame 57 1 a) O ha
          (frameGenerator (exteriorFrame 57 1 b) O hb) •
        (internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 b)).app O hb H := by
  let α : Γ(Surface, O) := frameCoordinate (exteriorFrame 57 1 a) O ha
    (frameGenerator (exteriorFrame 57 1 b) O hb)
  have hgen : frameGenerator (exteriorFrame 57 1 b) O hb =
      α • frameGenerator (exteriorFrame 57 1 a) O ha := by
    apply ((exteriorFrame 57 1 a).app O ha).injective
    change α = (exteriorFrame 57 1 a).app O ha
      (α • ((exteriorFrame 57 1 a).app O ha).symm (1 : Γ(Surface, O)))
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one α).symm
  apply localLinearHom_ext
  intro V x
  change (exteriorFrame 57 1 a).app V.left (V.hom.le.trans ha)
      (H.val.app (op V) x) =
    Surface.presheaf.map V.hom.op α •
      (exteriorFrame 57 1 b).app V.left (V.hom.le.trans hb) (H.val.app (op V) x)
  have hg := congrArg (CanonicalForms.val.map V.hom.op) hgen
  rw [frameGenerator_naturality, CanonicalForms.val.map_smul,
    frameGenerator_naturality] at hg
  exact coordinates_of_generator_relation
    ((exteriorFrame 57 1 a).app V.left (V.hom.le.trans ha))
    ((exteriorFrame 57 1 b).app V.left (V.hom.le.trans hb))
    (Surface.presheaf.map V.hom.op α) hg (H.val.app (op V) x)

theorem localResidue_overlap (a b : PatchIndex) (O : Surface.Opens)
    (ha : O ≤ refinedPatch a) (hb : O ≤ refinedPatch b)
    (H : PoleForms.val.obj (op O)) :
    localResidue a O ha H = localResidue b O hb H := by
  let α : Γ(Surface, O) := frameCoordinate (exteriorFrame 57 1 a) O
    (ha.trans (refinedPatch_le a))
    (frameGenerator (exteriorFrame 57 1 b) O (hb.trans (refinedPatch_le b)))
  have hH := frameTransition a b O (ha.trans (refinedPatch_le a))
    (hb.trans (refinedPatch_le b)) H
  change (reducedContraction (frameCubic a)).val.app (op O)
      ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
        O (ha.trans (refinedPatch_le a)) H) = _
  rw [hH, map_smul]
  let n := (actualNormalPushforwardIso 57 1).inv.val.app (op O)
    ((inverseIdealReduction immersion).val.app (op O)
      ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 b)).app
        O (hb.trans (refinedPatch_le b)) H))
  change immersion.app O α •
    (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction (frameCubic a)).val.app
      (op (immersion ⁻¹ᵁ O)) n =
    (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction (frameCubic b)).val.app
      (op (immersion ⁻¹ᵁ O)) n
  have hc := CycleQ2CubicAdjunctionFrameBinding.contraction_formula
    (frameCubic b) a O (ha.trans (refinedPatch_le a)) (immersion ⁻¹ᵁ O)
    ((immersion.preimage_mono ha).trans (preimage_refinedPatch a).le) le_rfl n
  rw [Scheme.Hom.appLE_eq_app,
    ← generator_eq_original_cubic_on_overlap 57 1 a b O
      (ha.trans (refinedPatch_le a)) (hb.trans (refinedPatch_le b))] at hc
  exact hc.symm

/-- Each normal/quartic patch carries a literal local module morphism. -/
def localResidueHom (a : PatchIndex) :
    LocalLinearHom Surface.sheaf PoleForms ResidueTarget (refinedPatch a) :=
  ⟨{
    app V := AddCommGrpCat.ofHom
      (localResidue a V.unop.left V.unop.hom.le).toAddMonoidHom
    naturality {V W} f := by
      apply ConcreteCategory.hom_ext
      intro H
      exact (localResidue_restrict a f.unop.left.le V.unop.hom.le H).symm
  }, by
    intro V r H
    exact (localResidue a V.left V.hom.le).map_smul r H⟩

def coverResidue : (a : Option PatchIndex) →
    LocalLinearHom Surface.sheaf PoleForms ResidueTarget (residueCover a)
  | none => 0
  | some a => localResidueHom a

theorem coverResidue_compatible :
    TopCat.Presheaf.IsCompatible
      (addSheaf (moduleHomSheaf Surface.sheaf PoleForms ResidueTarget)).obj
      residueCover coverResidue := by
  intro a b
  apply localLinearHom_ext
  intro V H
  cases a with
  | none =>
      haveI := target_empty_of_le (V.hom.le.trans inf_le_left)
      exact Subsingleton.elim _ _
  | some a =>
      cases b with
      | none =>
          haveI := target_empty_of_le (V.hom.le.trans inf_le_right)
          exact Subsingleton.elim _ _
      | some b =>
          exact localResidue_overlap a b V.left
            (V.hom.le.trans inf_le_left) (V.hom.le.trans inf_le_right) H

theorem residueSection_existsUnique :
    ∃! H : LocalLinearHom Surface.sheaf PoleForms ResidueTarget ⊤, ∀ a,
      restrictLocalLinearHom Surface.sheaf PoleForms ResidueTarget
        (homOfLE (le_top : residueCover a ≤ ⊤)).op H = coverResidue a :=
  (addSheaf (moduleHomSheaf Surface.sheaf PoleForms ResidueTarget)).existsUnique_gluing'
    residueCover ⊤ (fun _ => homOfLE le_top) residueCover_top.ge coverResidue
    coverResidue_compatible

/-- The globally glued local linear morphism, before the canonical top-open
identification with an actual morphism of module sheaves. -/
def residueSection : LocalLinearHom Surface.sheaf PoleForms ResidueTarget ⊤ :=
  Classical.choose residueSection_existsUnique

theorem residueSection_restrict (a : Option PatchIndex) :
    restrictLocalLinearHom Surface.sheaf PoleForms ResidueTarget
      (homOfLE (le_top : residueCover a ≤ ⊤)).op residueSection = coverResidue a :=
  (Classical.choose_spec residueSection_existsUnique).1 a

/-- The canonical residue morphism for the original literal surface/curve. -/
def canonicalResidue : PoleForms ⟶ ResidueTarget :=
  localLinearHomTopEquiv Surface.sheaf PoleForms ResidueTarget residueSection

/-- On every specified patch subopen, the global map retains the original
Cartier reduction and actual local normal-first contraction. -/
theorem canonicalResidue_local (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a) (H : PoleForms.val.obj (op O)) :
    canonicalResidue.val.app (op O) H = localResidue a O hO H := by
  have h := residueSection_restrict (some a)
  have hh := congrArg
    (fun f : LocalLinearHom Surface.sheaf PoleForms ResidueTarget (refinedPatch a) =>
      f.val.app (op (Over.mk (homOfLE hO))) H) h
  exact hh

/-- Expanded component formula for the original Cartier/canonical diagram. -/
theorem canonicalResidue_local_formula (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a) (H : PoleForms.val.obj (op O)) :
    canonicalResidue.val.app (op O) H =
      (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction (frameCubic a)).val.app
        (op (immersion ⁻¹ᵁ O))
        ((actualNormalPushforwardIso 57 1).inv.val.app (op O)
          ((inverseIdealReduction immersion).val.app (op O)
            ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
              O (hO.trans (refinedPatch_le a)) H))) :=
  canonicalResidue_local a O hO H

theorem canonicalResidue_offCurve (O : Surface.Opens) (hO : O ≤ offCurve)
    (H : PoleForms.val.obj (op O)) : canonicalResidue.val.app (op O) H = 0 :=
  @Subsingleton.elim _ (target_empty_of_le hO) _ _

theorem localResidue_regular (a : PatchIndex) (O : Surface.Opens)
    (hO : O ≤ refinedPatch a) (s : CanonicalForms.val.obj (op O)) :
    localResidue a O hO
      ((idealRegularInclusion immersion CanonicalForms).val.app (op O) s) = 0 := by
  change (reducedContraction (frameCubic a)).val.app (op O)
    ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
      O (hO.trans (refinedPatch_le a))
      ((idealRegularInclusion immersion CanonicalForms).val.app (op O) s)) = 0
  rw [internalHomFrame_idealRegularInclusion]
  have hz := congrArg
    (fun f : SheafOfModules.unit (ringSheaf Surface.sheaf) ⟶
        normalDirectImageSheaf immersion =>
      f.val.app (op O) ((exteriorFrame 57 1 a).app O
        (hO.trans (refinedPatch_le a)) s))
    (inverseIdealScalar_comp_reduction immersion)
  change (inverseIdealReduction immersion).val.app (op O)
    ((inverseIdealScalar immersion).val.app (op O)
      ((exteriorFrame 57 1 a).app O (hO.trans (refinedPatch_le a)) s)) = 0 at hz
  change (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction (frameCubic a)).val.app
    (op (immersion ⁻¹ᵁ O))
    ((actualNormalPushforwardIso 57 1).inv.val.app (op O)
      ((inverseIdealReduction immersion).val.app (op O)
        ((inverseIdealScalar immersion).val.app (op O)
          ((exteriorFrame 57 1 a).app O (hO.trans (refinedPatch_le a)) s)))) = 0
  rw [hz, map_zero, map_zero]

theorem canonicalResidue_regular_section (O : Surface.Opens)
    (s : CanonicalForms.val.obj (op O)) :
    canonicalResidue.val.app (op O)
      ((idealRegularInclusion immersion CanonicalForms).val.app (op O) s) = 0 := by
  apply (addSheaf ResidueTarget).eq_of_locally_eq'
    (fun a => O ⊓ residueCover a) O (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, residueCover_top, inf_top_eq])
  intro a
  change ResidueTarget.val.map (homOfLE (show O ⊓ residueCover a ≤ O from inf_le_left)).op
    (canonicalResidue.val.app (op O)
      ((idealRegularInclusion immersion CanonicalForms).val.app (op O) s)) =
    ResidueTarget.val.map (homOfLE (show O ⊓ residueCover a ≤ O from inf_le_left)).op 0
  rw [map_zero, ← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply]
  cases a with
  | none =>
      haveI := target_empty_of_le (show O ⊓ residueCover none ≤ offCurve from inf_le_right)
      exact Subsingleton.elim _ _
  | some a =>
      rw [canonicalResidue_local a _ inf_le_right, localResidue_regular]

/-- The original regular inclusion followed by the actual residue is zero. -/
theorem canonicalResidue_regular :
    idealRegularInclusion immersion CanonicalForms ≫ canonicalResidue = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact canonicalResidue_regular_section O.unop s

/-- The canonical residue complex with the original ideal and genuine
surface and curve differential sheaves. Its short exactness is proved in
the separate local-exactness binding. -/
def canonicalResidueComplex : ShortComplex Surface.Modules where
  X₁ := CanonicalForms
  X₂ := PoleForms
  X₃ := ResidueTarget
  f := idealRegularInclusion immersion CanonicalForms
  g := canonicalResidue
  zero := canonicalResidue_regular

#print axioms residueCover_top
#print axioms localResidue_overlap
#print axioms canonicalResidue
#print axioms canonicalResidue_local
#print axioms canonicalResidue_local_formula
#print axioms canonicalResidue_offCurve
#print axioms canonicalResidue_regular
#print axioms canonicalResidueComplex

end CycleQ2CanonicalResidueSheaf

end
