/-
SOURCE-ONLY DRAFT: unverified.
Compilation and independent kernel replay were deferred at the user's request.
The proof terms below have not been accepted as a checked certificate.
-/

import Proposal.GeometricCartierNormalConnecting
import Proposal.GeometricCartierNormalBinding

/-!
# Cubic adjunction on the original intrinsic normal class

The local normal-first contractions of the original cubic surface
representatives glue to a morphism from the actual intrinsic normal sheaf
to the actual curve differential sheaf. The morphism agrees with the
previously constructed cubic morphism; its pushed degree-one map preserves
the proved nonzero selected-cubic image of the original normal class.

This file constructs neither the canonical residue connecting sequence nor
a Serre trace, a moving-cycle map, or the final rational primitive.
The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

section GlobalCubicAdjunctionGluing

/-!
# Global contraction by the original cubic surface forms

The local maps in this file are defined from the genuine intrinsic normal
frames and the actual normal-first contraction of the restricted surface
determinants. Their values on arbitrary sections are glued over the proved
Jacobian/quartic refinement. The previously constructed cubic morphism is
used to prove compatibility and identify the result, not to define it.

This is a comparison of genuine sheaf morphisms at the literal seed. It
does not construct the canonical residue sequence, a Serre trace, or the
final de Rham primitive.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GlobalCubicAdjunction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricSurfaceNormalCover CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricModuleLocalIso CycleQ2SourceNormalSheaf
  CycleQ2ProjectiveNormalFrames CycleQ2NormalVectorOnCurve
  CycleQ2IntrinsicNormalModel CycleQ2CubicDifferentialMap
  CycleQ2CurveCubicCoefficients CycleQ2SurfaceCubicGluing
  CycleQ2ActualCubicAdjunctionBinding

open CycleQ2GeometricSheafLocalIso (res res_comp)

abbrev Curve := projectiveCurve (57 : ℂ) 1
abbrev Normal := actualNormal (57 : ℂ) 1
abbrev Differentials := projectiveDifferentialSheaf (57 : ℂ) 1

local instance normalSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Normal.val.obj (op W)) :=
  (Normal.val.obj (op W)).isModule

local instance differentialSectionModule (W : Curve.Opens) :
    Module Γ(Curve, W) (Differentials.val.obj (op W)) :=
  (Differentials.val.obj (op W)).isModule

abbrev PatchIndex := (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3)

/-- The actual normal-chart refinement of the original quartic cover. -/
def patchOpen : PatchIndex → Curve.Opens
  | .inl a => firstFamily a ⊓ firstProjectivePatch 57 1
  | .inr a => secondFamily a ⊓ secondProjectivePatch 57 1

theorem patchOpen_cover : (⨆ a, patchOpen a) = ⊤ := by
  have hfirst : firstProjectivePatch 57 1 ≤ ⨆ a, patchOpen a := by
    calc
      firstProjectivePatch 57 1 =
          (⨆ a, firstFamily a) ⊓ firstProjectivePatch 57 1 := by
        rw [firstFamily_cover]
        exact (inf_eq_right.mpr (firstProjectivePatch_le_firstCoordinate 57 1)).symm
      _ = ⨆ a, firstFamily a ⊓ firstProjectivePatch 57 1 := iSup_inf_eq _ _
      _ ≤ ⨆ a, patchOpen a := iSup_le (fun a => le_iSup patchOpen (.inl a))
  have hsecond : secondProjectivePatch 57 1 ≤ ⨆ a, patchOpen a := by
    calc
      secondProjectivePatch 57 1 =
          (⨆ a, secondFamily a) ⊓ secondProjectivePatch 57 1 := by
        rw [secondFamily_cover]
        exact (inf_eq_right.mpr (secondProjectivePatch_le_secondCoordinate 57 1)).symm
      _ = ⨆ a, secondFamily a ⊓ secondProjectivePatch 57 1 := iSup_inf_eq _ _
      _ ≤ ⨆ a, patchOpen a := iSup_le (fun a => le_iSup patchOpen (.inr a))
  apply le_antisymm le_top
  simpa only [projective_twoOpen_cover 57 1 (by norm_num)] using sup_le hfirst hsecond

/-- These are the original intrinsic normal frames, restricted to the
specified refinement. In particular their generators are not chosen from
the desired image. -/
def patchFrame : (a : PatchIndex) → LocalFrame Curve.sheaf Normal (patchOpen a)
  | .inl a => restrictFrame (firstNormalFrame 57 1 a.1 a.2) inf_le_left
  | .inr a => restrictFrame (secondNormalFrame 57 1 a.1 a.2) inf_le_left

/-- The actual local contraction of the original glued cubic surface
representative. The first representative is positive, the second negative. -/
def patchForm (p : WeightedCubic) (a : PatchIndex) (W : Curve.Opens)
    (hW : W ≤ patchOpen a) : Differentials.val.obj (op W) :=
  match a with
  | .inl a =>
      chartKaehlerSection (firstNormalCurveChart 57 1 a.1 a.2)
        (projectiveToComplex 57 1) (firstNormalCurveChart_overComplex 57 1 a.1 a.2)
        (Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (firstNormalOpen_preimage 57 1 a.1 a.2).le)))
        (firstNormalAdjunction 57 1 a.1 a.2
          (firstRestrictedPolynomialForm 57 1 a.1 a.2 p.val))
  | .inr a =>
      chartKaehlerSection (secondNormalCurveChart 57 1 a.1 a.2)
        (projectiveToComplex 57 1) (secondNormalCurveChart_overComplex 57 1 a.1 a.2)
        (Over.mk (homOfLE ((hW.trans inf_le_left).trans
          (secondNormalOpen_preimage 57 1 a.1 a.2).le)))
        (secondNormalAdjunction 57 1 a.1 a.2
          (-(secondRestrictedPolynomialForm 57 1 a.1 a.2 p.val)))

/-- Contraction of an arbitrary actual normal section, expressed in the
original normal frame on this subopen. -/
def patchContraction (p : WeightedCubic) (a : PatchIndex) (W : Curve.Opens)
    (hW : W ≤ patchOpen a) :
    Normal.val.obj (op W) →ₗ[Γ(Curve, W)] Differentials.val.obj (op W) :=
  ((patchFrame a).app W hW).toLinearMap.smulRight (patchForm p a W hW)

@[simp] theorem patchContraction_apply (p : WeightedCubic) (a : PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) (s : Normal.val.obj (op W)) :
    patchContraction p a W hW s =
      (patchFrame a).app W hW s • patchForm p a W hW := rfl

/-- The local contraction sends its fixed intrinsic normal generator to
the actual contracted surface form, before any comparison with a model. -/
theorem patchContraction_generator (p : WeightedCubic) (a : PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) :
    patchContraction p a W hW (frameGenerator (patchFrame a) W hW) =
      patchForm p a W hW := by
  change (patchFrame a).app W hW (((patchFrame a).app W hW).symm 1) • _ = _
  rw [LinearEquiv.apply_symm_apply, one_smul]

/-- The existing morphism is retained only as the comparison object. -/
def originalCubicMorphism (p : WeightedCubic) : Normal ⟶ Differentials :=
  intrinsicNormalIso.hom ≫ literalModelCubicDifferential (substitute p.val)
    (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)

private theorem linearFrame_reconstruct {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) (s : M) :
    e s • e.symm 1 = s := by
  apply e.injective
  rw [e.map_smul, LinearEquiv.apply_symm_apply]
  exact mul_one _

theorem originalCubicMorphism_generator (p : WeightedCubic) (a : PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) :
    (originalCubicMorphism p).val.app (op W)
        (frameGenerator (patchFrame a) W hW) = patchForm p a W hW := by
  cases a with
  | inl a =>
      change (originalCubicMorphism p).val.app (op W)
        (frameGenerator (firstNormalFrame 57 1 a.1 a.2) W (hW.trans inf_le_left)) = _
      exact (congrArg ((originalCubicMorphism p).val.app (op W))
        (firstNormalFrame_generator 57 1 a.1 a.2 W (hW.trans inf_le_left))).trans
        (literal_first_cubic_adjunction p a.1 a.2
          (Over.mk (homOfLE ((hW.trans inf_le_left).trans
            (firstNormalOpen_preimage 57 1 a.1 a.2).le))) (hW.trans inf_le_right))
  | inr a =>
      change (originalCubicMorphism p).val.app (op W)
        (frameGenerator (secondNormalFrame 57 1 a.1 a.2) W (hW.trans inf_le_left)) = _
      exact (congrArg ((originalCubicMorphism p).val.app (op W))
        (secondNormalFrame_generator 57 1 a.1 a.2 W (hW.trans inf_le_left))).trans
        (literal_second_cubic_adjunction p a.1 a.2
          (Over.mk (homOfLE ((hW.trans inf_le_left).trans
            (secondNormalOpen_preimage 57 1 a.1 a.2).le))) (hW.trans inf_le_right))

/-- Generator agreement gives the same contraction on every actual normal
section, by the already proved local frame equivalence. -/
theorem patchContraction_eq_original (p : WeightedCubic) (a : PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) (s : Normal.val.obj (op W)) :
    patchContraction p a W hW s = (originalCubicMorphism p).val.app (op W) s := by
  let e := (patchFrame a).app W hW
  let f := ((originalCubicMorphism p).val.app (op W)).hom
  calc
    patchContraction p a W hW s = e s • f (e.symm 1) := by
      exact congrArg (fun z => e s • z)
        (originalCubicMorphism_generator p a W hW).symm
    _ = f (e s • e.symm 1) := (f.map_smul _ _).symm
    _ = f s := congrArg f (linearFrame_reconstruct e s)

theorem patchContraction_agreement (p : WeightedCubic) (a b : PatchIndex)
    (W : Curve.Opens) (ha : W ≤ patchOpen a) (hb : W ≤ patchOpen b)
    (s : Normal.val.obj (op W)) :
    patchContraction p a W ha s = patchContraction p b W hb s :=
  (patchContraction_eq_original p a W ha s).trans
    (patchContraction_eq_original p b W hb s).symm

theorem patchContraction_naturality (p : WeightedCubic) (a : PatchIndex)
    {W V : Curve.Opens} (hVW : V ≤ W) (hW : W ≤ patchOpen a)
    (s : Normal.val.obj (op W)) :
    Differentials.val.map (homOfLE hVW).op (patchContraction p a W hW s) =
      patchContraction p a V (hVW.trans hW)
        (Normal.val.map (homOfLE hVW).op s) := by
  rw [patchContraction_eq_original, patchContraction_eq_original]
  exact (PresheafOfModules.naturality_apply (originalCubicMorphism p).val
    (homOfLE hVW).op s).symm

/-- The prescribed image on one member of the refinement of an arbitrary
open. This definition uses only the actual local contraction above. -/
def patchValue (p : WeightedCubic) (O : Curve.Opens) (s : Normal.val.obj (op O))
    (a : PatchIndex) : Differentials.val.obj (op (O ⊓ patchOpen a)) :=
  patchContraction p a (O ⊓ patchOpen a) inf_le_right
    (Normal.val.map (homOfLE (show O ⊓ patchOpen a ≤ O from inf_le_left)).op s)

theorem patchValue_eq_restriction (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) (a : PatchIndex) :
    patchValue p O s a = res (addSheaf Differentials) inf_le_left
      ((originalCubicMorphism p).val.app (op O) s) := by
  exact (patchContraction_eq_original p a (O ⊓ patchOpen a) inf_le_right _).trans
    (PresheafOfModules.naturality_apply (originalCubicMorphism p).val
      (homOfLE (show O ⊓ patchOpen a ≤ O from inf_le_left)).op s)

private theorem patchValue_compatible (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) :
    TopCat.Presheaf.IsCompatible (addSheaf Differentials).obj
      (fun a => O ⊓ patchOpen a) (patchValue p O s) := by
  intro a b
  change res (addSheaf Differentials) inf_le_left (patchValue p O s a) =
    res (addSheaf Differentials) inf_le_right (patchValue p O s b)
  rw [patchValue_eq_restriction, patchValue_eq_restriction, res_comp, res_comp]

private theorem cover_on (O : Curve.Opens) : O ≤ ⨆ a, O ⊓ patchOpen a := by
  rw [← inf_iSup_eq, patchOpen_cover, inf_top_eq]

/-- Genuine sheaf gluing of the actual local contractions, with uniqueness. -/
theorem contractionSection_existsUnique (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) :
    ∃! t : Differentials.val.obj (op O), ∀ a,
      res (addSheaf Differentials) (show O ⊓ patchOpen a ≤ O from inf_le_left) t =
        patchValue p O s a :=
  (addSheaf Differentials).existsUnique_gluing' (fun a => O ⊓ patchOpen a) O
    (fun _ => homOfLE inf_le_left) (cover_on O) (patchValue p O s)
    (patchValue_compatible p O s)

/-- The section is chosen by its actual contracted restrictions, not by a
cohomology class or a normal-model value. -/
def contractionSection (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) : Differentials.val.obj (op O) :=
  Classical.choose (contractionSection_existsUnique p O s)

theorem contractionSection_restrict (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) (a : PatchIndex) :
    res (addSheaf Differentials) (show O ⊓ patchOpen a ≤ O from inf_le_left)
        (contractionSection p O s) = patchValue p O s a :=
  (Classical.choose_spec (contractionSection_existsUnique p O s)).1 a

theorem contractionSection_eq_original (p : WeightedCubic) (O : Curve.Opens)
    (s : Normal.val.obj (op O)) :
    contractionSection p O s = (originalCubicMorphism p).val.app (op O) s :=
  ((Classical.choose_spec (contractionSection_existsUnique p O s)).2
    ((originalCubicMorphism p).val.app (op O) s)
    (fun a => (patchValue_eq_restriction p O s a).symm)).symm

def contractionSectionLinearMap (p : WeightedCubic) (O : Curve.Opens) :
    Normal.val.obj (op O) →ₗ[Γ(Curve, O)] Differentials.val.obj (op O) where
  toFun := contractionSection p O
  map_add' s t := by
    rw [contractionSection_eq_original, contractionSection_eq_original,
      contractionSection_eq_original, map_add]
  map_smul' a s := by
    rw [contractionSection_eq_original, contractionSection_eq_original, map_smul]

/-- The independently glued contraction morphism of the actual intrinsic
normal sheaf into the actual curve differential sheaf. -/
def literalCubicAdjunction (p : WeightedCubic) : Normal ⟶ Differentials where
  val :=
    { app O := ModuleCat.ofHom (contractionSectionLinearMap p O.unop)
      naturality {O P} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        change contractionSection p P.unop (Normal.val.map f s) =
          Differentials.val.map f (contractionSection p O.unop s)
        rw [contractionSection_eq_original, contractionSection_eq_original]
        exact PresheafOfModules.naturality_apply (originalCubicMorphism p).val f s }

/-- Equality of genuine sheaf morphisms, obtained from the actual local
contractions and the proved generating frames on a covering refinement. -/
theorem literalCubicAdjunction_eq_original (p : WeightedCubic) :
    literalCubicAdjunction p =
      intrinsicNormalIso.hom ≫ literalModelCubicDifferential (substitute p.val)
        (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact contractionSection_eq_original p O.unop s

/-- The global contraction retains the actual local formula on every
normal section of every subopen of the twelve-member refinement. -/
theorem literalCubicAdjunction_on_patch (p : WeightedCubic) (a : PatchIndex)
    (W : Curve.Opens) (hW : W ≤ patchOpen a) (s : Normal.val.obj (op W)) :
    (literalCubicAdjunction p).val.app (op W) s =
      (patchFrame a).app W hW s • patchForm p a W hW :=
  (contractionSection_eq_original p W s).trans
    (patchContraction_eq_original p a W hW s).symm

theorem literalCubicAdjunction_first_local (p : WeightedCubic) (i : Fin 2) (j : Fin 3)
    (W : Curve.Opens) (hN : W ≤ firstFamily (i,j))
    (hQ : W ≤ firstProjectivePatch 57 1) (s : Normal.val.obj (op W)) :
    (literalCubicAdjunction p).val.app (op W) s =
      (firstNormalFrame 57 1 i j).app W hN s •
        chartKaehlerSection (firstNormalCurveChart 57 1 i j)
          (projectiveToComplex 57 1) (firstNormalCurveChart_overComplex 57 1 i j)
          (Over.mk (homOfLE (hN.trans (firstNormalOpen_preimage 57 1 i j).le)))
          (firstNormalAdjunction 57 1 i j (firstRestrictedPolynomialForm 57 1 i j p.val)) :=
  literalCubicAdjunction_on_patch p (.inl (i,j)) W (le_inf hN hQ) s

theorem literalCubicAdjunction_second_local (p : WeightedCubic) (i : Fin 2) (j : Fin 3)
    (W : Curve.Opens) (hN : W ≤ secondFamily (i,j))
    (hQ : W ≤ secondProjectivePatch 57 1) (s : Normal.val.obj (op W)) :
    (literalCubicAdjunction p).val.app (op W) s =
      (secondNormalFrame 57 1 i j).app W hN s •
        chartKaehlerSection (secondNormalCurveChart 57 1 i j)
          (projectiveToComplex 57 1) (secondNormalCurveChart_overComplex 57 1 i j)
          (Over.mk (homOfLE (hN.trans (secondNormalOpen_preimage 57 1 i j).le)))
          (secondNormalAdjunction 57 1 i j (-(secondRestrictedPolynomialForm 57 1 i j p.val))) :=
  literalCubicAdjunction_on_patch p (.inr (i,j)) W (le_inf hN hQ) s

#print axioms patchOpen_cover
#print axioms patchContraction_generator
#print axioms patchContraction_eq_original
#print axioms contractionSection_existsUnique
#print axioms literalCubicAdjunction_eq_original
#print axioms literalCubicAdjunction_first_local
#print axioms literalCubicAdjunction_second_local

end CycleQ2GlobalCubicAdjunction
end

end GlobalCubicAdjunctionGluing

section GlobalCubicAdjunctionCohomology

/-!
# The original normal class under actual cubic adjunction

The map here is the pushforward of the independently glued contraction
on the curve, transported by the genuine normal pushforward isomorphism.
Its comparison with the already checked cubic map is an equality of
actual morphisms. Nonvanishing is preserved by the actual canonical
sheaf isomorphism. No Serre trace or residue connecting map is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GlobalCubicAdjunctionCohomology

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2GlobalCubicAdjunction CycleQ2SeedTrace
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCurveSurface
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricCanonicalSheaf
  CycleQ2GeometricIncidenceJacobianCover CycleQ2CubicDifferentialMap
  CycleQ2IntrinsicNormalModel CycleQ2NormalPushforwardIso
  CycleQ2SurfaceNormalTransport CycleQ2SurfaceNormalCohomology
  CycleQ2IntrinsicSurfaceNormalCohomology CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2SurfaceCubicGluing CycleQ2GluedCubicAdjunction
  CycleQ2GeometricLiteralDirection

abbrev Surface := projectiveSurface (57 : ℂ) 1
abbrev immersion := curveToSurface (57 : ℂ) 1

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

def literalCanonicalModuleIso : degreeOneModuleSheaf 57 1 ≅ Differentials :=
  canonicalSheafIso 57 1 first_chart_jacobianIdeal_eq_top
    second_chart_jacobianIdeal_eq_top (by norm_num)

abbrev pushedDifferentialSheaf :=
  (SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).obj
    ((Scheme.Modules.pushforward immersion).obj Differentials)

/-- The original canonical sheaf isomorphism, pushed along the unchanged
projective curve immersion and then forgetting only the module structure. -/
def surfaceCanonicalIso : pushedDegreeOneSheaf 57 1 ≅ pushedDifferentialSheaf :=
  (SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).mapIso
    ((Scheme.Modules.pushforward immersion).mapIso literalCanonicalModuleIso)

/-- The actual pushed contraction, with source the genuine intrinsic
normal direct image used by the inverse-ideal connecting sequence. -/
def surfaceAdjunctionMorphism (p : WeightedCubic) :
    intrinsicSurfaceNormalSheaf 57 1 ⟶ pushedDifferentialSheaf :=
  (SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).map
    ((actualNormalPushforwardIso 57 1).inv ≫
      (Scheme.Modules.pushforward immersion).map (literalCubicAdjunction p))

private theorem forget_pushforward_map {M N : Curve.Modules} (f : M ⟶ N) :
    (SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).map
        ((Scheme.Modules.pushforward immersion).map f) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} immersion.base).map
        ((SheafOfModules.toSheaf (ringSheaf Curve.sheaf)).map f) := rfl

theorem surfaceAdjunctionMorphism_eq (p : WeightedCubic) :
    surfaceAdjunctionMorphism p =
      literalIntrinsicCubicMorphism (substitute p.val)
        (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property) ≫
          surfaceCanonicalIso.hom := by
  let P := Scheme.Modules.pushforward immersion
  let F := SheafOfModules.toSheaf (ringSheaf Surface.sheaf)
  let c := cubicMorphism 57 1 (by norm_num) (substitute p.val)
    (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)
  have hm : (actualNormalPushforwardIso 57 1).inv ≫ P.map (literalCubicAdjunction p) =
      ((actualNormalPushforwardIso 57 1).inv ≫ P.map intrinsicNormalIso.hom) ≫
        P.map c ≫ P.map literalCanonicalModuleIso.hom := by
    rw [literalCubicAdjunction_eq_original]
    change (actualNormalPushforwardIso 57 1).inv ≫
      P.map (intrinsicNormalIso.hom ≫ (c ≫ literalCanonicalModuleIso.hom)) = _
    simp only [Functor.map_comp, Category.assoc]
  have hF : F.map ((actualNormalPushforwardIso 57 1).inv ≫
      P.map (literalCubicAdjunction p)) =
      (F.map ((actualNormalPushforwardIso 57 1).inv ≫ P.map intrinsicNormalIso.hom) ≫
        F.map (P.map c)) ≫ F.map (P.map literalCanonicalModuleIso.hom) := by
    exact (congrArg F.map hm).trans (by simp only [Functor.map_comp, Category.assoc])
  exact hF.trans (congrArg
    (fun f =>
      (F.map ((actualNormalPushforwardIso 57 1).inv ≫ P.map intrinsicNormalIso.hom) ≫ f) ≫
        F.map (P.map literalCanonicalModuleIso.hom)) (forget_pushforward_map c))

def surfaceCanonicalH1Equiv :
    (pushedDegreeOneSheaf 57 1).H' 1 ⊤ ≃+ pushedDifferentialSheaf.H' 1 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).mapIso
    surfaceCanonicalIso).app (op ⊤)).addCommGroupIsoToAddEquiv

def surfaceAdjunctionH1 (p : WeightedCubic) :
    IntrinsicNormalH1 57 1 →+ pushedDifferentialSheaf.H' 1 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).map
    (surfaceAdjunctionMorphism p)).app (op ⊤)).hom

theorem surfaceAdjunctionH1_factor (p : WeightedCubic) (x : IntrinsicNormalH1 57 1) :
    surfaceAdjunctionH1 p x = surfaceCanonicalH1Equiv
      (literalIntrinsicCubicH1Map (substitute p.val)
        (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property) x) := by
  let H := Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1
  change ((H.map (surfaceAdjunctionMorphism p)).app (op ⊤)) x = _
  rw [surfaceAdjunctionMorphism_eq]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op ⊤)) (H.map_comp
      (literalIntrinsicCubicMorphism (substitute p.val)
        (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property))
      surfaceCanonicalIso.hom)) x

/-- The original reduced inverse-ideal class retains its fixed negative
Cech/Mayer--Vietoris normalization under every actual cubic contraction. -/
theorem originalNormalClass_adjunction_image (p : WeightedCubic) :
    surfaceAdjunctionH1 p literalNormalClassAtTop =
      -(surfaceCanonicalH1Equiv
        (cubicH1OnSurface 57 1 (by norm_num) (substitute p.val)
          (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)
          literalNormalClassOnSurface)) := by
  rw [surfaceAdjunctionH1_factor, literalNormalClassAtTop_cubic_image, map_neg]

/-- The original reduced inverse-ideal class has nonzero image under the
actual glued adjunction morphism for the original selected surface cubic. -/
theorem originalNormalClass_selected_adjunction_ne_zero :
    surfaceAdjunctionH1 originalSelectedCubic literalNormalClassAtTop ≠ 0 := by
  rw [surfaceAdjunctionH1_factor]
  intro hz
  have hz' := surfaceCanonicalH1Equiv.injective
    (hz.trans surfaceCanonicalH1Equiv.map_zero.symm)
  apply literalNormalClassAtTop_selected_cubic_image_ne_zero
  simpa only [originalSelectedCubic_substitute] using hz'

#print axioms surfaceAdjunctionMorphism_eq
#print axioms surfaceAdjunctionH1_factor
#print axioms originalNormalClass_adjunction_image
#print axioms originalNormalClass_selected_adjunction_ne_zero

end CycleQ2GlobalCubicAdjunctionCohomology
end

end GlobalCubicAdjunctionCohomology

section GlobalCubicAdjunctionIncidenceTests

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GlobalCubicAdjunctionCohomology

open CycleQ2IntrinsicSurfaceNormalCohomology
  CycleQ2GluedCubicAdjunction CycleQ2SeedTrace

/-- The separate original incidence class is killed by each of the seven
original test cubics under the actual glued contraction. This statement
retains that incidence class; it does not identify it with the original
ambient normal class whose selected cubic image is nonzero. -/
theorem incidenceClass_test_adjunction_zero (j : Fin 7) :
    surfaceAdjunctionH1 (originalTestCubic j) literalIntrinsicIncidenceClass = 0 := by
  rw [surfaceAdjunctionH1_factor]
  have h : literalIntrinsicCubicH1Map (substitute (originalTestCubic j).val)
      (CycleQ2GeometricLiteralSurface.substitute_homogeneous (originalTestCubic j).property)
      literalIntrinsicIncidenceClass = 0 := by
    simpa only [originalTestCubic_substitute] using
      literalIntrinsicIncidenceClass_in_seven_kernels j
  rw [h, map_zero]

#print axioms incidenceClass_test_adjunction_zero

end CycleQ2GlobalCubicAdjunctionCohomology
end

end GlobalCubicAdjunctionIncidenceTests
