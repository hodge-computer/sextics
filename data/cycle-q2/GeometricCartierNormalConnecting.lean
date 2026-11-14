import Proposal.GeometricCartierCechConnecting
import Proposal.GeometricSurfaceResidueFunctoriality
import Proposal.GeometricNormalSheafComparison
import Proposal.GeometricCartierDeformation
import Proposal.GeometricCartierOrdinaryScalar

/-! Checked components of the original normalized intrinsic normal class
and its actual Cartier boundary. Every component body is retained verbatim. -/

section CheckedCartierNormalPart01

/-!
# A supported four-open cocycle and the original two-open boundary

The first two opens refine the two members of an actual Mayer--Vietoris
cover.  The other two lie in the overlap, where the given section vanishes.
The resulting six-edge cocycle has only its first edge nonzero.  Its
injective comparison is the negative of the original Mayer--Vietoris
boundary: the two constructions use opposite degree-zero differences.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechOneMayerVietoris

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace Topology
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechTwoComparison CycleQ2CechOneConnecting CycleQ2ClosedSupportCohomology

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (U : Fin 4 → Opens X)

/-- Actual open inclusions of the four-cover into the original two-cover. -/
structure SupportedRefinement where
  left : Opens X
  right : Opens X
  overlap : Opens X
  overlap_eq : overlap = left ⊓ right
  cover : left ⊔ right = ⊤
  first_le : U 0 ≤ left
  second_le : U 1 ≤ right
  third_le : U 2 ≤ overlap
  fourth_le : U 3 ≤ overlap

namespace SupportedRefinement
variable {U} (D : SupportedRefinement U)

def square : (Opens.grothendieckTopology X).MayerVietorisSquare :=
  coverSquare D.left D.right D.overlap D.overlap_eq D.cover

theorem overlap_left : D.overlap ≤ D.left := D.overlap_eq.le.trans inf_le_left
theorem overlap_right : D.overlap ≤ D.right := D.overlap_eq.le.trans inf_le_right

theorem edge_le : U 0 ⊓ U 1 ≤ D.overlap :=
  (le_inf (inf_le_left.trans D.first_le) (inf_le_right.trans D.second_le)).trans
    D.overlap_eq.ge

def edge (z : Sections F D.overlap) : One F U :=
  ⟨res F D.edge_le z, 0, 0, 0, 0, 0⟩

structure LiftData (z : Sections F D.overlap) where
  leftLift : Sections (presentation F).X₂ D.left
  left_restriction : res (presentation F).X₂ D.overlap_left leftLift =
    app (presentation F).f D.overlap z
  quotientGlobal : Sections (presentation F).X₃ ⊤
  quotient_left : res (presentation F).X₃ le_top quotientGlobal =
    -app (presentation F).g D.left leftLift
  quotient_right : res (presentation F).X₃ (show D.right ≤ ⊤ from le_top) quotientGlobal = 0

theorem liftData_nonempty (z : Sections F D.overlap) : Nonempty (D.LiftData z) := by
  obtain ⟨e,he⟩ := injective_restriction_surjective (presentation F).X₂
    D.overlap_left (app (presentation F).f D.overlap z)
  have heOn (W : Opens X) (hW : W ≤ D.overlap) :
      res (presentation F).X₂ (hW.trans D.overlap_left) e =
        app (presentation F).f W (res F hW z) := by
    have h := congrArg (res (presentation F).X₂ hW) he
    rw [res_comp, ← app_res] at h
    exact h
  obtain ⟨t,ht,-⟩ := existsUnique_pair (presentation F).X₃ ⊤ D.left D.right
    le_top le_top D.cover.ge (-app (presentation F).g D.left e) 0 (by
      intro W hL hR
      have hW : W ≤ D.overlap := (le_inf hL hR).trans D.overlap_eq.ge
      rw [map_neg, ← app_res, heOn W hW, app_comp, (presentation F).zero,
        app_zero, neg_zero, map_zero])
  exact ⟨⟨e,he,t,ht.1,ht.2⟩⟩

namespace LiftData
variable {D} {z : Sections F D.overlap} (d : D.LiftData z)

theorem left_on (W : Opens X) (hW : W ≤ D.overlap) :
    res (presentation F).X₂ (hW.trans D.overlap_left) d.leftLift =
      app (presentation F).f W (res F hW z) := by
  have h := congrArg (res (presentation F).X₂ hW) d.left_restriction
  rw [res_comp, ← app_res] at h
  exact h

def primitive : Zero (presentation F).X₂ U :=
  Fin.cases (-res (presentation F).X₂ D.first_le d.leftLift) (fun _ => 0)

theorem primitive_differential
    (hz₂ : res F D.third_le z=0) (hz₃ : res F D.fourth_le z=0) :
    d0 (presentation F).X₂ U d.primitive = mapOne U (presentation F).f (D.edge z) := by
  have h₂ : res (presentation F).X₂ (D.third_le.trans D.overlap_left) d.leftLift=0 := by
    rw [d.left_on (U 2) D.third_le, hz₂, map_zero]
  have h₃ : res (presentation F).X₂ (D.fourth_le.trans D.overlap_left) d.leftLift=0 := by
    rw [d.left_on (U 3) D.fourth_le, hz₃, map_zero]
  apply Prod.ext
  · change res (presentation F).X₂ inf_le_right 0 -
      res (presentation F).X₂ inf_le_left (-res (presentation F).X₂ D.first_le d.leftLift) = _
    simp only [map_zero, map_neg, zero_sub, neg_neg, res_comp]
    exact d.left_on _ D.edge_le
  · apply Prod.ext
    · change res (presentation F).X₂ inf_le_right 0 -
        res (presentation F).X₂ inf_le_left (-res (presentation F).X₂ D.first_le d.leftLift) =
          app (presentation F).f _ 0
      simp only [map_zero, map_neg, zero_sub, neg_neg, res_comp]
      have h := congrArg (res (presentation F).X₂ (inf_le_right : U 0 ⊓ U 2 ≤ U 2)) h₂
      simpa only [res_comp, map_zero] using h
    · apply Prod.ext
      · change res (presentation F).X₂ inf_le_right 0 -
          res (presentation F).X₂ inf_le_left (-res (presentation F).X₂ D.first_le d.leftLift) =
            app (presentation F).f _ 0
        simp only [map_zero, map_neg, zero_sub, neg_neg, res_comp]
        have h := congrArg (res (presentation F).X₂ (inf_le_right : U 0 ⊓ U 3 ≤ U 3)) h₃
        simpa only [res_comp, map_zero] using h
      · apply Prod.ext
        · change res (presentation F).X₂ inf_le_right 0 -
            res (presentation F).X₂ inf_le_left 0 = app (presentation F).f _ 0
          simp only [map_zero, sub_self]
        · apply Prod.ext
          · change res (presentation F).X₂ inf_le_right 0 -
              res (presentation F).X₂ inf_le_left 0 = app (presentation F).f _ 0
            simp only [map_zero, sub_self]
          · change res (presentation F).X₂ inf_le_right 0 -
              res (presentation F).X₂ inf_le_left 0 = app (presentation F).f _ 0
            simp only [map_zero, sub_self]

theorem global_restriction : globalZero U d.quotientGlobal =
    mapZero U (presentation F).g d.primitive := by
  funext i
  fin_cases i
  · change res (presentation F).X₃ le_top d.quotientGlobal =
      app (presentation F).g (U 0) (-res (presentation F).X₂ D.first_le d.leftLift)
    rw [← res_comp (presentation F).X₃ (show D.left ≤ ⊤ from le_top) D.first_le,
      d.quotient_left, map_neg, map_neg, app_res]
  · change res (presentation F).X₃ le_top d.quotientGlobal = app (presentation F).g (U 1) 0
    rw [← res_comp (presentation F).X₃ (show D.right ≤ ⊤ from le_top) D.second_le,
      d.quotient_right, map_zero, map_zero]
  · change res (presentation F).X₃ le_top d.quotientGlobal = app (presentation F).g (U 2) 0
    rw [← res_comp (presentation F).X₃ (show D.right ≤ ⊤ from le_top)
      (D.third_le.trans D.overlap_right), d.quotient_right, map_zero, map_zero]
  · change res (presentation F).X₃ le_top d.quotientGlobal = app (presentation F).g (U 3) 0
    rw [← res_comp (presentation F).X₃ (show D.right ≤ ⊤ from le_top)
      (D.fourth_le.trans D.overlap_right), d.quotient_right, map_zero, map_zero]

def descent (hz₂ : res F D.third_le z=0) (hz₃ : res F D.fourth_le z=0) :
    OneDescent U (D.edge z) where
  primitive := d.primitive
  differential := d.primitive_differential hz₂ hz₃
  globalSection := d.quotientGlobal
  global_restriction := d.global_restriction

end LiftData

theorem edge_closed (z : Sections F D.overlap)
    (hz₂ : res F D.third_le z=0) (hz₃ : res F D.fourth_le z=0) :
    d1 F U (D.edge z)=0 := by
  obtain ⟨d⟩ := D.liftData_nonempty z
  apply mapTwo_injective U (presentation F).f
  rw [mapTwo_d1, ← d.primitive_differential hz₂ hz₃, d1_d0, mapTwo_zero]

end SupportedRefinement

private def sectionHom (V : Opens X) (x : Sections F V) : freeOpen V ⟶ F :=
  (freeOpenSections F V).symm x

private theorem sectionHom_section (V : Opens X) (x : Sections F V) :
    freeOpenSections F V (sectionHom V x)=x := AddEquiv.apply_symm_apply _ _

private theorem sectionHom_restrict {V W : Opens X} (h : W ≤ V) (x : Sections F V) :
    freeOpenMap h ≫ sectionHom V x = sectionHom W (res F h x) := by
  apply (freeOpenSections F W).injective
  rw [freeOpenSections_naturality, sectionHom_section, sectionHom_section]

private theorem sectionHom_postcomp (f : F ⟶ G) (V : Opens X) (x : Sections F V) :
    sectionHom V x ≫ f = sectionHom V (app f V x) := by
  apply (freeOpenSections G V).injective
  rw [← freeOpenSections_postcomp, sectionHom_section, sectionHom_section]

private theorem sections_biprod_lift {O V W : Opens X} (hV : O ≤ V) (hW : O ≤ W)
    (v : Sections F V) (w : Sections F W) :
    freeOpenSections F O
      (biprod.lift (freeOpenMap hV) (-(freeOpenMap hW)) ≫
        biprod.desc (sectionHom V v) (sectionHom W w)) =
      res F hV v - res F hW w := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, map_sub,
    freeOpenSections_naturality, freeOpenSections_naturality,
    sectionHom_section, sectionHom_section]

private theorem sectionExtZero_eq_hzero (V : Opens X) (x : Sections F V) :
    sectionExtZero V x = (CycleQ2GeometricConeCech.HZero.sectionsEquiv F V).symm x := by
  apply (CycleQ2GeometricConeCech.HZero.sectionsEquiv F V).injective
  rw [AddEquiv.apply_symm_apply]
  unfold sectionExtZero
  rw [CycleQ2GeometricConeCech.HZero.sectionsEquiv_mk₀]
  exact sectionHom_section V x

private theorem sectionBoundary_eq_ext
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (z : Sections F S.X₁) :
    sectionBoundary F S z =
      S.shortComplex_shortExact.extClass.comp (sectionExtZero S.X₁ z) (add_zero 1) := by
  change S.shortComplex_shortExact.extClass.comp
    ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F S.X₁).symm z) (add_zero 1) = _
  rw [sectionExtZero_eq_hzero]

namespace SupportedRefinement.LiftData
variable {U} {D : SupportedRefinement U} {z : Sections F D.overlap} (d : D.LiftData z)

private def mvMiddle : D.square.shortComplex.X₂ ⟶ (presentation F).X₂ :=
  biprod.desc (sectionHom D.left (-d.leftLift)) (sectionHom D.right 0)

private theorem mv_first_comm :
    sectionHom D.overlap (-z) ≫ (presentation F).f =
      D.square.shortComplex.f ≫ d.mvMiddle := by
  apply (freeOpenSections (presentation F).X₂ D.overlap).injective
  rw [sectionHom_postcomp, sectionHom_section]
  change _ = freeOpenSections (presentation F).X₂ D.overlap
    (biprod.lift (freeOpenMap D.overlap_left) (-(freeOpenMap D.overlap_right)) ≫
      biprod.desc (sectionHom D.left (-d.leftLift)) (sectionHom D.right 0))
  rw [sections_biprod_lift, map_neg, map_neg, map_zero, sub_zero, d.left_restriction]

private def mvComparison : D.square.shortComplex ⟶ presentation F where
  τ₁ := sectionHom D.overlap (-z)
  τ₂ := d.mvMiddle
  τ₃ := sectionHom ⊤ d.quotientGlobal
  comm₁₂ := d.mv_first_comm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [mvMiddle, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inl_desc_assoc]
      change sectionHom D.left (-d.leftLift) ≫ (presentation F).g =
        freeOpenMap le_top ≫ sectionHom ⊤ d.quotientGlobal
      rw [sectionHom_postcomp, sectionHom_restrict, d.quotient_left, map_neg]
    · simp only [mvMiddle, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inr_desc_assoc]
      change sectionHom D.right 0 ≫ (presentation F).g =
        freeOpenMap le_top ≫ sectionHom ⊤ d.quotientGlobal
      rw [sectionHom_postcomp, sectionHom_restrict, d.quotient_right, map_zero]

theorem class_eq_neg_boundary (hz₂ : res F D.third_le z=0) (hz₃ : res F D.fourth_le z=0) :
    oneDescentClass U (d.descent hz₂ hz₃) = -sectionBoundary F D.square z := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    D.square.shortComplex_shortExact (presentation_shortExact F) d.mvComparison
  have he : sectionBoundary F D.square (-z) = oneDescentClass U (d.descent hz₂ hz₃) := by
    rw [sectionBoundary_eq_ext]
    exact hn
  rw [map_neg] at he
  exact he.symm

end SupportedRefinement.LiftData

theorem supported_cechOne_eq_neg_boundary (hcover : (⨆ i, U i) = ⊤)
    (D : SupportedRefinement U) (z : Sections F D.overlap)
    (hz₂ : res F D.third_le z=0) (hz₃ : res F D.fourth_le z=0)
    (hc : d1 F U (D.edge z)=0) :
    cechOneClass U hcover (D.edge z) hc = -sectionBoundary F D.square z := by
  obtain ⟨d⟩ := D.liftData_nonempty z
  rw [cechOneClass_eq_descentClass U hcover _ hc (d.descent hz₂ hz₃)]
  exact d.class_eq_neg_boundary hz₂ hz₃

theorem cechOneClass_congr (hcover : (⨆ i, U i) = ⊤)
    {c c' : One F U} (h : c=c') (hc : d1 F U c=0) (hc' : d1 F U c'=0) :
    cechOneClass U hcover c hc = cechOneClass U hcover c' hc' := by
  subst c'
  rfl

/-- The exact sign of the standard coefficient boundary on the original
two-open class, after the genuine supported four-open refinement. -/
theorem supported_coefficient_connecting (hcover : (⨆ i, U i) = ⊤)
    {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (D : SupportedRefinement U) (z : Sections S.X₃ D.overlap)
    (hz₂ : res S.X₃ D.third_le z=0) (hz₃ : res S.X₃ D.fourth_le z=0)
    (ν : One S.X₂ U) (b : Two S.X₁ U) (hb : d2 S.X₁ U b=0)
    (hν : d1 S.X₂ U ν = mapTwo U S.f b)
    (hred : mapOne U S.g ν = D.edge z) :
    (sectionBoundary S.X₃ D.square z).comp hS.extClass rfl =
      -cechTwoClass U hcover b hb := by
  have hclass := (cechOneClass_congr U hcover hred (reduction_closed U ν b hν)
    (D.edge_closed z hz₂ hz₃)).trans
      (supported_cechOne_eq_neg_boundary U hcover D z hz₂ hz₃ _)
  have hδ := coefficient_connecting U hcover hS ν b hb hν
  rw [hclass, Ext.neg_comp] at hδ
  exact neg_eq_iff_eq_neg.mp hδ

/-- An open of the ambient space lies in the canonical extension exactly
when its actual preimage lies in the original closed-subspace open. -/
theorem le_extendedOpen_iff {Y : TopCat.{0}} (j : X ⟶ Y) (hj : IsClosedEmbedding j)
    (V : Opens Y) (W : Opens X) :
    V ≤ extendedOpen j hj W ↔ (Opens.map j).obj V ≤ W := by
  constructor
  · intro h x hx
    have he := h hx
    by_contra hn
    exact he ⟨x,hn,rfl⟩
  · intro h y hy
    rintro ⟨x,hx,rfl⟩
    exact hx (h hy)

section ClosedSupport
variable {Y : TopCat.{0}} (j : X ⟶ Y) (hj : IsClosedEmbedding j)
variable (F : AbSheaf X) (A B W : Opens X) (hW : W=A⊓B) (hAB : A⊔B=⊤)
variable (V : Fin 4 → Opens Y)
  (h₀ : (Opens.map j).obj (V 0)=A) (h₁ : (Opens.map j).obj (V 1)=B)
  (h₂ : (Opens.map j).obj (V 2)=⊥) (h₃ : (Opens.map j).obj (V 3)=⊥)

/-- The existing surface four-cover genuinely refines the closed-support
Mayer--Vietoris cover of the original two curve opens. -/
def closedSupportRefinement : SupportedRefinement V where
  left := extendedOpen j hj A
  right := extendedOpen j hj B
  overlap := extendedOpen j hj W
  overlap_eq := (congrArg (extendedOpen j hj) hW).trans (extendedOpen_inf j hj A B)
  cover := extendedOpen_cover j hj A B hAB
  first_le := (le_extendedOpen_iff j hj _ A).mpr h₀.le
  second_le := (le_extendedOpen_iff j hj _ B).mpr h₁.le
  third_le := (le_extendedOpen_iff j hj _ W).mpr (h₂.le.trans bot_le)
  fourth_le := (le_extendedOpen_iff j hj _ W).mpr (h₃.le.trans bot_le)

private theorem directImage_empty_subsingleton (O : Opens Y)
    (hO : (Opens.map j).obj O=⊥) :
    Subsingleton ((directImage j F).obj.obj (op O)) := by
  change Subsingleton (F.obj.obj (op ((Opens.map j).obj O)))
  rw [hO]
  have ht : IsTerminal (F.obj.obj (op (⊥ : Opens X))) :=
    TopCat.Sheaf.isTerminalOfEmpty (show TopCat.Sheaf AddCommGrpCat X from F)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp ht.isZero

/-- No comparison of different classes is assumed: the single retained
edge is the original section under the actual closed-image section map. -/
theorem closedSupport_cechOne_eq_neg_pushforwardBoundary
    (hcover : (⨆ i, V i)=⊤) (z : Sections F W) :
    let D := closedSupportRefinement j hj A B W hW hAB V h₀ h₁ h₂ h₃
    let z' := (pushedSectionsEquiv j hj F W).symm z
    ∃ hc : d1 (directImage j F) V (D.edge z')=0,
      cechOneClass V hcover (D.edge z') hc =
        -CycleQ2ClosedSupportBoundary.pushforwardBoundary j hj F A B W hW hAB z := by
  let D := closedSupportRefinement j hj A B W hW hAB V h₀ h₁ h₂ h₃
  let z' := (pushedSectionsEquiv j hj F W).symm z
  have hz₂ : res (directImage j F) D.third_le z'=0 :=
    @Subsingleton.elim _ (directImage_empty_subsingleton j F (V 2) h₂) _ _
  have hz₃ : res (directImage j F) D.fourth_le z'=0 :=
    @Subsingleton.elim _ (directImage_empty_subsingleton j F (V 3) h₃) _ _
  refine ⟨D.edge_closed z' hz₂ hz₃, ?_⟩
  exact supported_cechOne_eq_neg_boundary V hcover D z' hz₂ hz₃ _

end ClosedSupport

#print axioms SupportedRefinement.edge_closed
#print axioms supported_cechOne_eq_neg_boundary
#print axioms supported_coefficient_connecting
#print axioms le_extendedOpen_iff
#print axioms closedSupportRefinement
#print axioms closedSupport_cechOne_eq_neg_pushforwardBoundary

end CycleQ2CechOneMayerVietoris
end

end CheckedCartierNormalPart01

section CheckedCartierNormalPart02

/-!
# The original intrinsic normal class as an actual section boundary

The existing cohomological transport through the proved normal-sheaf
isomorphism is rewritten using Mayer--Vietoris naturality.  This retains
the original overlap section and its normalization.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IntrinsicNormalBoundary

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2ClosedSupportCohomology CycleQ2ClosedSupportBoundary
  CycleQ2SurfaceNormalCohomology CycleQ2SurfaceNormalTransport
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricLiteralCanonicalClass CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCurveSurface CycleQ2SourceNormalSheaf CycleQ2SeedTrace

variable (r θ : ℂ)

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

def normalTargetSquare (hr : r ≠ 0) :
    (Opens.grothendieckTopology (projectiveSurface r θ)).MayerVietorisSquare :=
  targetCoverSquare (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (projective_twoOpen_cover r θ hr)

abbrev normalTargetOverlap : Opens (projectiveSurface r θ) :=
  extendedOpen (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (overlapProjectivePatch r θ)

def modelOverlapSection (p : Poly) (hp : p.IsHomogeneous 6) :
    (pushedNormalSheaf r θ).obj.obj (op (normalTargetOverlap r θ)) :=
  (pushedSectionsEquiv (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (normalAdditiveSheaf r θ) (overlapProjectivePatch r θ)).symm
      (normalOverlapSection r θ p hp)

variable (e : actualNormal r θ ≅ normalModuleSheaf r θ)

/-- The original overlap section in the genuine intrinsic normal sheaf,
transported by the inverse of the actual proved sheaf isomorphism. -/
def intrinsicOverlapSection (p : Poly) (hp : p.IsHomogeneous 6) :
    (intrinsicSurfaceNormalSheaf r θ).obj.obj (op (normalTargetOverlap r θ)) :=
  (surfaceNormalAdditiveIso r θ e).inv.hom.app (op (normalTargetOverlap r θ))
    (modelOverlapSection r θ p hp)

theorem intrinsicOverlapSection_to_model (p : Poly) (hp : p.IsHomogeneous 6) :
    (surfaceNormalAdditiveIso r θ e).hom.hom.app (op (normalTargetOverlap r θ))
      (intrinsicOverlapSection r θ e p hp) = modelOverlapSection r θ p hp := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (normalTargetOverlap r θ)))
      (surfaceNormalAdditiveIso r θ e).inv_hom_id) _

/-- This is an equality of the original cohomology class with the actual
Mayer--Vietoris boundary, not a new definition of that class. -/
theorem intrinsicNormalClass_eq_boundary (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    intrinsicNormalClass r θ e hr p hp =
      sectionBoundary (intrinsicSurfaceNormalSheaf r θ) (normalTargetSquare r θ hr)
        (intrinsicOverlapSection r θ e p hp) := by
  exact sectionBoundary_map (surfaceNormalAdditiveIso r θ e).inv
    (normalTargetSquare r θ hr) (modelOverlapSection r θ p hp)

#print axioms intrinsicOverlapSection_to_model
#print axioms intrinsicNormalClass_eq_boundary

end CycleQ2IntrinsicNormalBoundary
end

end CheckedCartierNormalPart02

section CheckedCartierNormalPart03

/-!
# The original intrinsic normal class on the actual surface four-cover

The two quartic curve opens extend to a genuine cover of the ambient
surface.  The actual Cartier four-cover refines it, and the two extra
opens have empty curve preimage.  The resulting positive 01 cocycle
represents the negative of the unchanged original normal class.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IntrinsicNormalRefinement

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechOneConnecting CycleQ2CechOneMayerVietoris
  CycleQ2ClosedSupportCohomology CycleQ2SurfaceNormalCohomology
  CycleQ2SurfaceNormalTransport CycleQ2IntrinsicNormalBoundary
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCurveSurface CycleQ2SourceNormalSheaf
  CycleQ2SeedTrace

variable (r θ : ℂ) (hr : r ≠ 0)

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The actual product-defined 01 surface patch pulls back to the
original quartic overlap on the curve. -/
theorem normalCoverOverlap_preimage :
    curveToSurface r θ ⁻¹ᵁ coverPatch r θ {0,1} = overlapProjectivePatch r θ := by
  rw [coverPatch_pair, Scheme.Hom.preimage_inf,
    curveToSurface_preimage_cover_zero, curveToSurface_preimage_cover_one]
  exact (overlapProjectivePatch_eq r θ).symm

theorem normalCoverOverlap_le_target :
    coverPatch r θ {0,1} ≤ normalTargetOverlap r θ :=
  (le_extendedOpen_iff (curveToSurface r θ).base (curveClosedEmbedding r θ) _ _).mpr
    (normalCoverOverlap_preimage r θ).le

def normalRefinement : SupportedRefinement (coverFamily r θ) :=
  closedSupportRefinement (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (projective_twoOpen_cover r θ hr) (coverFamily r θ)
    (curveToSurface_preimage_cover_zero r θ) (curveToSurface_preimage_cover_one r θ)
    (curveToSurface_preimage_cover_two r θ) (curveToSurface_preimage_cover_three r θ)

variable (e : actualNormal r θ ≅ normalModuleSheaf r θ)

include e in
/-- The actual intrinsic normal sheaf has zero sections on each open
whose preimage in the original curve is empty. -/
theorem intrinsicNormal_sections_empty (V : Opens (projectiveSurface r θ))
    (hV : curveToSurface r θ ⁻¹ᵁ V = ⊥) :
    Subsingleton ((intrinsicSurfaceNormalSheaf r θ).obj.obj (op V)) := by
  have : Subsingleton ((pushedNormalSheaf r θ).obj.obj (op V)) := by
    change Subsingleton ((normalAdditiveSheaf r θ).obj.obj
      (op (curveToSurface r θ ⁻¹ᵁ V)))
    rw [hV]
    have ht : IsTerminal ((normalAdditiveSheaf r θ).obj.obj
        (op (⊥ : Opens (projectiveCurve r θ)))) :=
      TopCat.Sheaf.isTerminalOfEmpty
        (show TopCat.Sheaf AddCommGrpCat (projectiveCurve r θ) from normalAdditiveSheaf r θ)
    exact AddCommGrpCat.isZero_iff_subsingleton.mp ht.isZero
  exact (app_injective (surfaceNormalAdditiveIso r θ e).hom V).subsingleton

def intrinsicNormalCocycle (p : Poly) (hp : p.IsHomogeneous 6) :
    One (intrinsicSurfaceNormalSheaf r θ) (coverFamily r θ) :=
  (normalRefinement r θ hr).edge (intrinsicOverlapSection r θ e p hp)

theorem intrinsicNormalCocycle_closed (p : Poly) (hp : p.IsHomogeneous 6) :
    d1 (intrinsicSurfaceNormalSheaf r θ) (coverFamily r θ)
      (intrinsicNormalCocycle r θ hr e p hp)=0 := by
  apply (normalRefinement r θ hr).edge_closed
  · exact @Subsingleton.elim _
      (intrinsicNormal_sections_empty r θ e (coverFamily r θ 2)
        (curveToSurface_preimage_cover_two r θ)) _ _
  · exact @Subsingleton.elim _
      (intrinsicNormal_sections_empty r θ e (coverFamily r θ 3)
        (curveToSurface_preimage_cover_three r θ)) _ _

/-- The genuine four-to-two comparison fixes the sign of the original
normal class without changing its overlap representative or normalization. -/
theorem intrinsicNormalCocycle_class (p : Poly) (hp : p.IsHomogeneous 6) :
    cechOneClass (coverFamily r θ) (projective_four_cover r θ hr)
      (intrinsicNormalCocycle r θ hr e p hp)
      (intrinsicNormalCocycle_closed r θ hr e p hp) =
        -intrinsicNormalClass r θ e hr p hp := by
  have h := supported_cechOne_eq_neg_boundary (coverFamily r θ)
    (projective_four_cover r θ hr) (normalRefinement r θ hr)
    (intrinsicOverlapSection r θ e p hp)
    (@Subsingleton.elim _
      (intrinsicNormal_sections_empty r θ e (coverFamily r θ 2)
        (curveToSurface_preimage_cover_two r θ)) _ _)
    (@Subsingleton.elim _
      (intrinsicNormal_sections_empty r θ e (coverFamily r θ 3)
        (curveToSurface_preimage_cover_three r θ)) _ _)
    (intrinsicNormalCocycle_closed r θ hr e p hp)
  exact h.trans (congrArg Neg.neg (intrinsicNormalClass_eq_boundary r θ e hr p hp).symm)

#print axioms normalCoverOverlap_preimage
#print axioms normalCoverOverlap_le_target
#print axioms normalRefinement
#print axioms intrinsicNormal_sections_empty
#print axioms intrinsicNormalCocycle_closed
#print axioms intrinsicNormalCocycle_class

end CycleQ2IntrinsicNormalRefinement
end

end CheckedCartierNormalPart03

section CheckedCartierNormalPart04

/-!
# Coefficient-boundary argument from the exact original overlap reduction

This core separates the coefficient-boundary argument from the geometric
reduction supplied by the final closed module. The incoming actual inverse-ideal
one-cochain has positive edge 01. Its
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
namespace CycleQ2OriginalCartierConnectingCore

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechOneConnecting CycleQ2CechOneMayerVietoris
  CycleQ2IntrinsicNormalBoundary CycleQ2IntrinsicNormalRefinement
  CycleQ2IntrinsicNormalModel CycleQ2IntrinsicSurfaceNormalCohomology
  CycleQ2SurfaceNormalTransport CycleQ2CartierProjectiveCover
  CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricLiteralDirection CycleQ2SeedTrace
  CycleQ2ProjectiveInverseIdeal
  CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2GeometricSheafCohomologyRestriction

open CycleQ2ProjectiveCartierIntersections (literal_cover sectionEquivOfOpenEq)
open CycleQ2ProjectiveCartierDerived
  (literalCocycle literalCocycle_closed literalDerivedClassAtTop
   literalDerivedClassAtTop_ne_zero literalTerminalCohomologyEquiv
   literalDerivedClass literalDerivedClass_ne_zero)

local instance : HasExt.{1} (AbSheaf (projectiveSurface 57 1)) := HasExt.standard _

/-- The positive 01 cocycle of the original normalized intrinsic normal
overlap section on the actual four-open surface cover. -/
def originalCocycle : One literalSequence.X₃ (coverFamily 57 1) :=
  intrinsicNormalCocycle 57 1 (by norm_num) intrinsicNormalIso
    ambientNormalNumerator ambientNormalNumerator_homogeneous

theorem originalCocycle_closed :
    d1 literalSequence.X₃ (coverFamily 57 1) originalCocycle = 0 :=
  intrinsicNormalCocycle_closed 57 1 (by norm_num) intrinsicNormalIso
    ambientNormalNumerator ambientNormalNumerator_homogeneous

/-- This comparison retains the original normal-frame normalization and
the sign of the existing Mayer--Vietoris boundary. -/
theorem originalCocycle_class :
    CycleQ2CechOneConnecting.cechOneClass (coverFamily 57 1) literal_cover
      originalCocycle originalCocycle_closed = -literalIntrinsicNormalClass :=
  intrinsicNormalCocycle_class 57 1 (by norm_num) intrinsicNormalIso
    ambientNormalNumerator ambientNormalNumerator_homogeneous

/-- The precise section-level reduction used by the coefficient argument.
The final closed module supplies this equality from actual inverse-ideal evaluation. -/
abbrev ReductionHolds : Prop :=
  app literalSequence.g (coverPatch 57 1 {0,1}) literalConnectingEdge =
    res literalSequence.X₃ (normalCoverOverlap_le_target 57 1)
      (intrinsicOverlapSection 57 1 intrinsicNormalIso
        ambientNormalNumerator ambientNormalNumerator_homogeneous)

/-- The section-level reduction on the genuine product open transports
naturally to its equal binary intersection. All five other edges remain zero. -/
theorem literalConnectingOne_reduction (hred : ReductionHolds) :
    mapOne (coverFamily 57 1) literalSequence.g literalConnectingOne =
      originalCocycle := by
  have he :
      app literalSequence.g (coverPatch 57 1 {0,1}) literalConnectingEdge =
        res literalSequence.X₃ (normalCoverOverlap_le_target 57 1)
          (intrinsicOverlapSection 57 1 intrinsicNormalIso
            ambientNormalNumerator ambientNormalNumerator_homogeneous) :=
    hred
  have hfirst :
      app literalSequence.g (coverFamily 57 1 0 ⊓ coverFamily 57 1 1)
        (sectionEquivOfOpenEq literalSequence.X₂ (coverPatch_pair 57 1 0 1)
          literalConnectingEdge) =
        res literalSequence.X₃ (normalRefinement 57 1 (by norm_num)).edge_le
          (intrinsicOverlapSection 57 1 intrinsicNormalIso
            ambientNormalNumerator ambientNormalNumerator_homogeneous) :=
    (app_res literalSequence.g (coverPatch_pair 57 1 0 1).ge
      literalConnectingEdge).trans
        ((congrArg (res literalSequence.X₃ (coverPatch_pair 57 1 0 1).ge) he).trans
          (res_comp literalSequence.X₃ (normalCoverOverlap_le_target 57 1)
            (coverPatch_pair 57 1 0 1).ge
            (intrinsicOverlapSection 57 1 intrinsicNormalIso
              ambientNormalNumerator ambientNormalNumerator_homogeneous)))
  change
    (app literalSequence.g _ _, app literalSequence.g _ 0,
      app literalSequence.g _ 0, app literalSequence.g _ 0,
      app literalSequence.g _ 0, app literalSequence.g _ 0) =
    (res literalSequence.X₃ _ _, 0, 0, 0, 0, 0)
  simp only [map_zero]
  exact congrArg (fun x => (x, (0, (0, (0, (0, 0)))))) hfirst

theorem literalReducedCocycle_class (hred : ReductionHolds) :
    CycleQ2CechOneConnecting.cechOneClass (coverFamily 57 1) literal_cover
      (mapOne (coverFamily 57 1) literalSequence.g literalConnectingOne)
      (reduction_closed (coverFamily 57 1) literalConnectingOne literalCocycle
        literalConnectingOne_boundary) = -literalIntrinsicNormalClass :=
  (cechOneClass_congr (coverFamily 57 1) literal_cover (literalConnectingOne_reduction hred)
    (reduction_closed (coverFamily 57 1) literalConnectingOne literalCocycle
      literalConnectingOne_boundary) originalCocycle_closed).trans originalCocycle_class

/-- The actual intrinsic Cartier coefficient boundary of the original
normal class is the negative of the unchanged literal Cartier class. -/
theorem literalOpenConnecting_originalClass (hred : ReductionHolds) :
    literalOpenConnecting ⊤ literalIntrinsicNormalClass = -literalDerivedClassAtTop := by
  have h := coefficient_connecting (coverFamily 57 1) literal_cover
    literalInverseIdealAdditiveComplex_shortExact literalConnectingOne
    literalCocycle literalCocycle_closed literalConnectingOne_boundary
  rw [literalReducedCocycle_class hred, Ext.neg_comp] at h
  exact neg_eq_iff_eq_neg.mp h

theorem literalOpenConnecting_originalClass_ne_zero (hred : ReductionHolds) :
    literalOpenConnecting ⊤ literalIntrinsicNormalClass ≠ 0 := by
  rw [literalOpenConnecting_originalClass hred]
  exact neg_ne_zero.mpr literalDerivedClassAtTop_ne_zero

/-- The same comparison in ordinary derived sheaf cohomology, using
the existing terminal-source equivalence on the original intrinsic class. -/
theorem literalConnecting_originalClass (hred : ReductionHolds) :
    literalConnecting
      (terminalCohomologyEquiv
        (Opens.grothendieckTopology (projectiveSurface 57 1)) literalSequence.X₃
        ⊤ isTerminalTop 1 literalIntrinsicNormalClass) = -literalDerivedClass := by
  have h := (terminalCohomologyEquiv_connecting
    (S := literalSequence) literalInverseIdealAdditiveComplex_shortExact
    1 literalIntrinsicNormalClass).symm
  exact h.trans ((congrArg literalTerminalCohomologyEquiv
    (literalOpenConnecting_originalClass hred)).trans (map_neg _ _))

end CycleQ2OriginalCartierConnectingCore
end

end CheckedCartierNormalPart04

/-! SOURCE-ONLY CONTINUATION: the appended actual cubic adjunction binding
was recovered and assembled in this turn, but has not been compiled or independently
replayed in its final module context. Verification is deferred at the user's request.
The original module above is preserved verbatim. -/

section CheckedGeometricCartierNormalConnectingV7Part1

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ActualCubicAdjunctionBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricSurfaceCurveCharts CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricAffineChartSections CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricSurfaceExteriorSections CycleQ2GeometricPrincipalChartSections
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricAffineOverlap
  CycleQ2GeometricDifferentialChartTransport

/-- The two independently constructed coordinate presentations are the
same literal ring equivalence, as checked on every homogeneous fraction. -/
theorem firstChartEquiv_eq (r θ : ℂ) :
    CycleQ2GeometricDehomogenizedCharts.firstChartEquiv r θ =
      (firstCoordinateEquiv r θ).toRingEquiv := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (curveGrade r θ)
      (coordinate_mem_grade r θ 1) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsHomogeneous n := by simpa using hp
  exact (firstCurveChartEquiv_homogeneousFraction r θ n p hp').trans
    (firstCoordinateEquiv_fraction r θ n p hp').symm

theorem secondChartEquiv_eq (r θ : ℂ) :
    CycleQ2GeometricDehomogenizedCharts.secondChartEquiv r θ =
      (secondCoordinateEquiv r θ).toRingEquiv := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (curveGrade r θ)
      (coordinate_mem_grade r θ 2) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsHomogeneous n := by simpa using hp
  exact (secondCurveChartEquiv_homogeneousFraction r θ n p hp').trans
    (secondCoordinateEquiv_fraction r θ n p hp').symm

theorem firstAffineChart_eq (r θ : ℂ) :
    CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ =
      firstCoordinateChartIso r θ := by
  unfold CycleQ2GeometricAffineProjectiveCharts.firstAffineChart firstCoordinateChartIso
  rw [firstChartEquiv_eq]

theorem secondAffineChart_eq (r θ : ℂ) :
    CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ =
      secondCoordinateChartIso r θ := by
  unfold CycleQ2GeometricAffineProjectiveCharts.secondAffineChart secondCoordinateChartIso
  rw [secondChartEquiv_eq]

section PrincipalDifferentials

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (s : A)
  (hs : (principalChart e s).inv ≫ (principalOpen e s).ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away s))))

/-- Restricting an affine differential through the actual principal chart
is the same as its original universal sheaf lift on that subopen. -/
theorem principal_chartKaehlerSection (V : Over (principalOpen e s))
    (ω : KaehlerDifferential ℂ A) :
    chartKaehlerSection (principalChart e s) f hs V
      (KaehlerDifferential.map ℂ ℂ A (Localization.Away s) ω) =
      chartKaehlerSection e f h
        (Over.mk (V.hom ≫ homOfLE (principalOpen_le e s))) ω := by
  have hm : differentialMap (IsScalarTower.toAlgHom ℂ A (Localization.Away s)) ω =
      KaehlerDifferential.map ℂ ℂ A (Localization.Away s) ω := by
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [differentialMap_D, KaehlerDifferential.map_D]
        rfl
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx =>
        rw [differentialMap_smul, map_smul, hx]
        exact (IsScalarTower.algebraMap_smul (R := A) (A := Localization.Away s) a
          (KaehlerDifferential.map ℂ ℂ A (Localization.Away s) x))
  rw [← hm]
  exact sectionLift_differentialMap X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e (Over.mk (V.hom ≫ homOfLE (principalOpen_le e s))))
    (chartSection_complex e f h _) (chartSection (principalChart e s) V)
    (chartSection_complex (principalChart e s) f hs V)
    (IsScalarTower.toAlgHom ℂ A (Localization.Away s))
    (principal_chartSection e s V) ω

end PrincipalDifferentials

open CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricProjectiveChartModules CycleQ2GeometricProjectiveSectionForms
  CycleQ2GeometricProjectiveAffineCoefficients
  CycleQ2GeometricSparseJacobianCover CycleQ2GeometricChartKaehler

section UniversalSection

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤)) (U : Opens X)
  {A : Type} [CommRing A] [Algebra ℂ A]

/-- The affine universal lift is the actual differential-sheaf unit after
the corresponding map on ordinary Kähler differentials. -/
theorem sectionLift_eq_toSheaf :
    letI := sectionAlgebra R c U
    ∀ (φ : A →ₐ[ℂ] SectionRing R U) (ω : KaehlerDifferential ℂ A),
      sectionLift R c (differentialSheaf R c) (universalDifferential R c)
        U φ.toRingHom φ.commutes ω = toSheaf R c U (differentialMap φ ω) := by
  letI := sectionAlgebra R c U
  intro φ ω
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D, differentialMap_D, toSheaf_D]
      rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, differentialMap_smul, map_smul, hx]
      rfl

end UniversalSection

local instance projectiveSectionAlgebra (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Algebra ℂ Γ(projectiveCurve r θ, O) :=
  sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O

private theorem sectionLift_congr {X : TopCat.{0}}
    {R : X.Sheaf CommRingCat.{0}} {c : ℂ →+* R.obj.obj (op ⊤)}
    {M : SheafOfModules.{0} (ringSheaf R)}
    {d : M.val.Derivation' (coefficientMap R c)} {O : Opens X}
    {A : Type} [CommRing A] [Algebra ℂ A]
    {f g : A →+* R.obj.obj (op O)}
    {hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z}
    {hg : ∀ z : ℂ, g (algebraMap ℂ A z) = coefficientOn R c O z}
    (hfg : f = g) (ω : KaehlerDifferential ℂ A) :
    sectionLift R c M d O f hf ω = sectionLift R c M d O g hg ω := by
  subst g
  rfl

theorem firstSheafFrame_eq_chart (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    firstSheafFrame r θ h1 h2 =
      chartKaehlerSection (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
        (firstCoordinateChartIso_overComplex r θ)
        (chartTop (coordinateProjectivePatch r θ 1))
        (-globalForm (firstEquations r θ) h1) := by
  have ht : chartSection (firstCoordinateChartIso r θ)
      (chartTop (coordinateProjectivePatch r θ 1)) = (firstSectionAlgEquiv r θ).toRingHom := by
    have hcat : CommRingCat.ofHom (chartSection (firstCoordinateChartIso r θ)
        (chartTop (coordinateProjectivePatch r θ 1))) =
        CommRingCat.ofHom (firstSectionAlgEquiv r θ).toRingHom := by
      dsimp only [chartTop]
      rw [chartSection_top]
      exact firstCoordinateChartIso_section_map r θ
    exact congrArg CommRingCat.Hom.hom hcat
  have hf := ((congrArg (differentialMap (firstSectionAlgEquiv r θ).toAlgHom)
    (firstOrientedAffineEquiv_symm_one r θ h1)).symm.trans
      (firstSectionForm_eq r θ h1 h2)).symm
  exact (congrArg (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinateProjectivePatch r θ 1)) hf).trans
      ((sectionLift_eq_toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 1) (firstSectionAlgEquiv r θ).toAlgHom
        (-globalForm (firstEquations r θ) h1)).symm.trans
          (sectionLift_congr ht (-globalForm (firstEquations r θ) h1)).symm)

theorem secondSheafFrame_eq_chart (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    secondSheafFrame r θ h1 h2 =
      chartKaehlerSection (secondCoordinateChartIso r θ) (projectiveToComplex r θ)
        (secondCoordinateChartIso_overComplex r θ)
        (chartTop (coordinateProjectivePatch r θ 2))
        (globalForm (secondEquations r θ) h2) := by
  have ht : chartSection (secondCoordinateChartIso r θ)
      (chartTop (coordinateProjectivePatch r θ 2)) = (secondSectionAlgEquiv r θ).toRingHom := by
    have hcat : CommRingCat.ofHom (chartSection (secondCoordinateChartIso r θ)
        (chartTop (coordinateProjectivePatch r θ 2))) =
        CommRingCat.ofHom (secondSectionAlgEquiv r θ).toRingHom := by
      dsimp only [chartTop]
      rw [chartSection_top]
      exact secondCoordinateChartIso_section_map r θ
    exact congrArg CommRingCat.Hom.hom hcat
  have hf := ((congrArg (differentialMap (secondSectionAlgEquiv r θ).toAlgHom)
    (secondOrientedAffineEquiv_symm_one r θ h2)).symm.trans
      (secondSectionForm_eq r θ h1 h2)).symm
  exact (congrArg (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinateProjectivePatch r θ 2)) hf).trans
      ((sectionLift_eq_toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 2) (secondSectionAlgEquiv r θ).toAlgHom
        (globalForm (secondEquations r θ) h2)).symm.trans
          (sectionLift_congr ht (globalForm (secondEquations r θ) h2)).symm)

open CycleQ2GeometricProjectiveFrameRestriction

theorem firstDenominatorFrame_subopen (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ firstProjectivePatch r θ) :
    (projectiveDifferentialSheaf r θ).val.map (homOfLE hW).op
        (firstDenominatorFrame r θ h1 h2) =
      chartKaehlerSection (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
        (firstCoordinateChartIso_overComplex r θ)
        (Over.mk (homOfLE (hW.trans (firstProjectivePatch_le_firstCoordinate r θ))))
        (-globalForm (firstEquations r θ) h1) := by
  have hc := ConcreteCategory.congr_hom
    ((projectiveDifferentialSheaf r θ).val.presheaf.map_comp
      (homOfLE (firstProjectivePatch_le_firstCoordinate r θ)).op (homOfLE hW).op)
    (firstSheafFrame r θ h1 h2)
  change _ = (projectiveDifferentialSheaf r θ).val.map (homOfLE hW).op
    (firstDenominatorFrame r θ h1 h2) at hc
  refine hc.symm.trans ?_
  rw [firstSheafFrame_eq_chart]
  exact sectionLift_restriction (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) (projectiveDifferentialSheaf r θ)
    (projectiveUniversalDifferential r θ) _
    (chartSection (firstCoordinateChartIso r θ) (chartTop _))
    (chartSection_complex _ _ (firstCoordinateChartIso_overComplex r θ) _)
    W (hW.trans (firstProjectivePatch_le_firstCoordinate r θ))
    (chartSection (firstCoordinateChartIso r θ)
      (Over.mk (homOfLE (hW.trans (firstProjectivePatch_le_firstCoordinate r θ)))))
    (chartSection_complex _ _ (firstCoordinateChartIso_overComplex r θ)
      (Over.mk (homOfLE (hW.trans (firstProjectivePatch_le_firstCoordinate r θ)))))
    (chartSection_naturality _ (toChartTop
      (Over.mk (homOfLE (hW.trans (firstProjectivePatch_le_firstCoordinate r θ)))))) _

theorem secondDenominatorFrame_subopen (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ secondProjectivePatch r θ) :
    (projectiveDifferentialSheaf r θ).val.map (homOfLE hW).op
        (secondDenominatorFrame r θ h1 h2) =
      chartKaehlerSection (secondCoordinateChartIso r θ) (projectiveToComplex r θ)
        (secondCoordinateChartIso_overComplex r θ)
        (Over.mk (homOfLE (hW.trans (secondProjectivePatch_le_secondCoordinate r θ))))
        (globalForm (secondEquations r θ) h2) := by
  have hc := ConcreteCategory.congr_hom
    ((projectiveDifferentialSheaf r θ).val.presheaf.map_comp
      (homOfLE (secondProjectivePatch_le_secondCoordinate r θ)).op (homOfLE hW).op)
    (secondSheafFrame r θ h1 h2)
  change _ = (projectiveDifferentialSheaf r θ).val.map (homOfLE hW).op
    (secondDenominatorFrame r θ h1 h2) at hc
  refine hc.symm.trans ?_
  rw [secondSheafFrame_eq_chart]
  exact sectionLift_restriction (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) (projectiveDifferentialSheaf r θ)
    (projectiveUniversalDifferential r θ) _
    (chartSection (secondCoordinateChartIso r θ) (chartTop _))
    (chartSection_complex _ _ (secondCoordinateChartIso_overComplex r θ) _)
    W (hW.trans (secondProjectivePatch_le_secondCoordinate r θ))
    (chartSection (secondCoordinateChartIso r θ)
      (Over.mk (homOfLE (hW.trans (secondProjectivePatch_le_secondCoordinate r θ)))))
    (chartSection_complex _ _ (secondCoordinateChartIso_overComplex r θ)
      (Over.mk (homOfLE (hW.trans (secondProjectivePatch_le_secondCoordinate r θ)))))
    (chartSection_naturality _ (toChartTop
      (Over.mk (homOfLE (hW.trans (secondProjectivePatch_le_secondCoordinate r θ)))))) _

open CycleQ2GeometricSurfacePrincipalCurveCharts CycleQ2GeometricSurfaceNormalCover
  CycleQ2CurveCubicCoefficients

theorem firstNormalCurve_le_coordinate (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    firstNormalCurveOpen r θ i j ≤ coordinateProjectivePatch r θ 1 :=
  principalOpen_le (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ)
    (firstAffineCurveMap r θ (firstJacobian r θ i j))

theorem secondNormalCurve_le_coordinate (r θ : ℂ) (i : Fin 2) (j : Fin 3) :
    secondNormalCurveOpen r θ i j ≤ coordinateProjectivePatch r θ 2 :=
  principalOpen_le (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ)
    (secondAffineCurveMap r θ (secondJacobian r θ i j))

theorem firstNormalCurve_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen r θ i j)) (a : FirstChartRing r θ) :
    chartSection (firstNormalCurveChart r θ i j) V
        (algebraMap (FirstChartRing r θ) (FirstNormalCurveRing r θ i j) a) =
      chartSection (firstCoordinateChartIso r θ)
        (Over.mk (homOfLE (V.hom.le.trans (firstNormalCurve_le_coordinate r θ i j)))) a := by
  have h := principal_chartSection (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ)
    (firstAffineCurveMap r θ (firstJacobian r θ i j)) V a
  exact h.trans (congrArg (fun e => chartSection e
    (Over.mk (homOfLE (V.hom.le.trans (firstNormalCurve_le_coordinate r θ i j)))) a)
      (firstAffineChart_eq r θ))

theorem secondNormalCurve_chartSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen r θ i j)) (a : SecondChartRing r θ) :
    chartSection (secondNormalCurveChart r θ i j) V
        (algebraMap (SecondChartRing r θ) (SecondNormalCurveRing r θ i j) a) =
      chartSection (secondCoordinateChartIso r θ)
        (Over.mk (homOfLE (V.hom.le.trans (secondNormalCurve_le_coordinate r θ i j)))) a := by
  have h := principal_chartSection (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ)
    (secondAffineCurveMap r θ (secondJacobian r θ i j)) V a
  exact h.trans (congrArg (fun e => chartSection e
    (Over.mk (homOfLE (V.hom.le.trans (secondNormalCurve_le_coordinate r θ i j)))) a)
      (secondAffineChart_eq r θ))

theorem firstNormalCurve_chartKaehlerSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen r θ i j)) (ω : KaehlerDifferential ℂ (FirstChartRing r θ)) :
    chartKaehlerSection (firstNormalCurveChart r θ i j) (projectiveToComplex r θ)
        (firstNormalCurveChart_overComplex r θ i j) V
        (KaehlerDifferential.map ℂ ℂ (FirstChartRing r θ) (FirstNormalCurveRing r θ i j) ω) =
      chartKaehlerSection (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
        (firstCoordinateChartIso_overComplex r θ)
        (Over.mk (homOfLE (V.hom.le.trans (firstNormalCurve_le_coordinate r θ i j)))) ω := by
  have hf : (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 1).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstChartRing r θ))) := by
    rw [firstAffineChart_eq]
    exact firstCoordinateChartIso_overComplex r θ
  have h := principal_chartKaehlerSection
    (CycleQ2GeometricAffineProjectiveCharts.firstAffineChart r θ)
    (projectiveToComplex r θ) hf (firstAffineCurveMap r θ (firstJacobian r θ i j))
    (firstNormalCurveChart_overComplex r θ i j) V ω
  exact h.trans (sectionLift_congr
    (congrArg (fun e => chartSection e
      (Over.mk (homOfLE (V.hom.le.trans (firstNormalCurve_le_coordinate r θ i j)))))
        (firstAffineChart_eq r θ)) ω)

theorem secondNormalCurve_chartKaehlerSection (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen r θ i j)) (ω : KaehlerDifferential ℂ (SecondChartRing r θ)) :
    chartKaehlerSection (secondNormalCurveChart r θ i j) (projectiveToComplex r θ)
        (secondNormalCurveChart_overComplex r θ i j) V
        (KaehlerDifferential.map ℂ ℂ (SecondChartRing r θ) (SecondNormalCurveRing r θ i j) ω) =
      chartKaehlerSection (secondCoordinateChartIso r θ) (projectiveToComplex r θ)
        (secondCoordinateChartIso_overComplex r θ)
        (Over.mk (homOfLE (V.hom.le.trans (secondNormalCurve_le_coordinate r θ i j)))) ω := by
  have hf : (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ).inv ≫
      (coordinateProjectivePatch r θ 2).ι ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (SecondChartRing r θ))) := by
    rw [secondAffineChart_eq]
    exact secondCoordinateChartIso_overComplex r θ
  have h := principal_chartKaehlerSection
    (CycleQ2GeometricAffineProjectiveCharts.secondAffineChart r θ)
    (projectiveToComplex r θ) hf (secondAffineCurveMap r θ (secondJacobian r θ i j))
    (secondNormalCurveChart_overComplex r θ i j) V ω
  exact h.trans (sectionLift_congr
    (congrArg (fun e => chartSection e
      (Over.mk (homOfLE (V.hom.le.trans (secondNormalCurve_le_coordinate r θ i j)))))
        (secondAffineChart_eq r θ)) ω)

open CycleQ2CubicSheafCoefficients

theorem firstCoefficient_subopen (r θ : ℂ) (σ : Poly)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ coordinateProjectivePatch r θ 1) :
    chartSection (firstCoordinateChartIso r θ) (Over.mk (homOfLE hW))
        (firstChartMap r θ (firstDehomogenize σ)) =
      (projectiveCurve r θ).presheaf.map (homOfLE hW).op (firstCoefficient r θ σ) := by
  have ht := RingHom.congr_fun (CycleQ2GeometricProjectiveChartSections.first_chartSection_top r θ)
    (firstChartMap r θ (firstDehomogenize σ))
  have hn := chartSection_naturality (firstCoordinateChartIso r θ)
    (toChartTop (Over.mk (homOfLE hW))) (firstChartMap r θ (firstDehomogenize σ))
  exact hn.symm.trans (congrArg ((projectiveCurve r θ).presheaf.map (homOfLE hW).op) ht)

theorem secondCoefficient_subopen (r θ : ℂ) (σ : Poly)
    (W : (projectiveCurve r θ).Opens) (hW : W ≤ coordinateProjectivePatch r θ 2) :
    chartSection (secondCoordinateChartIso r θ) (Over.mk (homOfLE hW))
        (secondChartMap r θ (secondDehomogenize σ)) =
      (projectiveCurve r θ).presheaf.map (homOfLE hW).op (secondCoefficient r θ σ) := by
  have ht := RingHom.congr_fun (CycleQ2GeometricProjectiveChartSections.second_chartSection_top r θ)
    (secondChartMap r θ (secondDehomogenize σ))
  have hn := chartSection_naturality (secondCoordinateChartIso r θ)
    (toChartTop (Over.mk (homOfLE hW))) (secondChartMap r θ (secondDehomogenize σ))
  exact hn.symm.trans (congrArg ((projectiveCurve r θ).presheaf.map (homOfLE hW).op) ht)

theorem firstCurveCoefficient_section (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen r θ i j)) (p : MvPolynomial (Fin 5) ℂ) :
    chartSection (firstNormalCurveChart r θ i j) V (firstCurveCoefficient r θ i j p) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (V.hom.le.trans (firstNormalCurve_le_coordinate r θ i j))).op
        (firstCoefficient r θ (substitute p)) := by
  rw [firstCurveCoefficient_eq, firstNormalCurve_chartSection]
  exact firstCoefficient_subopen r θ (substitute p) V.left _

theorem secondCurveCoefficient_section (r θ : ℂ) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen r θ i j)) (p : MvPolynomial (Fin 5) ℂ) :
    chartSection (secondNormalCurveChart r θ i j) V (secondCurveCoefficient r θ i j p) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (V.hom.le.trans (secondNormalCurve_le_coordinate r θ i j))).op
        (secondCoefficient r θ (substitute p)) := by
  rw [secondCurveCoefficient_eq, secondNormalCurve_chartSection]
  exact secondCoefficient_subopen r θ (substitute p) V.left _

local instance differentialSectionModule (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O) ((projectiveDifferentialSheaf r θ).val.obj (op O)) :=
  inferInstanceAs (Module ((ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op O))
    ((projectiveDifferentialSheaf r θ).val.obj (op O)))

/-- The real local normal-first contraction lands in precisely the old
canonical frame, with the first chart's negative curve orientation. -/
theorem firstAdjunctionSection_eq (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen r θ i j)) (hV : V.left ≤ firstProjectivePatch r θ)
    (p : MvPolynomial (Fin 5) ℂ) :
    chartKaehlerSection (firstNormalCurveChart r θ i j) (projectiveToComplex r θ)
        (firstNormalCurveChart_overComplex r θ i j) V
        (firstNormalAdjunction r θ i j (firstRestrictedPolynomialForm r θ i j p)) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (hV.trans (firstProjectivePatch_le_firstCoordinate r θ))).op
        (firstCoefficient r θ (substitute p)) •
      (projectiveDifferentialSheaf r θ).val.map (homOfLE hV).op
        (firstDenominatorFrame r θ h1 h2) := by
  have hform := firstNormalAdjunction_formula r θ i j h1 p
  have hsm := sectionLift_smul (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ) V.left
    (chartSection (firstNormalCurveChart r θ i j) V)
    (chartSection_complex _ _ (firstNormalCurveChart_overComplex r θ i j) V)
    (-(firstCurveCoefficient r θ i j p))
    (KaehlerDifferential.map ℂ ℂ (FirstChartRing r θ) (FirstNormalCurveRing r θ i j)
      (globalForm (firstEquations r θ) h1))
  have h := (congrArg
    (chartKaehlerSection (firstNormalCurveChart r θ i j) (projectiveToComplex r θ)
      (firstNormalCurveChart_overComplex r θ i j) V) hform).trans hsm
  let c : Γ(projectiveCurve r θ, V.left) :=
    (projectiveCurve r θ).presheaf.map
      (homOfLE (hV.trans (firstProjectivePatch_le_firstCoordinate r θ))).op
      (firstCoefficient r θ (substitute p))
  let ω : (projectiveDifferentialSheaf r θ).val.obj (op V.left) :=
    chartKaehlerSection (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
      (firstCoordinateChartIso_overComplex r θ)
      (Over.mk (homOfLE (hV.trans (firstProjectivePatch_le_firstCoordinate r θ))))
      (globalForm (firstEquations r θ) h1)
  have hc : chartSection (firstNormalCurveChart r θ i j) V
      (-(firstCurveCoefficient r θ i j p)) = -c :=
    (map_neg (chartSection (firstNormalCurveChart r θ i j) V) _).trans
      (congrArg (fun z : Γ(projectiveCurve r θ, V.left) => -z)
        (firstCurveCoefficient_section r θ i j V p))
  have hω := firstNormalCurve_chartKaehlerSection r θ i j V
    (globalForm (firstEquations r θ) h1)
  have hpair := congrArg₂
    (fun (a : Γ(projectiveCurve r θ, V.left))
      (z : (projectiveDifferentialSheaf r θ).val.obj (op V.left)) => a • z) hc hω
  have hf : (projectiveDifferentialSheaf r θ).val.map (homOfLE hV).op
      (firstDenominatorFrame r θ h1 h2) = -ω :=
    (firstDenominatorFrame_subopen r θ h1 h2 V.left hV).trans
      (map_neg (chartKaehlerSection (firstCoordinateChartIso r θ) (projectiveToComplex r θ)
        (firstCoordinateChartIso_overComplex r θ)
        (Over.mk (homOfLE (hV.trans (firstProjectivePatch_le_firstCoordinate r θ))))) _)
  exact h.trans (hpair.trans ((neg_smul c ω).trans
    ((smul_neg c ω).symm.trans (congrArg (fun z => c • z) hf.symm))))

/-- The second surface representative carries its fixed minus sign;
contraction consequently lands in the positive second curve frame. -/
theorem secondAdjunctionSection_eq (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen r θ i j)) (hV : V.left ≤ secondProjectivePatch r θ)
    (p : MvPolynomial (Fin 5) ℂ) :
    chartKaehlerSection (secondNormalCurveChart r θ i j) (projectiveToComplex r θ)
        (secondNormalCurveChart_overComplex r θ i j) V
        (secondNormalAdjunction r θ i j (-(secondRestrictedPolynomialForm r θ i j p))) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE (hV.trans (secondProjectivePatch_le_secondCoordinate r θ))).op
        (secondCoefficient r θ (substitute p)) •
      (projectiveDifferentialSheaf r θ).val.map (homOfLE hV).op
        (secondDenominatorFrame r θ h1 h2) := by
  have hform := secondNormalAdjunction_oriented r θ i j h2 p
  have hsm := sectionLift_smul (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ) V.left
    (chartSection (secondNormalCurveChart r θ i j) V)
    (chartSection_complex _ _ (secondNormalCurveChart_overComplex r θ i j) V)
    (secondCurveCoefficient r θ i j p)
    (KaehlerDifferential.map ℂ ℂ (SecondChartRing r θ) (SecondNormalCurveRing r θ i j)
      (globalForm (secondEquations r θ) h2))
  have h := (congrArg
    (chartKaehlerSection (secondNormalCurveChart r θ i j) (projectiveToComplex r θ)
      (secondNormalCurveChart_overComplex r θ i j) V) hform).trans hsm
  have hc := secondCurveCoefficient_section r θ i j V p
  have hω := secondNormalCurve_chartKaehlerSection r θ i j V
    (globalForm (secondEquations r θ) h2)
  have hpair := congrArg₂
    (fun (a : Γ(projectiveCurve r θ, V.left))
      (z : (projectiveDifferentialSheaf r θ).val.obj (op V.left)) => a • z) hc hω
  exact h.trans (hpair.trans (congrArg (fun z =>
      (projectiveCurve r θ).presheaf.map
        (homOfLE (hV.trans (secondProjectivePatch_le_secondCoordinate r θ))).op
        (secondCoefficient r θ (substitute p)) • z)
    (secondDenominatorFrame_subopen r θ h1 h2 V.left hV).symm))

open CycleQ2IntrinsicNormalModel CycleQ2NormalVectorOnCurve CycleQ2CubicDifferentialMap
  CycleQ2SurfaceCubicGluing

/-- On every literal first Jacobian/quartic subopen, the original normal
generator's actual cubic differential image is the genuine contraction
of the original local representative of the glued cubic surface form. -/
theorem literal_first_cubic_adjunction (p : WeightedCubic) (i : Fin 2) (j : Fin 3)
    (V : Over (firstNormalCurveOpen (57 : ℂ) 1 i j))
    (hV : V.left ≤ firstProjectivePatch 57 1) :
    ((intrinsicNormalIso.hom ≫ literalModelCubicDifferential (substitute p.val)
      (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)).val.app (op V.left))
        (firstVectorAt 57 1 i j V.left
          (V.hom.le.trans (firstNormalOpen_preimage 57 1 i j).ge)) =
      chartKaehlerSection (firstNormalCurveChart 57 1 i j) (projectiveToComplex 57 1)
        (firstNormalCurveChart_overComplex 57 1 i j) V
        (firstNormalAdjunction 57 1 i j (firstRestrictedPolynomialForm 57 1 i j p.val)) := by
  have hc : firstNormalCoordinate 57 1 V.left hV
      (intrinsicNormalIso.hom.val.app (op V.left)
        (firstVectorAt 57 1 i j V.left
          (V.hom.le.trans (firstNormalOpen_preimage 57 1 i j).ge))) = 1 :=
    intrinsicNormalIso_first_vector (i,j) V.left hV _
  have h := modelCubicDifferential_first_local 57 1 (by norm_num)
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top
    (substitute p.val) (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)
    V.left hV (intrinsicNormalIso.hom.val.app (op V.left)
      (firstVectorAt 57 1 i j V.left
        (V.hom.le.trans (firstNormalOpen_preimage 57 1 i j).ge)))
  rw [hc, one_mul] at h
  exact h.trans (firstAdjunctionSection_eq 57 1
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top i j V hV p.val).symm

/-- The second chart retains the negated surface representative and the
same original normal generator, so no global sign is silently changed. -/
theorem literal_second_cubic_adjunction (p : WeightedCubic) (i : Fin 2) (j : Fin 3)
    (V : Over (secondNormalCurveOpen (57 : ℂ) 1 i j))
    (hV : V.left ≤ secondProjectivePatch 57 1) :
    ((intrinsicNormalIso.hom ≫ literalModelCubicDifferential (substitute p.val)
      (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)).val.app (op V.left))
        (secondVectorAt 57 1 i j V.left
          (V.hom.le.trans (secondNormalOpen_preimage 57 1 i j).ge)) =
      chartKaehlerSection (secondNormalCurveChart 57 1 i j) (projectiveToComplex 57 1)
        (secondNormalCurveChart_overComplex 57 1 i j) V
        (secondNormalAdjunction 57 1 i j (-(secondRestrictedPolynomialForm 57 1 i j p.val))) := by
  have hc : secondNormalCoordinate 57 1 V.left hV
      (intrinsicNormalIso.hom.val.app (op V.left)
        (secondVectorAt 57 1 i j V.left
          (V.hom.le.trans (secondNormalOpen_preimage 57 1 i j).ge))) = 1 :=
    intrinsicNormalIso_second_vector (i,j) V.left hV _
  have h := modelCubicDifferential_second_local 57 1 (by norm_num)
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top
    (substitute p.val) (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)
    V.left hV (intrinsicNormalIso.hom.val.app (op V.left)
      (secondVectorAt 57 1 i j V.left
        (V.hom.le.trans (secondNormalOpen_preimage 57 1 i j).ge)))
  rw [hc, one_mul] at h
  exact h.trans (secondAdjunctionSection_eq 57 1
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top i j V hV p.val).symm

#print axioms literal_first_cubic_adjunction
#print axioms literal_second_cubic_adjunction

#print axioms firstChartEquiv_eq
#print axioms firstAffineChart_eq
#print axioms principal_chartKaehlerSection
#print axioms firstSheafFrame_eq_chart

end CycleQ2ActualCubicAdjunctionBinding
end

end CheckedGeometricCartierNormalConnectingV7Part1
