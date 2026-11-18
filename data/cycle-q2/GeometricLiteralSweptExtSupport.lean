import Proposal.GeometricLiteralCompletedHodgePullback
import Proposal.GeometricLiteralProperSweptSupport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Restriction of the swept two-form coefficient and its Yoneda action

The direct image of the two-form module on the closed swept scheme has zero
restriction to the complementary open of the fixed threefold. Consequently
precomposition by its actual Kähler two-form map has supported image in
module Ext, including for the top-form coefficient in degree two.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralSweptExtSupport

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
  TopologicalSpace CycleQ2ExteriorPullComposition CycleQ2GeometricAffineChartSections
  CycleQ2LiteralThreefoldHodgeCech
open CycleQ2LiteralAmbientCylinder (fixedIso)
open CycleQ2LiteralAbelJacobiTimeProjection (q)
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable {X Y : Scheme.{0}}

/-- Restriction along an open immersion is exact. Its description as
pushforward along the functor of open images gives left exactness. -/
private instance exactRestrict (u : X ⟶ Y) [IsOpenImmersion u] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor u) := by
  let F := Scheme.Modules.toPresheaf X
  have : ReflectsLimits F := reflectsLimits_of_reflectsIsomorphisms
  let W := (Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ AddCommGrpCat.{0}).obj u.opensFunctor.op
  have : PreservesFiniteLimits W := ⟨fun _ => inferInstanceAs (PreservesLimitsOfShape _ ((Functor.whiskeringLeft _ _ _).obj u.opensFunctor.op))⟩
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y ⋙ W) := comp_preservesFiniteLimits _ _
  have e : Scheme.Modules.restrictFunctor u ⋙ F ≅ Scheme.Modules.toPresheaf Y ⋙ W := Iso.refl _
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor u ⋙ F) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ F

private instance addRestrict (u : X ⟶ Y) [IsOpenImmersion u] :
    (Scheme.Modules.restrictFunctor u).Additive where

private theorem disjoint_sections (i : X ⟶ Y) (M : X.Modules) (W : Y.Opens)
    (hW : i ⁻¹ᵁ W = ⊥) :
    Subsingleton (((Scheme.Modules.pushforward i).obj M).val.obj (op W)) := by
  let F : (show TopCat from X).Sheaf AddCommGrpCat.{0} := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (TopCat.Sheaf.isTerminalOfEqEmpty F hW).isZero

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev inclusion := CycleQ2LiteralCompletedHodgePullback.sweptMap V t
abbrev sweptCoefficients := schemeCoefficient (inclusion V t ≫ structureMap)
abbrev onSwept := forms (q V t).image (sweptCoefficients V t) 2
abbrev directImage := (Scheme.Modules.pushforward (inclusion V t)).obj (onSwept V t)
abbrev coefficientsMap : TwoForms ⟶ directImage V t :=
  schemeExteriorPull (inclusion V t) (sweptCoefficients V t) coefficients
    (compatible_over _ _ _ rfl) 2

def complement : Threefold.Opens :=
  ⟨(Set.range (inclusion V t))ᶜ, (inclusion V t).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- For an independent parameter and the selected time open this is a
nonempty open in the actual fixed threefold. -/
theorem exists_nonempty_complement (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, CycleQ2IncidenceSeedFiberCover.seedBasePoint ∈ V ∧
      Nonempty (complement V t) := by
  obtain ⟨V, hV, _, _, _, hne, _⟩ := CycleQ2LiteralSweptSupport.swept_support_of_independent t hi
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨V, hV, ⟨⟨fixedIso.hom x, ?_⟩⟩⟩
  rintro ⟨y, hy⟩
  exact hx ⟨y, fixedIso.hom.isOpenEmbedding.injective hy⟩

private theorem off_image (W : (complement V t).toScheme.Opens) :
    inclusion V t ⁻¹ᵁ ((complement V t).ι ''ᵁ W) = ⊥ := by
  apply bot_unique
  rintro x ⟨y, -, hy⟩
  exact y.property ⟨x, hy.symm⟩

/-- The restriction vanishes as a sheaf of modules over the open complement. -/
theorem directImage_off :
    IsZero ((Scheme.Modules.restrictFunctor (complement V t).ι).obj (directImage V t)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro x
  exact (disjoint_sections (inclusion V t) (onSwept V t) _ (off_image V t W.unop)).elim _ _

attribute [local instance] HasExt.standard

abbrev canonicalModule := forms Threefold coefficients 3

/-- The contravariant map on genuine module Ext with the canonical top forms
of the smooth threefold as coefficient. -/
def supportedMap : Ext.{1} (directImage V t) canonicalModule 2 →+
    Ext.{1} TwoForms canonicalModule 2 :=
  (Ext.mk₀ (coefficientsMap V t)).precomp canonicalModule (zero_add 2)

/-- Every class in the image is zero after exact restriction to the swept
complement. -/
theorem supportedMap_restrict (e : Ext.{1} (directImage V t) canonicalModule 2) :
    ((supportedMap V t) e).mapExactFunctor (Scheme.Modules.restrictFunctor (complement V t).ι) = 0 := by
  let R := Scheme.Modules.restrictFunctor (complement V t).ι
  change ((Ext.mk₀ (coefficientsMap V t)).comp e (zero_add 2)).mapExactFunctor R = 0
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    (directImage_off V t).eq_of_tgt (R.map (coefficientsMap V t)) 0, Ext.mk₀_zero, Ext.zero_comp]

section NativeTest

open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2FiniteCechHOne (cechOneClass cechOneClass_naturality)
open CycleQ2LiteralAbelJacobiQPullbackDerived (pullH pullH_cech)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)

abbrev additiveCoefficientMap : HodgeSheaf ⟶ addSheaf (directImage V t) :=
  (SheafOfModules.toSheaf Threefold.ringCatSheaf).map (coefficientsMap V t)

/-- The native class with coefficients in an actual module on T supported
on the swept subscheme. -/
def supportedTestClass : (addSheaf (directImage V t)).H' 1 ⊤ :=
  CycleQ2LiteralThreefoldTestClass.ambientTestClass.comp
    (Ext.mk₀ (additiveCoefficientMap V t)) (add_zero 1)

/-- Evaluating the supported coefficient on the swept scheme gives exactly
the pullback of the original native Hodge class. -/
theorem supportedTest_restrict :
    pullH (inclusion V t).base (G := addSheaf (onSwept V t)) (𝟙 (addSheaf (directImage V t))) 1 (supportedTestClass V t) =
      pullH (inclusion V t).base (G := addSheaf (onSwept V t)) (additiveCoefficientMap V t) 1
        CycleQ2LiteralThreefoldTestClass.ambientTestClass := by
  unfold supportedTestClass CycleQ2LiteralThreefoldTestClass.ambientTestClass hodgeClass
  rw [cechOneClass_naturality, pullH_cech, pullH_cech]
  rfl

/-- The original pullback to the smooth time family is obtained from the
class on T whose coefficient module vanishes on the swept complement. -/
theorem supportedTest_family :
    CycleQ2LiteralCompletedHodgePullback.pullToFamily (inclusion V t) V t (q V t).toImage
        (CycleQ2LiteralCompletedHodgePullback.toImage_sweptMap V t)
        (pullH (inclusion V t).base (G := addSheaf (onSwept V t)) (𝟙 (addSheaf (directImage V t))) 1 (supportedTestClass V t)) =
      CycleQ2LiteralAbelJacobiQPullbackDerived.qHodge V t
        CycleQ2LiteralThreefoldTestClass.ambientTestClass := by
  rw [supportedTest_restrict]
  exact (CycleQ2LiteralCompletedHodgePullback.ambientTest_factorizations V t).2

/-- The forgetful functor on module sheaves preserves finite colimits:
the additive sheafification of a colimit presentation computes its image. -/
theorem forgetFiniteColimits (S : Scheme.{0}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{0} S.ringCatSheaf) where
  preservesFiniteColimits J _ _ := by
    constructor
    intro K
    let R := S.ringCatSheaf
    let L := PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)
    let G := SheafOfModules.toSheaf.{0} R
    let F := SheafOfModules.forget.{0} R ⋙ PresheafOfModules.restrictScalars.{0} (𝟙 R.obj)
    let P := K ⋙ F
    let η : F ⋙ L ≅ 𝟭 (SheafOfModules.{0} R) :=
      asIso (PresheafOfModules.sheafificationAdjunction.{0} (R := R) (𝟙 R.obj)).counit
    let e : P ⋙ L ≅ K := Functor.associator K F L ≪≫ Functor.isoWhiskerLeft K η ≪≫ K.rightUnitor
    have : PreservesColimitsOfShape J (L ⋙ G) :=
      preservesColimitsOfShape_of_natIso (PresheafOfModules.sheafificationCompToSheaf (R := R) (𝟙 R.obj)).symm
    have : PreservesColimit (P ⋙ L) G := preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit P)) (isColimitOfPreserves (L ⋙ G) (colimit.isColimit P))
    exact preservesColimit_of_iso_diagram G e

attribute [local instance] forgetFiniteColimits

private instance additiveForget (S : Scheme.{0}) : (SheafOfModules.toSheaf.{0} S.ringCatSheaf).Additive where

instance (priority := low) forgetPreservesZero (S : Scheme.{0}) :
    (SheafOfModules.toSheaf.{0} S.ringCatSheaf).PreservesZeroMorphisms where
  map_zero _ _ := by ext V s; rfl

/-- A short exact sequence of scheme modules remains short exact on the underlying
additive sheaves, including the extension used in the supported pairing. -/
theorem additiveShortExact {X : Scheme.{0}} {D : ShortComplex (SheafOfModules.{0} X.ringCatSheaf)} (h : D.ShortExact) :
    (D.map (SheafOfModules.toSheaf.{0} X.ringCatSheaf)).ShortExact := h.map_of_exact _

/-- Pairing the supported native test with any module extension agrees with
pairing the original Hodge class with its supported pullback. Both products
are in the actual degree-three cohomology of the top forms of T. -/
theorem supportedTest_pairing (e : Ext.{1} (directImage V t) canonicalModule 2) :
    (supportedTestClass V t).comp (e.mapExactFunctor (SheafOfModules.toSheaf Threefold.ringCatSheaf)) rfl =
      CycleQ2LiteralThreefoldTestClass.ambientTestClass.comp
        (((supportedMap V t) e).mapExactFunctor (SheafOfModules.toSheaf Threefold.ringCatSheaf)) rfl := by
  let G := SheafOfModules.toSheaf Threefold.ringCatSheaf
  unfold supportedTestClass supportedMap
  change (CycleQ2LiteralThreefoldTestClass.ambientTestClass.comp (Ext.mk₀ (additiveCoefficientMap V t)) (add_zero 1)).comp (e.mapExactFunctor G) rfl =
    CycleQ2LiteralThreefoldTestClass.ambientTestClass.comp (((Ext.mk₀ (coefficientsMap V t)).comp e (zero_add 2)).mapExactFunctor G) rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 2) rfl

end NativeTest

end CycleQ2LiteralSweptExtSupport

#print axioms CycleQ2LiteralSweptExtSupport.directImage_off
#print axioms CycleQ2LiteralSweptExtSupport.supportedMap_restrict
#print axioms CycleQ2LiteralSweptExtSupport.supportedTest_restrict
#print axioms CycleQ2LiteralSweptExtSupport.supportedTest_family
#print axioms CycleQ2LiteralSweptExtSupport.supportedTest_pairing
