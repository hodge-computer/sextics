import Proposal.GeometricLiteralAbelJacobiQPullback
import Proposal.GeometricAutomorphismCohomology
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Derived pullback of the fixed-threefold Hodge class

Inverse image of abelian sheaves is exact. Applying it to Ext and using
the global-section generator gives the pullback in sheaf cohomology.
The second projection acts through its actual exterior-square differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPullbackDerived

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2GeometricSheafLocalIso
  CycleQ2FiniteCechOrbitPullback CycleQ2FiniteCechHOne CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2AutomorphismCohomology

section ChangeOfSpace
variable {X Y : TopCat.{0}} (j : X ⟶ Y)

private abbrev inverse : AbSheaf Y ⥤ AbSheaf X := (Opens.map j).sheafPullback AddCommGrpCat _ _
private abbrev direct : AbSheaf X ⥤ AbSheaf Y := (Opens.map j).sheafPushforwardContinuous AddCommGrpCat _ _
private abbrev adj : inverse j ⊣ direct j := (Opens.map j).sheafAdjunctionContinuous _ _ _

local instance (Z : TopCat.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms
  preservesBinaryBiproducts_of_preservesBinaryCoproducts

local instance : PreservesFiniteLimits (inverse j) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits
local instance : (inverse j).IsLeftAdjoint := (adj j).isLeftAdjoint
local instance : (inverse j).Additive := Functor.additive_of_preservesBinaryBiproducts _

/-- Inverse image carries the global section represented by the identity of the free open sheaf. -/
def sourceMap : freeOpen (⊤ : Opens X) ⟶ (inverse j).obj (freeOpen (⊤ : Opens Y)) :=
  (freeOpenSections _ ⊤).symm (app ((adj j).unit.app (freeOpen (⊤ : Opens Y))) ⊤
    (freeOpenSections _ ⊤ (𝟙 (freeOpen (⊤ : Opens Y)))))

private theorem sourceMap_section (F : AbSheaf Y) (s : Sections F ⊤) :
    sourceMap j ≫ (inverse j).map ((freeOpenSections F ⊤).symm s) =
      (freeOpenSections ((inverse j).obj F) ⊤).symm (app ((adj j).unit.app F) ⊤ s) := by
  apply (freeOpenSections ((inverse j).obj F) ⊤).injective
  rw [← freeOpenSections_postcomp, sourceMap, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let z := freeOpenSections (freeOpen (⊤ : Opens Y)) ⊤ (𝟙 _)
  let a := (freeOpenSections F ⊤).symm s
  change app (((adj j).unit.app _) ≫ (direct j).map ((inverse j).map a)) ⊤ z = _
  have hn : a ≫ (adj j).unit.app F = (adj j).unit.app _ ≫ (direct j).map ((inverse j).map a) :=
    (adj j).unit.naturality a
  rw [← hn]
  change app ((adj j).unit.app F) ⊤ (app a ⊤ z) = _
  apply congrArg
  change app a ⊤ (freeOpenSections _ ⊤ (𝟙 _)) = s
  rw [freeOpenSections_postcomp, Category.id_comp]
  exact AddEquiv.apply_symm_apply _ _

/-- The change-of-space map before applying a morphism of coefficients. -/
def inverseH (F : AbSheaf Y) (n : ℕ) : F.H' n ⊤ →+ ((inverse j).obj F).H' n ⊤ :=
  ((((extFunctor n).map (sourceMap j).op).app ((inverse j).obj F)).hom).comp
    ((inverse j).mapExtAddHom (freeOpen (⊤ : Opens Y)) F n)

private theorem inverseH_zero (F : AbSheaf Y) (s : Sections F ⊤) :
    inverseH j F 0 (sectionExtZero ⊤ s) = sectionExtZero (F := (inverse j).obj F) ⊤ (app ((adj j).unit.app F) ⊤ s) := by
  change (Ext.mk₀ (sourceMap j)).comp ((sectionExtZero ⊤ s).mapExactFunctor (inverse j)) rfl = _
  rw [sectionExtZero, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (sourceMap_section j F s)

private theorem inverseH_connecting {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    (z : Sections S.X₃ ⊤) :
    inverseH j S.X₁ 1 ((sectionExtZero ⊤ z).comp hS.extClass rfl) =
      (sectionExtZero (F := (inverse j).obj S.X₃) ⊤ (app ((adj j).unit.app S.X₃) ⊤ z)).comp
        (hS.map_of_exact (inverse j)).extClass rfl := by
  rw [← inverseH_zero]
  change (Ext.mk₀ _).comp (((sectionExtZero ⊤ z).comp hS.extClass rfl).mapExactFunctor (inverse j)) (zero_add 1) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ rfl rfl rfl).symm

/-- Pullback on all degree-n classes along an arbitrary continuous map. -/
def pullH {F : AbSheaf Y} {G : AbSheaf X} (φ : F ⟶ push j G) (n : ℕ) : F.H' n ⊤ →+ G.H' n ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor _ n).map (((adj j).homEquiv F G).symm φ)).app (op ⊤)).hom.comp
    (inverseH j F n)

private theorem inverseH_cech {ι : Type} [Fintype ι] {F : AbSheaf Y}
    (U : ι → Opens Y) (hU : (⨆ i, U i) = ⊤) (c : One F U) (hc : IsOneCocycle F U c) :
    inverseH j F 1 (cechOneClass U hU c hc) = cechOneClass (cover j U) (cover_top j U hU)
      (pullOne j ((adj j).unit.app F) U c) (pullOne_closed j _ U c hc) := by
  let d := Classical.choice (oneDescent_nonempty U hU c hc)
  let S := presentation F
  let T := S.map (inverse j)
  let u := (adj j).unit
  let p : Zero T.X₂ (cover j U) := fun i => app (u.app S.X₂) (U i) (d.primitive i)
  have hn (a : S.X₁ ⟶ S.X₂) : a ≫ u.app S.X₂ = u.app S.X₁ ≫ (direct j).map ((inverse j).map a) := u.naturality a
  rw [cechOneClass_eq_descentClass U hU c hc d]
  change inverseH j F 1 ((sectionExtZero ⊤ d.globalSection).comp (presentation_shortExact F).extClass rfl) = _
  refine (inverseH_connecting j (presentation_shortExact F) d.globalSection).trans ?_
  symm
  apply cechOneClass_of_lifts (cover j U) (cover_top j U hU) ((presentation_shortExact F).map_of_exact (inverse j))
    _ _ p _
  · intro i k W hi hk
    let P := U i ⊓ U k
    have hW : W ≤ pre j P := le_inf hi hk
    change pullTo j (u.app S.X₂) hk (d.primitive k) - pullTo j (u.app S.X₂) hi (d.primitive i) = _
    rw [← pullTo_res j (u.app S.X₂) hW (show P ≤ U k from inf_le_right),
      ← pullTo_res j (u.app S.X₂) hW (show P ≤ U i from inf_le_left), ← map_sub]
    refine (congrArg (pullTo j (u.app S.X₂) hW) (d.differential i k P inf_le_left inf_le_right)).trans ?_
    refine (pullTo_app j S.f T.f (u.app S.X₁) (u.app S.X₂) (hn S.f) hW _).trans ?_
    exact congrArg (app T.f W) (edgeValue_pullOne j (u.app S.X₁) U c i k hW inf_le_left inf_le_right).symm
  · funext i
    have hz := congrFun d.global_restriction i
    change res S.X₃ le_top d.globalSection = app S.g (U i) (d.primitive i) at hz
    change res (push j T.X₃) (show U i ≤ ⊤ from le_top) (app (u.app S.X₃) ⊤ d.globalSection) = _
    refine (app_res (u.app S.X₃) (show U i ≤ ⊤ from le_top) d.globalSection).symm.trans ?_
    refine (congrArg (app (u.app S.X₃) (U i)) hz).trans ?_
    exact congrArg (fun a : S.X₂ ⟶ (direct j).obj T.X₃ => app a (U i) (d.primitive i))
      (show S.g ≫ u.app S.X₃ = u.app S.X₂ ≫ (direct j).map T.g from u.naturality S.g)

/-- On finite Čech representatives the derived map applies the actual coefficient
morphism on each original intersection. -/
theorem pullH_cech {ι : Type} [Fintype ι] {F : AbSheaf Y} {G : AbSheaf X}
    (φ : F ⟶ push j G) (U : ι → Opens Y) (hU : (⨆ i, U i) = ⊤)
    (c : One F U) (hc : IsOneCocycle F U c) :
    pullH j φ 1 (cechOneClass U hU c hc) = cechOneClass (cover j U) (cover_top j U hU)
      (pullOne j φ U c) (pullOne_closed j φ U c hc) := by
  let f := ((adj j).homEquiv F G).symm φ
  change (inverseH j F 1 (cechOneClass U hU c hc)).comp (Ext.mk₀ f) (Nat.add_zero 1) = _
  rw [inverseH_cech, cechOneClass_naturality]
  have h : mapOne (cover j U) f (pullOne j ((adj j).unit.app F) U c) = pullOne j φ U c := by
    funext i k
    have he : (adj j).unit.app F ≫ (direct j).map f = φ := ((adj j).homEquiv F G).apply_symm_apply φ
    exact congrArg (fun g : F ⟶ push j G => app g (U i ⊓ U k) (c i k)) he
  congr 1

end ChangeOfSpace

open AlgebraicGeometry CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAbelJacobiQPullback
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralAmbientCharts

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

/-- The actual second cylinder projection on the entire degree-one two-form group. -/
def qHodge (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    Hodge21 →+ (familyHodgeSheaf V t).H' 1 ⊤ :=
  pullH (toThreefold V t).base (qAdd V t) 1

theorem qHodge_native (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (ω : NativeEdges)
    (faces : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk) :
    qHodge V t (hodgeClass ω faces) = pulledHodgeClass V t ω faces :=
  pullH_cech (toThreefold V t).base (qAdd V t) fixedOpen fixedOpen_cover (hodgeCocycle ω faces).val
    (fun i j k W hi hj hk => ((hodgeCocycle ω faces).condition i j k W hi hj hk).symm)

end CycleQ2LiteralAbelJacobiQPullbackDerived
end

#print axioms CycleQ2LiteralAbelJacobiQPullbackDerived.qHodge
