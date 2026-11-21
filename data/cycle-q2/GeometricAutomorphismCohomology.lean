import Proposal.GeometricAffineHigherChartRestriction
import Proposal.GeometricFiniteCechOrbitPullback
import Proposal.GeometricAutomorphismGlobalSections

/-!
# Transport of the actual derived connecting map

An equivalence of additive sheaves transports Yoneda classes by its exact
functor on Ext. The comparison from the source of cohomology is composed
in degree zero, so transport commutes with every connecting map.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AutomorphismCohomology

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  TopologicalSpace CycleQ2GeometricSheafCohomologyRestriction

section Ext

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
    (F : C ⥤ C) [F.IsEquivalence] [F.Additive] {A : C} (i : A ≅ F.obj A)

/-- Exact transport, followed by precomposition at the source of Ext. -/
def transport (B : C) (n : ℕ) : Ext.{w} A B n ≃+ Ext.{w} A (F.obj B) n :=
  (AddEquiv.ofBijective (F.mapExtAddHom A B n)
    (mapExt_bijective_of_fixedSource F A
      (fun _ => ⟨F.map_injective, F.map_surjective⟩) B n)).trans
    ((((extFunctor n).mapIso i.op).app (F.obj B)).addCommGroupIsoToAddEquiv)

theorem transport_apply {B : C} {n : ℕ} (x : Ext.{w} A B n) :
    transport F i B n x = (Ext.mk₀ i.hom).comp (x.mapExactFunctor F) (zero_add n) := rfl

theorem transport_connecting {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext.{w} A S.X₃ n) :
    transport F i S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (transport F i S.X₃ n x).comp (hS.map_of_exact F).extClass rfl := by
  rw [transport_apply, transport_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- A coefficient morphism into a direct image on sheaves induces the
pullback on classes by undoing the change of site at its target. -/
def pull {B D : C} (f : B ⟶ F.obj D) (n : ℕ) : Ext.{w} A B n →+ Ext.{w} A D n :=
  (transport F i D n).symm.toAddMonoidHom.comp ((Ext.mk₀ f).postcomp A (add_zero n))

theorem pull_connecting {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T.map F) (n : ℕ) (x : Ext.{w} A S.X₃ n) :
    (pull F i f.τ₃ n x).comp hT.extClass rfl =
      pull F i f.τ₁ (n+1) (x.comp hS.extClass rfl) := by
  apply (transport F i T.X₁ (n+1)).injective
  rw [transport_connecting]
  change ((transport F i T.X₃ n) ((transport F i T.X₃ n).symm _)).comp _ _ =
    (transport F i T.X₁ (n+1)) ((transport F i T.X₁ (n+1)).symm _)
  simp only [AddEquiv.apply_symm_apply]
  change (x.comp (Ext.mk₀ f.τ₃) (add_zero n)).comp (hT.map_of_exact F).extClass rfl =
    (x.comp hS.extClass rfl).comp (Ext.mk₀ f.τ₁) (add_zero (n+1))
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality (hT.map_of_exact F) f,
    Ext.comp_assoc_of_second_deg_zero]

end Ext

section Cech
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2CechTwoNaturality CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (app app_comp app_res presentation presentation_shortExact sectionExtZero)
open CycleQ2CechTwoComparison (sectionExtZero_app)
open CycleQ2CechOneConnecting (coefficientPresentationMap coefficientPresentationMap_left)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι]
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- A global quotient section with specified local lifts represents the
boundary of those lifts, for any actual short exact sequence. -/
theorem cechOneClass_of_lifts (U : ι → Opens X) (hU : (⨆ j, U j) = ⊤)
    {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (c : One S.X₁ U)
    (hc : IsOneCocycle S.X₁ U c) (p : Zero S.X₂ U) (q : Sections S.X₃ ⊤)
    (hp : ∀ i j W hi hj, res S.X₂ hj (p j) - res S.X₂ hi (p i) =
      app S.f W (edgeValue S.X₁ U c i j W hi hj))
    (hq : globalZero U q = mapZero U S.g p) :
    cechOneClass U hU c hc = (sectionExtZero ⊤ q).comp hS.extClass rfl := by
  let m := coefficientPresentationMap hS
  have hm : S.f ≫ m.τ₂ = (presentation S.X₁).f := by
    simpa only [m, coefficientPresentationMap_left, Category.id_comp] using m.comm₁₂.symm
  let d : OneDescent U c :=
    { primitive := mapZero U m.τ₂ p
      differential i j W hi hj := by
        change res _ hj (app m.τ₂ _ (p j)) - res _ hi (app m.τ₂ _ (p i)) = _
        rw [← app_res, ← app_res, ← map_sub, hp, app_comp, hm]
      globalSection := app m.τ₃ ⊤ q
      global_restriction := by
        funext j
        change res _ le_top (app m.τ₃ ⊤ q) =
          app (presentation S.X₁).g _ (app m.τ₂ _ (p j))
        rw [← app_res]
        change app m.τ₃ _ (globalZero U q j) = _
        rw [hq]
        change app m.τ₃ _ (app S.g _ (p j)) = _
        rw [app_comp, ← m.comm₂₃, app_comp] }
  rw [cechOneClass_eq_descentClass U hU c hc d]
  change (sectionExtZero ⊤ (app m.τ₃ ⊤ q)).comp (presentation_shortExact S.X₁).extClass rfl = _
  rw [sectionExtZero_app]
  simpa only [m, coefficientPresentationMap_left, Ext.comp_mk₀_id] using
    (connecting_naturality hS (presentation_shortExact S.X₁) m 0 (sectionExtZero ⊤ q)).symm

end Cech

open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app sectionExtZero)

section Homeomorphism
variable {X : TopCat.{0}} (h : X ≅ X)
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

open CycleQ2AutomorphismGlobalSections CycleQ2FiniteCechOrbitPullback

/-- The equivalence on the actual cohomology at the top open, in direct-image direction. -/
def pushH (B : AbSheaf X) (n : ℕ) : B.H' n ⊤ ≃+ ((pushFunctor h).obj B).H' n ⊤ :=
  transport (pushFunctor h) (sourceIso h) B n

/-- Cohomological pullback for a coefficient morphism over a homeomorphism. -/
def pullH {B D : AbSheaf X} (f : B ⟶ (pushFunctor h).obj D) (n : ℕ) : B.H' n ⊤ →+ D.H' n ⊤ :=
  pull (pushFunctor h) (sourceIso h) f n

theorem pushH_connecting {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (n : ℕ) (x : S.X₃.H' n ⊤) : pushH h S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (pushH h S.X₃ n x).comp (hS.map_of_exact (pushFunctor h)).extClass rfl :=
  transport_connecting (pushFunctor h) (sourceIso h) hS n x

theorem pullH_connecting {S T : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (hT : T.ShortExact) (f : S ⟶ T.map (pushFunctor h)) (n : ℕ) (x : S.X₃.H' n ⊤) :
    (pullH h f.τ₃ n x).comp hT.extClass rfl =
      pullH h f.τ₁ (n+1) (x.comp hS.extClass rfl) :=
  pull_connecting (pushFunctor h) (sourceIso h) hS hT f n x

theorem pushH_cechOneClass
    {ι : Type} [Fintype ι] {B : AbSheaf X} (U : ι → Opens X)
    (hU : (⨆ j, U j) = ⊤) (hV : (⨆ j, (Opens.map h.hom).obj (U j)) = ⊤)
    (c : One B (fun j => (Opens.map h.hom).obj (U j)))
    (hc : IsOneCocycle B _ c) (hd : IsOneCocycle ((pushFunctor h).obj B) U c) :
    pushH h B 1 (cechOneClass _ hV c hc) = cechOneClass U hU c hd := by
  let V := fun j => (Opens.map h.hom).obj (U j)
  let d := Classical.choice (oneDescent_nonempty V hV c hc)
  rw [cechOneClass_eq_descentClass V hV c hc d]
  change pushH h B 1 ((sectionExtZero ⊤ d.globalSection).comp
    (presentation_shortExact B).extClass rfl) = _
  refine (pushH_connecting h (presentation_shortExact B) 0
    (sectionExtZero ⊤ d.globalSection)).trans ?_
  have hq : pushH h _ 0 (sectionExtZero ⊤ d.globalSection) =
      sectionExtZero (F := (pushFunctor h).obj (presentation B).X₃) ⊤ d.globalSection :=
    sourceIso_sectionExtZero h _ _
  refine (congrArg (fun x : ((pushFunctor h).obj (presentation B).X₃).H' 0 ⊤ =>
    x.comp ((presentation_shortExact B).map_of_exact (pushFunctor h)).extClass rfl) hq).trans ?_
  symm
  apply cechOneClass_of_lifts U hU ((presentation_shortExact B).map_of_exact (pushFunctor h))
    c hd d.primitive d.globalSection
  · intro j k W hj hk
    exact d.differential j k ((Opens.map h.hom).obj W)
      (fun _ hx => hj hx) (fun _ hx => hk hx)
  · exact d.global_restriction

/-- On Čech one-classes the derived pullback applies the coefficient map to each edge. -/
theorem pullH_cechOneClass {ι : Type} [Fintype ι] (U : ι → Opens X)
    (hU : (⨆ j, U j) = ⊤) (hV : (⨆ j, (Opens.map h.hom).obj (U j)) = ⊤)
    {B D : AbSheaf X} (f : B ⟶ (pushFunctor h).obj D) (c : One B U) (hc : IsOneCocycle B U c) :
    pullH h f 1 (cechOneClass U hU c hc) =
      cechOneClass (cover h.hom U) hV (pullOne h.hom f U c) (pullOne_closed h.hom f U c hc) := by
  apply (pushH h D 1).injective
  change (pushH h D 1) ((pushH h D 1).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  exact (cechOneClass_naturality U hU f c hc).trans
    (pushH_cechOneClass h U hU hV (pullOne h.hom f U c) (pullOne_closed h.hom f U c hc)
      (mapOne_closed U f c hc)).symm

end Homeomorphism
end CycleQ2AutomorphismCohomology
end

#print axioms CycleQ2AutomorphismCohomology.pull_connecting

#print axioms CycleQ2AutomorphismCohomology.pullH_connecting
#print axioms CycleQ2AutomorphismCohomology.pullH_cechOneClass
