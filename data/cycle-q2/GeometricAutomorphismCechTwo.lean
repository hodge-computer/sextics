import Proposal.GeometricFiniteCechOrbitPullback
import Proposal.GeometricAutomorphismCohomology

/-!
# The action of a homeomorphism on normalized Čech two-classes

The first lift of a normalized cocycle expresses its derived class as a
connecting class. Its edge and face identities on inverse images are
precisely the identities of the corresponding direct image sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2AutomorphismCechTwo

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechConnecting
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app)

variable {X Y : TopCat.{0}} {ι : Type} (g : X ⟶ Y) (U : ι → Opens Y)

open CycleQ2FiniteCechOrbitPullback (cover pullTwo pullTwo_normalized pullTwo_closed)

private theorem preimage_le {W V : Opens Y} (h : W ≤ V) :
    (Opens.map g).obj W ≤ (Opens.map g).obj V := fun _ hx => h hx

theorem directImage_normalized {F : AbSheaf X} {c : Two F (cover g U)}
    (hn : NormalizedTwo F (cover g U) c) :
    NormalizedTwo ((TopCat.Sheaf.pushforward AddCommGrpCat g).obj F) U c where
  repeat12 i k W hi hk := hn.repeat12 i k ((Opens.map g).obj W) (preimage_le g hi) (preimage_le g hk)
  repeat23 i j W hi hj := hn.repeat23 i j ((Opens.map g).obj W) (preimage_le g hi) (preimage_le g hj)
  swap12 i j k W hi hj hk := hn.swap12 i j k ((Opens.map g).obj W)
    (preimage_le g hi) (preimage_le g hj) (preimage_le g hk)
  swap23 i j k W hi hj hk := hn.swap23 i j k ((Opens.map g).obj W)
    (preimage_le g hi) (preimage_le g hj) (preimage_le g hk)

theorem directImage_closed {F : AbSheaf X} {c : Two F (cover g U)}
    (hc : IsTwoCocycle F (cover g U) c) :
    IsTwoCocycle ((TopCat.Sheaf.pushforward AddCommGrpCat g).obj F) U c :=
  fun i j k l W hi hj hk hl =>
    hc i j k l ((Opens.map g).obj W) (preimage_le g hi) (preimage_le g hj)
      (preimage_le g hk) (preimage_le g hl)

private theorem directImage_boundary {S : ShortComplex (AbSheaf X)}
    {b : One S.X₂ (cover g U)} {c : Two S.X₁ (cover g U)}
    (hb : ∀ i j k W hi hj hk,
      boundaryValue S.X₂ (cover g U) b i j k W hi hj hk =
        app S.f W (faceValue S.X₁ (cover g U) c i j k W hi hj hk)) :
    ∀ i j k W hi hj hk,
      boundaryValue ((TopCat.Sheaf.pushforward AddCommGrpCat g).obj S.X₂) U b i j k W hi hj hk =
        app ((TopCat.Sheaf.pushforward AddCommGrpCat g).map S.f) W
          (faceValue ((TopCat.Sheaf.pushforward AddCommGrpCat g).obj S.X₁) U c i j k W hi hj hk) :=
  fun i j k W hi hj hk => hb i j k ((Opens.map g).obj W) (preimage_le g hi)
    (preimage_le g hj) (preimage_le g hk)

section Action

local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

private theorem oneClass_congr [Fintype ι] {F : AbSheaf X} (U : ι → Opens X)
    (hU : (⨆ i, U i) = ⊤) {a b : One F U} (hab : a = b)
    (ha : IsOneCocycle F U a) (hb : IsOneCocycle F U b) :
    cechOneClass U hU a ha = cechOneClass U hU b hb := by
  subst b
  rfl

/-- Changing coefficients in a normalized finite-cover two-cocycle induces
the standard covariant map on its genuine derived class. -/
theorem cechTwoClass_map [Fintype ι] {F G : AbSheaf X} (U : ι → Opens X)
    (hU : (⨆ i, U i) = ⊤) (f : F ⟶ G) (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    (cechTwoClass U hU c hn hc).comp (Ext.mk₀ f) (add_zero 2) =
      cechTwoClass U hU (mapTwo U f c) (mapTwo_normalized U f c hn) (mapTwo_closed U f c hc) := by
  let d := Classical.choice (twoDescent_nonempty U hU c hn hc)
  let m := CycleQ2CechTwoNaturality.presentationMap f
  let b := mapOne U m.τ₂ d.first
  have hb : ∀ i j k W hi hj hk,
      boundaryValue (presentation G).X₂ U b i j k W hi hj hk =
        app (presentation G).f W (faceValue G U (mapTwo U f c) i j k W hi hj hk) := by
    intro i j k W hi hj hk
    rw [show b = mapOne U m.τ₂ d.first from rfl, boundaryValue_mapOne,
      d.first_differential, faceValue_mapTwo,
      CycleQ2CechTwoToDerived.app_comp, CycleQ2CechTwoToDerived.app_comp]
    exact congrArg (fun k => app k W _) m.comm₁₂.symm
  have hm : mapOne U m.τ₃ (mapOne U (presentation F).g d.first) = mapOne U (presentation G).g b := by
    funext i j
    exact congrArg (fun k => app k _ (d.first i j)) m.comm₂₃.symm
  have hF := presentation_shortExact F
  have hG := presentation_shortExact G
  have hleft := cechOneClass_connecting U hF hU d.first c hn hc d.first_differential
  have hclosed := primitive_image_closed U (presentation F) c d.first d.first_differential
  have hmiddle := CycleQ2CechTwoNaturality.connecting_naturality hF hG m 1
    (cechOneClass U hU (mapOne U (presentation F).g d.first) hclosed)
  rw [← hleft]
  refine hmiddle.trans ?_
  have hmap := cechOneClass_naturality U hU m.τ₃ _ hclosed
  have hc' := primitive_image_closed U (presentation G) (mapTwo U f c) b hb
  have hfirst := hmap.trans (oneClass_congr U hU hm _ hc')
  exact (congrArg (fun x : (presentation G).X₃.H' 1 ⊤ => x.comp hG.extClass rfl) hfirst).trans
    (cechOneClass_connecting U hG hU b (mapTwo U f c) _ _ hb)

open CycleQ2AutomorphismCohomology CycleQ2AutomorphismGlobalSections

/-- The isomorphism on `H' 2 ⊤` sends a normalized class to the class of
the same sections read in the direct image sheaf. -/
theorem pushH_cechTwoClass [Fintype ι] (h : X ≅ X) (U : ι → Opens X)
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ i, (Opens.map h.hom).obj (U i)) = ⊤)
    {F : AbSheaf X} (c : Two F (cover h.hom U))
    (hn : NormalizedTwo F (cover h.hom U) c)
    (hc : IsTwoCocycle F (cover h.hom U) c) :
    pushH h F 2 (cechTwoClass _ hV c hn hc) =
      cechTwoClass U hU c (directImage_normalized h.hom U hn) (directImage_closed h.hom U hc) := by
  let V := cover h.hom U
  let S := presentation F
  let P := pushFunctor h
  let d := Classical.choice (twoDescent_nonempty V hV c hn hc)
  have hS : S.ShortExact := presentation_shortExact F
  have hp := hS.map_of_exact P
  have hb := directImage_boundary h.hom U (S := S) d.first_differential
  have he := cechOneClass_connecting V hS hV d.first c hn hc d.first_differential
  have he' := cechOneClass_connecting U hp hU d.first c
    (directImage_normalized h.hom U hn) (directImage_closed h.hom U hc) hb
  rw [← he]
  refine (pushH_connecting h hS 1 _).trans ?_
  exact (congrArg (fun x : ((S.map P).X₃).H' 1 ⊤ => x.comp hp.extClass (rfl : 1+1=2))
    (pushH_cechOneClass h U hU hV (mapOne V S.g d.first)
      (primitive_image_closed V S c d.first d.first_differential)
      (primitive_image_closed U (S.map P) c d.first hb))).trans he'

/-- The canonical pullback on `H' 2 ⊤` acts on a normalized cocycle by
applying the coefficient morphism to each of its face sections. -/
theorem pullH_cechTwoClass [Fintype ι] (h : X ≅ X) (U : ι → Opens X)
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ i, (Opens.map h.hom).obj (U i)) = ⊤)
    {F G : AbSheaf X} (φ : F ⟶ (pushFunctor h).obj G) (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    pullH h φ 2 (cechTwoClass U hU c hn hc) =
      cechTwoClass (cover h.hom U) hV (pullTwo h.hom φ U c)
        (pullTwo_normalized h.hom φ U c hn) (pullTwo_closed h.hom φ U c hc) := by
  apply (pushH h G 2).injective
  change (pushH h G 2) ((pushH h G 2).symm _) = _
  rw [AddEquiv.apply_symm_apply, pushH_cechTwoClass h U hU hV]
  exact cechTwoClass_map U hU φ c hn hc

end Action
end CycleQ2AutomorphismCechTwo
end

#print axioms CycleQ2AutomorphismCechTwo.pushH_cechTwoClass
#print axioms CycleQ2AutomorphismCechTwo.pullH_cechTwoClass
