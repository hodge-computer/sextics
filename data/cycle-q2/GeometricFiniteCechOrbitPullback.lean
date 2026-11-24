import Proposal.GeometricFiniteCechConnecting

/-!
# Pullback of finite Čech cocycles and their connecting classes

A map into the direct image gives sections on the inverse images of the
original intersections. Restricting those sections to arbitrary subopens
preserves cocycle and primitive identities.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteCechOrbitPullback

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
open CycleQ2CechTwoToDerived (app app_res app_comp)

variable {X Y : TopCat.{0}} {ι : Type} (g : Y ⟶ X)

abbrev pre (V : Opens X) := (Opens.map g).obj V
abbrev push (G : AbSheaf Y) := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj G
abbrev cover (U : ι → Opens X) (i : ι) := pre g (U i)

theorem cover_top (U : ι → Opens X) (h : (⨆ i, U i) = ⊤) :
    (⨆ i, cover g U i) = ⊤ := by
  change (⨆ i, (Opens.map g).obj (U i)) = ⊤
  exact (Opens.map_iSup g U).symm.trans ((congrArg (Opens.map g).obj h).trans (Opens.map_top g))

variable {F : AbSheaf X} {G : AbSheaf Y} (φ : F ⟶ push g G)

def pullTo {V : Opens X} {W : Opens Y} (h : W ≤ pre g V) :
    Sections F V →+ Sections G W :=
  (res G h).comp (app φ V)

theorem pullTo_res {P V : Opens X} {W : Opens Y}
    (h : W ≤ pre g P) (hPV : P ≤ V) (x : Sections F V) :
    pullTo g φ h (res F hPV x) = pullTo g φ (fun _ hx => hPV (h hx)) x := by
  change res G h (app φ P (res F hPV x)) = _
  rw [app_res]
  exact res_comp G (fun _ hx => hPV hx) h _

variable (U : ι → Opens X)

def pullOne (b : One F U) : One G (cover g U) :=
  fun i j => app φ (U i ⊓ U j) (b i j)

def pullTwo (c : Two F U) : Two G (cover g U) :=
  fun i j k => app φ ((U i ⊓ U j) ⊓ U k) (c i j k)

theorem edgeValue_pullOne (b : One F U) (i j : ι) {P : Opens X} {W : Opens Y}
    (h : W ≤ pre g P) (hi : P ≤ U i) (hj : P ≤ U j) :
    edgeValue G (cover g U) (pullOne g φ U b) i j W
      (fun _ hx => hi (h hx)) (fun _ hx => hj (h hx)) =
      pullTo g φ h (edgeValue F U b i j P hi hj) :=
  (pullTo_res g φ h (le_inf hi hj) (b i j)).symm

theorem faceValue_pullTwo (c : Two F U) (i j k : ι) {P : Opens X} {W : Opens Y}
    (h : W ≤ pre g P) (hi : P ≤ U i) (hj : P ≤ U j) (hk : P ≤ U k) :
    faceValue G (cover g U) (pullTwo g φ U c) i j k W
      (fun _ hx => hi (h hx)) (fun _ hx => hj (h hx)) (fun _ hx => hk (h hx)) =
      pullTo g φ h (faceValue F U c i j k P hi hj hk) :=
  (pullTo_res g φ h (le_inf (le_inf hi hj) hk) (c i j k)).symm

theorem boundaryValue_pullOne (b : One F U) (i j k : ι) {P : Opens X} {W : Opens Y}
    (h : W ≤ pre g P) (hi : P ≤ U i) (hj : P ≤ U j) (hk : P ≤ U k) :
    boundaryValue G (cover g U) (pullOne g φ U b) i j k W
      (fun _ hx => hi (h hx)) (fun _ hx => hj (h hx)) (fun _ hx => hk (h hx)) =
      pullTo g φ h (boundaryValue F U b i j k P hi hj hk) := by
  simp only [boundaryValue, map_add, map_sub, edgeValue_pullOne g φ U b _ _ h hi hj,
    edgeValue_pullOne g φ U b _ _ h hi hk, edgeValue_pullOne g φ U b _ _ h hj hk]

theorem pullOne_closed (b : One F U) (hb : IsOneCocycle F U b) :
    IsOneCocycle G (cover g U) (pullOne g φ U b) := by
  intro i j k W hi hj hk
  let P := (U i ⊓ U j) ⊓ U k
  have ei : P ≤ U i := inf_le_left.trans inf_le_left
  have ej : P ≤ U j := inf_le_left.trans inf_le_right
  have ek : P ≤ U k := inf_le_right
  have h : W ≤ pre g P := le_inf (le_inf hi hj) hk
  change edgeValue _ _ _ i k W hi hk = edgeValue _ _ _ i j W hi hj + edgeValue _ _ _ j k W hj hk
  rw [edgeValue_pullOne g φ U b i k h ei ek, edgeValue_pullOne g φ U b i j h ei ej,
    edgeValue_pullOne g φ U b j k h ej ek, ← map_add]
  exact congrArg _ (hb i j k P ei ej ek)

theorem pullTwo_normalized (c : Two F U) (hc : NormalizedTwo F U c) :
    NormalizedTwo G (cover g U) (pullTwo g φ U c) where
  repeat12 i k W hi hk := by
    have h : W ≤ pre g (U i ⊓ U k) := le_inf hi hk
    rw [faceValue_pullTwo g φ U c i i k h inf_le_left inf_le_left inf_le_right,
      hc.repeat12, map_zero]
  repeat23 i j W hi hj := by
    have h : W ≤ pre g (U i ⊓ U j) := le_inf hi hj
    rw [faceValue_pullTwo g φ U c i j j h inf_le_left inf_le_right inf_le_right,
      hc.repeat23, map_zero]
  swap12 i j k W hi hj hk := by
    let P := (U i ⊓ U j) ⊓ U k
    have ei : P ≤ U i := inf_le_left.trans inf_le_left
    have ej : P ≤ U j := inf_le_left.trans inf_le_right
    have ek : P ≤ U k := inf_le_right
    have h : W ≤ pre g P := le_inf (le_inf hi hj) hk
    rw [faceValue_pullTwo g φ U c i j k h ei ej ek, faceValue_pullTwo g φ U c j i k h ej ei ek,
      hc.swap12, map_neg]
  swap23 i j k W hi hj hk := by
    let P := (U i ⊓ U j) ⊓ U k
    have ei : P ≤ U i := inf_le_left.trans inf_le_left
    have ej : P ≤ U j := inf_le_left.trans inf_le_right
    have ek : P ≤ U k := inf_le_right
    have h : W ≤ pre g P := le_inf (le_inf hi hj) hk
    rw [faceValue_pullTwo g φ U c i j k h ei ej ek, faceValue_pullTwo g φ U c i k j h ei ek ej,
      hc.swap23, map_neg]

theorem pullTwo_closed (c : Two F U) (hc : IsTwoCocycle F U c) :
    IsTwoCocycle G (cover g U) (pullTwo g φ U c) := by
  intro i j k l W hi hj hk hl
  let P := (U i ⊓ U j) ⊓ (U k ⊓ U l)
  have ei : P ≤ U i := inf_le_left.trans inf_le_left
  have ej : P ≤ U j := inf_le_left.trans inf_le_right
  have ek : P ≤ U k := inf_le_right.trans inf_le_left
  have el : P ≤ U l := inf_le_right.trans inf_le_right
  have h : W ≤ pre g P := le_inf (le_inf hi hj) (le_inf hk hl)
  rw [faceValue_pullTwo g φ U c j k l h ej ek el, faceValue_pullTwo g φ U c i k l h ei ek el,
    faceValue_pullTwo g φ U c i j l h ei ej el, faceValue_pullTwo g φ U c i j k h ei ej ek,
    ← map_sub, ← map_add, ← map_sub, hc i j k l P ei ej ek el, map_zero]

variable {F₁ F₂ : AbSheaf X} {G₁ G₂ : AbSheaf Y}

theorem pullTo_app
    (a : F₁ ⟶ F₂) (a' : G₁ ⟶ G₂) (φ₁ : F₁ ⟶ push g G₁) (φ₂ : F₂ ⟶ push g G₂)
    (sq : a ≫ φ₂ = φ₁ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map a')
    {P : Opens X} {W : Opens Y} (h : W ≤ pre g P) (x : Sections F₁ P) :
    pullTo g φ₂ h (app a P x) = app a' W (pullTo g φ₁ h x) := by
  change res G₂ h (app φ₂ P (app a P x)) = app a' W (res G₁ h (app φ₁ P x))
  rw [app_comp, sq, app_res]
  rfl

theorem pullOne_mapOne
    (a : F₁ ⟶ F₂) (a' : G₁ ⟶ G₂) (φ₁ : F₁ ⟶ push g G₁) (φ₂ : F₂ ⟶ push g G₂)
    (sq : a ≫ φ₂ = φ₁ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map a')
    (b : One F₁ U) :
    pullOne g φ₂ U (mapOne U a b) = mapOne (cover g U) a' (pullOne g φ₁ U b) := by
  funext i j
  change app φ₂ _ (app a _ _) = app a' _ (app φ₁ _ _)
  rw [app_comp, sq]
  rfl

variable {S : ShortComplex (AbSheaf X)} {T : ShortComplex (AbSheaf Y)}
  (φ₁ : S.X₁ ⟶ push g T.X₁) (φ₂ : S.X₂ ⟶ push g T.X₂) (φ₃ : S.X₃ ⟶ push g T.X₃)

theorem pull_boundary (sq : S.f ≫ φ₂ = φ₁ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map T.f)
    (b : One S.X₂ U) (c : Two S.X₁ U)
    (hb : ∀ i j k W hi hj hk, boundaryValue S.X₂ U b i j k W hi hj hk =
      app S.f W (faceValue S.X₁ U c i j k W hi hj hk))
    (i j k : ι) (W : Opens Y)
    (hi : W ≤ cover g U i) (hj : W ≤ cover g U j) (hk : W ≤ cover g U k) :
    boundaryValue T.X₂ (cover g U) (pullOne g φ₂ U b) i j k W hi hj hk =
      app T.f W (faceValue T.X₁ (cover g U) (pullTwo g φ₁ U c) i j k W hi hj hk) := by
  let P := (U i ⊓ U j) ⊓ U k
  have ei : P ≤ U i := inf_le_left.trans inf_le_left
  have ej : P ≤ U j := inf_le_left.trans inf_le_right
  have ek : P ≤ U k := inf_le_right
  have h : W ≤ pre g P := le_inf (le_inf hi hj) hk
  rw [boundaryValue_pullOne g φ₂ U b i j k h ei ej ek, faceValue_pullTwo g φ₁ U c i j k h ei ej ek,
    hb i j k P ei ej ek, pullTo_app g S.f T.f φ₁ φ₂ sq]

local instance pullSheafHasExt : HasExt.{1} (AbSheaf Y) := HasExt.standard _

/-- The actual connecting map on the inverse-image cover, with both input
and output represented by the pointwise pullbacks of the original sections. -/
theorem pullOneClass_connecting [Fintype ι] (hT : T.ShortExact) (hcover : (⨆ i, U i) = ⊤)
    (sq₁ : S.f ≫ φ₂ = φ₁ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map T.f)
    (sq₂ : S.g ≫ φ₃ = φ₂ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map T.g)
    (b : One S.X₂ U) (c : Two S.X₁ U)
    (hn : NormalizedTwo S.X₁ U c) (hc : IsTwoCocycle S.X₁ U c)
    (hb : ∀ i j k W hi hj hk, boundaryValue S.X₂ U b i j k W hi hj hk =
      app S.f W (faceValue S.X₁ U c i j k W hi hj hk)) :
    (cechOneClass (cover g U) (cover_top g U hcover) (pullOne g φ₃ U (mapOne U S.g b))
      (pullOne_closed g φ₃ U _ (primitive_image_closed U S c b hb))).comp hT.extClass rfl =
      cechTwoClass (cover g U) (cover_top g U hcover) (pullTwo g φ₁ U c)
        (pullTwo_normalized g φ₁ U c hn) (pullTwo_closed g φ₁ U c hc) := by
  have h := CycleQ2FiniteCechConnecting.cechOneClass_connecting (cover g U) hT
    (cover_top g U hcover) (pullOne g φ₂ U b) (pullTwo g φ₁ U c)
    (pullTwo_normalized g φ₁ U c hn) (pullTwo_closed g φ₁ U c hc)
    (pull_boundary g U φ₁ φ₂ sq₁ b c hb)
  have e := pullOne_mapOne g U S.g T.g φ₂ φ₃ sq₂ b
  convert h using 1
  congr 2

end CycleQ2FiniteCechOrbitPullback

end

#print axioms CycleQ2FiniteCechOrbitPullback.pullTwo_closed
#print axioms CycleQ2FiniteCechOrbitPullback.pullOneClass_connecting
