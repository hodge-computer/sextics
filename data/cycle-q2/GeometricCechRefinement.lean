import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricCartierCoordinateDescent


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CechTwoRefinement

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
open CycleQ2CechTwoComparison

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable (F : AbSheaf X) {U V W : Fin 4 → Opens X}
variable (h : ∀ i, V i ≤ U i)

/-- Actual restriction on every vertex of a pointwise refinement. -/
def restrictZero : Zero F U →+ Zero F V where
  toFun q i := res F (h i) (q i)
  map_zero' := by funext i; exact map_zero _
  map_add' q r := by funext i; exact map_add _ _ _

/-- Actual restrictions on the six edges, in the original fixed order. -/
def restrictOne : One F U →+ One F V where
  toFun c :=
    ⟨res F (inf_le_inf (h 0) (h 1)) c.1,
     res F (inf_le_inf (h 0) (h 2)) c.2.1,
     res F (inf_le_inf (h 0) (h 3)) c.2.2.1,
     res F (inf_le_inf (h 1) (h 2)) c.2.2.2.1,
     res F (inf_le_inf (h 1) (h 3)) c.2.2.2.2.1,
     res F (inf_le_inf (h 2) (h 3)) c.2.2.2.2.2⟩
  map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]
  map_add' c d := by simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

/-- Actual restrictions on the four faces; no face is renamed or rescaled. -/
def restrictTwo : Two F U →+ Two F V where
  toFun c :=
    ⟨res F (inf_le_inf (inf_le_inf (h 0) (h 1)) (h 2)) c.1,
     res F (inf_le_inf (inf_le_inf (h 0) (h 1)) (h 3)) c.2.1,
     res F (inf_le_inf (inf_le_inf (h 0) (h 2)) (h 3)) c.2.2.1,
     res F (inf_le_inf (inf_le_inf (h 1) (h 2)) (h 3)) c.2.2.2⟩
  map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]
  map_add' c d := by simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

def restrictThree : Three F U →+ Three F V :=
  res F (inf_le_inf (inf_le_inf (inf_le_inf (h 0) (h 1)) (h 2)) (h 3))

theorem restrict_d0 (q : Zero F U) :
    restrictOne F h (d0 F U q) = d0 F V (restrictZero F h q) := by
  simp only [restrictOne, restrictZero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    d0, map_sub, res_comp]

theorem restrict_d1 (c : One F U) :
    restrictTwo F h (d1 F U c) = d1 F V (restrictOne F h c) := by
  simp only [restrictTwo, restrictOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    d1, map_sub, map_add, res_comp]

theorem restrict_d2 (c : Two F U) :
    restrictThree F h (d2 F U c) = d2 F V (restrictTwo F h c) := by
  simp only [restrictThree, restrictTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    d2, map_sub, map_add, res_comp]

variable {F} {G : AbSheaf X}

theorem restrictZero_mapZero (f : F ⟶ G) (q : Zero F U) :
    restrictZero G h (mapZero U f q) = mapZero V f (restrictZero F h q) := by
  funext i
  exact (app_res f (h i) (q i)).symm

theorem restrictOne_mapOne (f : F ⟶ G) (c : One F U) :
    restrictOne G h (mapOne U f c) = mapOne V f (restrictOne F h c) := by
  simp only [restrictOne, mapOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, app_res]

theorem restrictTwo_mapTwo (f : F ⟶ G) (c : Two F U) :
    restrictTwo G h (mapTwo U f c) = mapTwo V f (restrictTwo F h c) := by
  simp only [restrictTwo, mapTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, app_res]

theorem restrict_globalZero (x : Sections F ⊤) :
    restrictZero F h (globalZero U x) = globalZero V x := by
  funext i
  exact res_comp F _ _ x

/-- The actual injective descent restricts to the smaller cover. Its global
section and both injective presentations remain exactly the original ones. -/
def restrictDescent {c : Two F U} (d : TwoDescent U c) :
    TwoDescent V (restrictTwo F h c) where
  first := restrictOne _ h d.first
  first_differential := by
    rw [← restrict_d1, d.first_differential, restrictTwo_mapTwo]
  second := restrictZero _ h d.second
  second_differential := by
    rw [← restrict_d0, d.second_differential, restrictOne_mapOne, restrictOne_mapOne]
  globalSection := d.globalSection
  global_restriction := by
    rw [← restrict_globalZero h d.globalSection, d.global_restriction, restrictZero_mapZero]

@[simp] theorem descentClass_restriction {c : Two F U} (d : TwoDescent U c) :
    descentClass V (restrictDescent h d) = descentClass U d := rfl

theorem restriction_closed (c : Two F U) (hc : d2 F U c = 0) :
    d2 F V (restrictTwo F h c) = 0 := by
  rw [← restrict_d2, hc, map_zero]

/-- Changing the actual four-open cover by pointwise refinement preserves the
actual derived class, not merely zero/nonzero status. -/
theorem cechTwoClass_refinement
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ i, V i) = ⊤)
    (c : Two F U) (hc : d2 F U c = 0) :
    cechTwoClass V hV (restrictTwo F h c) (restriction_closed h c hc) =
      cechTwoClass U hU c hc := by
  let d := Classical.choice (twoDescent_nonempty U hU c hc)
  calc
    _ = descentClass V (restrictDescent h d) :=
      cechTwoClass_eq_descentClass V hV _ _ (restrictDescent h d)
    _ = descentClass U d := rfl
    _ = _ := (cechTwoClass_eq_descentClass U hU c hc d).symm

/-- Pointwise refinement on the actual cycle subgroup. -/
def cyclesRestriction : twoCycles (F := F) U →+ twoCycles (F := F) V where
  toFun c := ⟨restrictTwo F h c.val, restriction_closed h c.val c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext ((restrictTwo F h).map_add c.val d.val)

theorem cyclesRestriction_boundaries :
    twoBoundaries (F := F) U ≤ (twoBoundaries (F := F) V).comap (cyclesRestriction h) := by
  intro c hc
  obtain ⟨a, rfl⟩ := hc
  apply (twoBoundaries_mem_iff V _).mpr
  exact ⟨restrictOne F h a, (restrict_d1 F h a).symm⟩

def quotientRestriction : CechTwo (F := F) U →+ CechTwo (F := F) V :=
  QuotientAddGroup.map (twoBoundaries U) (twoBoundaries V) (cyclesRestriction h)
    (cyclesRestriction_boundaries h)

@[simp] theorem quotientRestriction_mk (c : twoCycles (F := F) U) :
    quotientRestriction h (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (cyclesRestriction h c) := rfl

/-- The actual Cech-to-derived comparison commutes with the actual cover
restriction map. No local H1 vanishing is needed for this identity. -/
theorem comparison_refinement (hU : (⨆ i, U i) = ⊤) (hV : (⨆ i, V i) = ⊤) :
    (comparison (F := F) V hV).comp (quotientRestriction h) = comparison U hU := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  exact cechTwoClass_refinement h hU hV c.val c.property

/-- If the original cover has the required local vanishing, refinement cannot
kill an original Cech class. The refined cover needs no extra local premise. -/
theorem quotientRestriction_injective
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ i, V i) = ⊤)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i))) :
    Function.Injective (quotientRestriction (F := F) h) := by
  intro x y hxy
  apply comparison_injective U hU hlocal
  have he := congrArg (comparison (F := F) V hV) hxy
  simpa only [← AddMonoidHom.comp_apply, comparison_refinement h hU hV] using he

end CycleQ2CechTwoRefinement

#print axioms CycleQ2CechTwoRefinement.cechTwoClass_refinement
#print axioms CycleQ2CechTwoRefinement.comparison_refinement
#print axioms CycleQ2CechTwoRefinement.quotientRestriction_injective


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FiniteInjectiveCech

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

variable {X : TopCat.{0}} {ι : Type}
variable (F : AbSheaf X) [Injective F] (U : ι → Opens X)

/-- Ordered pair sections of the actual sheaf. -/
abbrev One := ∀ i j, Sections F (U i ⊓ U j)

/-- The additive one-cocycle identity, with every value restricted by the
actual sheaf maps to the same common open. -/
def IsOneCocycle (c : One F U) : Prop :=
  ∀ i j k (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
    res F (le_inf hi hk) (c i k) =
      res F (le_inf hi hj) (c i j) + res F (le_inf hj hk) (c j k)

variable {F U}

omit [Injective F] in
theorem oneCocycle_diagonal (c : One F U) (hc : IsOneCocycle F U c)
    (i : ι) (W : Opens X) (hi : W ≤ U i) :
    res F (le_inf hi hi) (c i i) = 0 := by
  have h := hc i i i W hi hi hi
  linear_combination (norm := abel) -h

/-- The primitive is constructed on any finite subfamily, using gluing on
the actual overlaps followed by injective extension to each new open. -/
theorem oneCocycle_primitive_on_finset (c : One F U) (hc : IsOneCocycle F U c)
    (s : Finset ι) :
    ∃ q : ∀ i, Sections F (U i),
      ∀ i ∈ s, ∀ j ∈ s, ∀ (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        res F hj (q j) - res F hi (q i) = res F (le_inf hi hj) (c i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨q, hq⟩ := ih
    let V : s → Opens X := fun j => U j.val ⊓ U k
    let a : ∀ j, Sections F (V j) :=
      fun j => res F inf_le_left (q j.val) + c j.val k
    obtain ⟨v, hv⟩ := extend_family F V (U k) (fun _ => inf_le_right) a (by
      intro i j W hi hj
      have hiU : W ≤ U i.val := hi.trans inf_le_left
      have hjU : W ≤ U j.val := hj.trans inf_le_left
      have hkU : W ≤ U k := hi.trans inf_le_right
      have hb := hq i.val i.property j.val j.property W hiU hjU
      have hz := hc i.val j.val k W hiU hjU hkU
      change res F hi (res F inf_le_left (q i.val) + c i.val k) =
        res F hj (res F inf_le_left (q j.val) + c j.val k)
      have hri : res F hi (res F inf_le_left (q i.val)) = res F hiU (q i.val) :=
        res_comp F inf_le_left hi (q i.val)
      have hrj : res F hj (res F inf_le_left (q j.val)) = res F hjU (q j.val) :=
        res_comp F inf_le_left hj (q j.val)
      rw [map_add, map_add, hri, hrj]
      linear_combination (norm := abel) hz - hb)
    let q' : ∀ i, Sections F (U i) := Function.update q k v
    have hnew : q' k = v := Function.update_self _ _ _
    have hold (i : ι) (hi : i ∈ s) : q' i = q i := by
      apply Function.update_of_ne
      exact fun hik => hks (hik ▸ hi)
    refine ⟨q', ?_⟩
    intro i hi j hj W hiW hjW
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        rw [sub_self]
        exact (oneCocycle_diagonal c hc k W hiW).symm
      · rw [hnew, hold j hj]
        have hvj := congrArg (res F (le_inf hjW hiW)) (hv ⟨j, hj⟩)
        change res F (le_inf hjW hiW) (res F inf_le_right v) =
          res F (le_inf hjW hiW) (res F inf_le_left (q j) + c j k) at hvj
        simp only [map_add, res_comp] at hvj
        have hz := hc j k j W hjW hiW hjW
        rw [oneCocycle_diagonal c hc j W hjW] at hz
        linear_combination (norm := abel) hz - hvj
    · rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        rw [hold i hi, hnew]
        have hvi := congrArg (res F (le_inf hiW hjW)) (hv ⟨i, hi⟩)
        change res F (le_inf hiW hjW) (res F inf_le_right v) =
          res F (le_inf hiW hjW) (res F inf_le_left (q i) + c i k) at hvi
        simp only [map_add, res_comp] at hvi
        linear_combination (norm := abel) hvi
      · rw [hold i hi, hold j hj]
        exact hq i hi j hj W hiW hjW

/-- Genuine degree-one Cech acyclicity for an injective additive sheaf on
an arbitrary finite family of actual opens. No cover or vanishing hypothesis
is needed, and the primitive uses the actual restriction maps. -/
theorem oneCocycle_has_primitive [Fintype ι] (c : One F U)
    (hc : IsOneCocycle F U c) :
    ∃ q : ∀ i, Sections F (U i),
      ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
        res F hj (q j) - res F hi (q i) = res F (le_inf hi hj) (c i j) := by
  obtain ⟨q, hq⟩ := oneCocycle_primitive_on_finset c hc Finset.univ
  exact ⟨q, fun i j W hi hj => hq i (Finset.mem_univ i) j (Finset.mem_univ j) W hi hj⟩

end CycleQ2FiniteInjectiveCech

#print axioms CycleQ2FiniteInjectiveCech.oneCocycle_has_primitive

namespace CycleQ2FiniteInjectiveCech

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

variable {X : TopCat.{0}} {ι : Type}
variable (F : AbSheaf X) (U : ι → Opens X)

abbrev Two := ∀ i j k, Sections F ((U i ⊓ U j) ⊓ U k)

def edgeValue (b : One F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) : Sections F W :=
  res F (le_inf hi hj) (b i j)

def faceValue (c : Two F U) (i j k : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) : Sections F W :=
  res F (le_inf (le_inf hi hj) hk) (c i j k)

def boundaryValue (b : One F U) (i j k : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) : Sections F W :=
  edgeValue F U b j k W hj hk - edgeValue F U b i k W hi hk +
    edgeValue F U b i j W hi hj

/-- Alternation and the zero values on repeated vertices are explicit identities
of actual restricted sections, as in the normalized Cech complex. -/
structure NormalizedTwo (c : Two F U) : Prop where
  repeat12 : ∀ i k W hi hk, faceValue F U c i i k W hi hi hk = 0
  repeat23 : ∀ i j W hi hj, faceValue F U c i j j W hi hj hj = 0
  swap12 : ∀ i j k W hi hj hk,
    faceValue F U c i j k W hi hj hk = -faceValue F U c j i k W hj hi hk
  swap23 : ∀ i j k W hi hj hk,
    faceValue F U c i j k W hi hj hk = -faceValue F U c i k j W hi hk hj

def IsTwoCocycle (c : Two F U) : Prop :=
  ∀ i j k l (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j)
      (hk : W ≤ U k) (hl : W ≤ U l),
    faceValue F U c j k l W hj hk hl - faceValue F U c i k l W hi hk hl +
      faceValue F U c i j l W hi hj hl - faceValue F U c i j k W hi hj hk = 0

variable {F U}

theorem NormalizedTwo.repeat13 {c : Two F U} (hn : NormalizedTwo F U c)
    (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    faceValue F U c i j i W hi hj hi = 0 := by
  rw [hn.swap12, hn.repeat23, neg_zero]

theorem NormalizedTwo.rotate {c : Two F U} (hn : NormalizedTwo F U c)
    (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue F U c k i j W hk hi hj = faceValue F U c i j k W hi hj hk := by
  rw [hn.swap12 k i j W hk hi hj, hn.swap23 i k j W hi hk hj, neg_neg]

variable [Injective F]

/-- Degree-two acyclicity on a finite subfamily, proved by adjoining one
vertex and using the checked degree-one theorem on its intersection family. -/
theorem twoCocycle_primitive_on_finset (c : Two F U) (hn : NormalizedTwo F U c)
    (hc : IsTwoCocycle F U c) (s : Finset ι) :
    ∃ b : One F U, ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
      ∀ (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        boundaryValue F U b i j k W hi hj hk = faceValue F U c i j k W hi hj hk := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨b, hb⟩ := ih
    let V : s → Opens X := fun i => U i.val ⊓ U k
    have hface (i j : s) : V i ⊓ V j ≤ (U i.val ⊓ U j.val) ⊓ U k :=
      le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
    have hedge (i j : s) : V i ⊓ V j ≤ U i.val ⊓ U j.val :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    let w : One F V := fun i j =>
      res F (hface i j) (c i.val j.val k) - res F (hedge i j) (b i.val j.val)
    have hwValue (i j : s) (W : Opens X) (hi : W ≤ V i) (hj : W ≤ V j) :
        res F (le_inf hi hj) (w i j) =
          faceValue F U c i.val j.val k W (hi.trans inf_le_left)
            (hj.trans inf_le_left) (hi.trans inf_le_right) -
          edgeValue F U b i.val j.val W (hi.trans inf_le_left) (hj.trans inf_le_left) := by
      change res F (le_inf hi hj)
        (res F (hface i j) (c i.val j.val k) - res F (hedge i j) (b i.val j.val)) = _
      rw [map_sub, res_comp, res_comp]
      rfl
    have hw : IsOneCocycle F V w := by
      intro i j l W hi hj hl
      rw [hwValue i l W hi hl, hwValue i j W hi hj, hwValue j l W hj hl]
      have hb' := hb i.val i.property j.val j.property l.val l.property W
        (hi.trans inf_le_left) (hj.trans inf_le_left) (hl.trans inf_le_left)
      have hc' := hc i.val j.val l.val k W (hi.trans inf_le_left)
        (hj.trans inf_le_left) (hl.trans inf_le_left) (hi.trans inf_le_right)
      dsimp only [boundaryValue] at hb'
      linear_combination (norm := abel) hb' - hc'
    obtain ⟨q, hq⟩ := oneCocycle_has_primitive w hw
    let a : ∀ i, Sections F (U i ⊓ U k) := fun i =>
      if hi : i ∈ s then q ⟨i, hi⟩ else 0
    have ha (i : ι) (hi : i ∈ s) : a i = q ⟨i,hi⟩ := dif_pos hi
    have hak : a k = 0 := dif_neg hks
    have hcore (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
        (W : Opens X) (hiW : W ≤ U i) (hjW : W ≤ U j) (hkW : W ≤ U k) :
        res F (le_inf hjW hkW) (a j) - res F (le_inf hiW hkW) (a i) +
          edgeValue F U b i j W hiW hjW = faceValue F U c i j k W hiW hjW hkW := by
      rw [ha i hi, ha j hj]
      have hq' := hq ⟨i,hi⟩ ⟨j,hj⟩ W (le_inf hiW hkW) (le_inf hjW hkW)
      rw [hwValue ⟨i,hi⟩ ⟨j,hj⟩ W (le_inf hiW hkW) (le_inf hjW hkW)] at hq'
      linear_combination (norm := abel) hq'
    let b' : One F U := fun i j =>
      if hi : i = k then by
        subst i
        exact -res F (le_inf inf_le_right inf_le_left) (a j)
      else if hj : j = k then by
        subst j
        exact a i
      else b i j
    have hleft (j : ι) : b' k j = -res F (le_inf inf_le_right inf_le_left) (a j) := by
      simp [b']
    have hright (i : ι) (hi : i ≠ k) : b' i k = a i := by
      simp [b', hi]
    have hold (i j : ι) (hi : i ≠ k) (hj : j ≠ k) : b' i j = b i j := by
      simp [b', hi, hj]
    have hneq (i : ι) (hi : i ∈ s) : i ≠ k := fun hik => hks (hik ▸ hi)
    have hleftValue (j : ι) (W : Opens X) (hk : W ≤ U k) (hj : W ≤ U j) :
        edgeValue F U b' k j W hk hj = -res F (le_inf hj hk) (a j) := by
      simp only [edgeValue, hleft, map_neg, res_comp]
    have hrightValue (i : ι) (hi : i ≠ k) (W : Opens X)
        (hiW : W ≤ U i) (hkW : W ≤ U k) :
        edgeValue F U b' i k W hiW hkW = res F (le_inf hiW hkW) (a i) := by
      simp only [edgeValue, hright i hi]
    have holdValue (i j : ι) (hi : i ∈ s) (hj : j ∈ s) (W : Opens X)
        (hiW : W ≤ U i) (hjW : W ≤ U j) :
        edgeValue F U b' i j W hiW hjW = edgeValue F U b i j W hiW hjW := by
      simp only [edgeValue, hold i j (hneq i hi) (hneq j hj)]
    have hkkValue (W : Opens X) (hkW : W ≤ U k) :
        edgeValue F U b' k k W hkW hkW = 0 := by
      rw [hleftValue, hak, map_zero, neg_zero]
    have hlast (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
        (W : Opens X) (hiW : W ≤ U i) (hjW : W ≤ U j) (hkW : W ≤ U k) :
        boundaryValue F U b' i j k W hiW hjW hkW = faceValue F U c i j k W hiW hjW hkW := by
      dsimp only [boundaryValue]
      rw [hrightValue j (hneq j hj), hrightValue i (hneq i hi), holdValue i j hi hj]
      exact hcore i hi j hj W hiW hjW hkW
    have hmiddle (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
        (W : Opens X) (hiW : W ≤ U i) (hjW : W ≤ U j) (hkW : W ≤ U k) :
        boundaryValue F U b' i k j W hiW hkW hjW = faceValue F U c i k j W hiW hkW hjW := by
      dsimp only [boundaryValue]
      rw [hleftValue, holdValue i j hi hj, hrightValue i (hneq i hi), hn.swap23]
      linear_combination (norm := abel) -(hcore i hi j hj W hiW hjW hkW)
    have hfirst (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
        (W : Opens X) (hiW : W ≤ U i) (hjW : W ≤ U j) (hkW : W ≤ U k) :
        boundaryValue F U b' k i j W hkW hiW hjW = faceValue F U c k i j W hkW hiW hjW := by
      dsimp only [boundaryValue]
      rw [holdValue i j hi hj, hleftValue, hleftValue, hn.rotate]
      linear_combination (norm := abel) hcore i hi j hj W hiW hjW hkW
    have hrepeat12 (j : ι) (W : Opens X) (hkW : W ≤ U k) (hjW : W ≤ U j) :
        boundaryValue F U b' k k j W hkW hkW hjW = faceValue F U c k k j W hkW hkW hjW := by
      dsimp only [boundaryValue]
      rw [hkkValue, hn.repeat12, sub_self, add_zero]
    have hrepeat23 (i : ι) (W : Opens X) (hiW : W ≤ U i) (hkW : W ≤ U k) :
        boundaryValue F U b' i k k W hiW hkW hkW = faceValue F U c i k k W hiW hkW hkW := by
      dsimp only [boundaryValue]
      rw [hkkValue, hn.repeat23]
      abel
    have hrepeat13 (j : ι) (hj : j ∈ s) (W : Opens X)
        (hkW : W ≤ U k) (hjW : W ≤ U j) :
        boundaryValue F U b' k j k W hkW hjW hkW = faceValue F U c k j k W hkW hjW hkW := by
      dsimp only [boundaryValue]
      rw [hrightValue j (hneq j hj), hkkValue, hleftValue, hn.repeat13]
      abel
    refine ⟨b', ?_⟩
    intro i hi j hj l hl W hiW hjW hlW
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        exact hrepeat12 l W hiW hlW
      · rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          exact hrepeat13 j hj W hiW hjW
        · exact hfirst j hj l hl W hjW hlW hiW
    · rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          exact hrepeat23 i W hiW hjW
        · exact hmiddle i hi l hl W hiW hlW hjW
      · rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          exact hlast i hi j hj W hiW hjW hlW
        · dsimp only [boundaryValue]
          rw [holdValue j l hj hl, holdValue i l hi hl, holdValue i j hi hj]
          exact hb i hi j hj l hl W hiW hjW hlW

/-- Genuine degree-two Cech acyclicity for normalized alternating cocycles
on any finite family of actual opens of an injective additive sheaf. -/
theorem twoCocycle_has_primitive [Fintype ι] (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    ∃ b : One F U, ∀ i j k (W : Opens X)
      (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
      boundaryValue F U b i j k W hi hj hk = faceValue F U c i j k W hi hj hk := by
  obtain ⟨b, hb⟩ := twoCocycle_primitive_on_finset c hn hc Finset.univ
  exact ⟨b, fun i j k W hi hj hk => hb i (Finset.mem_univ i) j (Finset.mem_univ j)
    k (Finset.mem_univ k) W hi hj hk⟩

end CycleQ2FiniteInjectiveCech

#print axioms CycleQ2FiniteInjectiveCech.twoCocycle_has_primitive

namespace CycleQ2FiniteCechDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_middle_injective
  presentation_left_mono app app_res app_comp app_zero sectionExtZero)

variable {X : TopCat.{0}} {ι : Type}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G H : AbSheaf X} (U : ι → Opens X)

abbrev Zero (F : AbSheaf X) (U : ι → Opens X) := ∀ i, Sections F (U i)

def mapZero (f : F ⟶ G) (q : Zero F U) : Zero G U := fun i => app f (U i) (q i)

def mapOne (f : F ⟶ G) (b : One F U) : One G U :=
  fun i j => app f (U i ⊓ U j) (b i j)

def mapTwo (f : F ⟶ G) (c : Two F U) : Two G U :=
  fun i j k => app f ((U i ⊓ U j) ⊓ U k) (c i j k)

theorem edgeValue_mapOne (f : F ⟶ G) (b : One F U)
    (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue G U (mapOne U f b) i j W hi hj = app f W (edgeValue F U b i j W hi hj) :=
  (app_res f (le_inf hi hj) (b i j)).symm

theorem faceValue_mapTwo (f : F ⟶ G) (c : Two F U)
    (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue G U (mapTwo U f c) i j k W hi hj hk =
      app f W (faceValue F U c i j k W hi hj hk) :=
  (app_res f (le_inf (le_inf hi hj) hk) (c i j k)).symm

theorem boundaryValue_mapOne (f : F ⟶ G) (b : One F U)
    (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    boundaryValue G U (mapOne U f b) i j k W hi hj hk =
      app f W (boundaryValue F U b i j k W hi hj hk) := by
  simp only [boundaryValue, edgeValue_mapOne, map_sub, map_add]

theorem mapTwo_normalized (f : F ⟶ G) (c : Two F U) (hn : NormalizedTwo F U c) :
    NormalizedTwo G U (mapTwo U f c) where
  repeat12 i k W hi hk := by rw [faceValue_mapTwo, hn.repeat12, map_zero]
  repeat23 i j W hi hj := by rw [faceValue_mapTwo, hn.repeat23, map_zero]
  swap12 i j k W hi hj hk := by
    rw [faceValue_mapTwo, faceValue_mapTwo, hn.swap12, map_neg]
  swap23 i j k W hi hj hk := by
    rw [faceValue_mapTwo, faceValue_mapTwo, hn.swap23, map_neg]

theorem mapTwo_closed (f : F ⟶ G) (c : Two F U) (hc : IsTwoCocycle F U c) :
    IsTwoCocycle G U (mapTwo U f c) := by
  intro i j k l W hi hj hk hl
  have h := congrArg (app f W) (hc i j k l W hi hj hk hl)
  simpa only [map_sub, map_add, map_zero, faceValue_mapTwo] using h

theorem mapOne_closed (f : F ⟶ G) (c : One F U) (hc : IsOneCocycle F U c) :
    IsOneCocycle G U (mapOne U f c) := by
  intro i j k W hi hj hk
  have h := congrArg (app f W) (hc i j k W hi hj hk)
  change edgeValue G U (mapOne U f c) i k W hi hk =
    edgeValue G U (mapOne U f c) i j W hi hj + edgeValue G U (mapOne U f c) j k W hj hk
  simp only [edgeValue_mapOne]
  simpa only [map_add, edgeValue] using h

/-- The image of an actual primitive through the quotient arrow is a
one-cocycle, using the literal zero composite of the short complex. -/
theorem primitive_image_closed (S : ShortComplex (AbSheaf X))
    (c : Two S.X₁ U) (b : One S.X₂ U)
    (hb : ∀ i j k W hi hj hk,
      boundaryValue S.X₂ U b i j k W hi hj hk =
        app S.f W (faceValue S.X₁ U c i j k W hi hj hk)) :
    IsOneCocycle S.X₃ U (mapOne U S.g b) := by
  intro i j k W hi hj hk
  have h := congrArg (app S.g W) (hb i j k W hi hj hk)
  have hzero : boundaryValue S.X₃ U (mapOne U S.g b) i j k W hi hj hk = 0 := by
    rw [boundaryValue_mapOne]
    simpa only [app_comp, S.zero, app_zero] using h
  change edgeValue S.X₃ U (mapOne U S.g b) i k W hi hk =
    edgeValue S.X₃ U (mapOne U S.g b) i j W hi hj +
      edgeValue S.X₃ U (mapOne U S.g b) j k W hj hk
  dsimp only [boundaryValue] at hzero
  linear_combination (norm := abel) -hzero

def globalZero (x : Sections F ⊤) : Zero F U := fun _ => res F le_top x

theorem globalZero_exists (hcover : (⨆ i, U i) = ⊤) (q : Zero F U)
    (hq : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res F hi (q i) = res F hj (q j)) :
    ∃ x : Sections F ⊤, globalZero U x = q := by
  obtain ⟨x, hx, -⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) (by rw [hcover]) q
      (fun i j => hq i j (U i ⊓ U j) inf_le_left inf_le_right)
  exact ⟨x, funext hx⟩

theorem globalZero_injective (hcover : (⨆ i, U i) = ⊤) :
    Function.Injective (globalZero (F := F) U) := by
  intro x y hxy
  obtain ⟨t, -, ht⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) (by rw [hcover]) (globalZero U x) (by
      intro i j
      dsimp only [globalZero]
      exact (res_comp F le_top inf_le_left x).trans (res_comp F le_top inf_le_right x).symm)
  exact (ht x (fun _ => rfl)).trans (ht y (fun i => congrFun hxy.symm i)).symm

/-- Two actual injective presentations and their actual local cochains,
with the global second quotient section kept explicitly. -/
structure TwoDescent (c : Two F U) where
  first : One (presentation F).X₂ U
  first_differential : ∀ i j k W hi hj hk,
    boundaryValue (presentation F).X₂ U first i j k W hi hj hk =
      app (presentation F).f W (faceValue F U c i j k W hi hj hk)
  second : Zero (presentation (presentation F).X₃).X₂ U
  second_differential : ∀ i j W hi hj,
    res (presentation (presentation F).X₃).X₂ hj (second j) -
      res (presentation (presentation F).X₃).X₂ hi (second i) =
      app (presentation (presentation F).X₃).f W
        (app (presentation F).g W (edgeValue (presentation F).X₂ U first i j W hi hj))
  globalSection : Sections (presentation (presentation F).X₃).X₃ ⊤
  global_restriction : globalZero U globalSection =
    mapZero U (presentation (presentation F).X₃).g second

/-- Existence follows from the actual finite-family injective acyclicity and
actual sheaf gluing. No Čech-acyclicity premise is supplied by the caller. -/
theorem twoDescent_nonempty [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    Nonempty (TwoDescent U c) := by
  obtain ⟨b, hb⟩ := twoCocycle_has_primitive (mapTwo U (presentation F).f c)
    (mapTwo_normalized U _ c hn) (mapTwo_closed U _ c hc)
  have hb' : ∀ i j k W hi hj hk,
      boundaryValue (presentation F).X₂ U b i j k W hi hj hk =
        app (presentation F).f W (faceValue F U c i j k W hi hj hk) := by
    intro i j k W hi hj hk
    exact (hb i j k W hi hj hk).trans (faceValue_mapTwo U _ c i j k W hi hj hk)
  have hquot := primitive_image_closed U (presentation F) c b hb'
  obtain ⟨v, hv⟩ := oneCocycle_has_primitive
    (mapOne U (presentation (presentation F).X₃).f (mapOne U (presentation F).g b))
    (mapOne_closed U _ _ hquot)
  have hv' : ∀ i j W hi hj,
      res (presentation (presentation F).X₃).X₂ hj (v j) -
        res (presentation (presentation F).X₃).X₂ hi (v i) =
        app (presentation (presentation F).X₃).f W
          (app (presentation F).g W (edgeValue (presentation F).X₂ U b i j W hi hj)) := by
    intro i j W hi hj
    have h := hv i j W hi hj
    change _ = edgeValue _ U (mapOne U _ (mapOne U _ b)) i j W hi hj at h
    simpa only [edgeValue_mapOne] using h
  have hcompatible : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res (presentation (presentation F).X₃).X₃ hi
          (mapZero U (presentation (presentation F).X₃).g v i) =
        res (presentation (presentation F).X₃).X₃ hj
          (mapZero U (presentation (presentation F).X₃).g v j) := by
    intro i j W hi hj
    have h := congrArg (app (presentation (presentation F).X₃).g W) (hv' i j W hi hj)
    simp only [map_sub, app_comp, Category.assoc, (presentation (presentation F).X₃).zero,
      comp_zero, app_zero] at h
    dsimp only [mapZero]
    rw [← app_res, ← app_res]
    exact (sub_eq_zero.mp h).symm
  obtain ⟨t, ht⟩ := globalZero_exists U hcover _ hcompatible
  exact ⟨⟨b, hb', v, hv', t, ht⟩⟩

/-- The actual Ext class from the retained global second quotient section. -/
def descentClass {c : Two F U} (d : TwoDescent U c) : F.H' 2 ⊤ :=
  ((sectionExtZero ⊤ d.globalSection).comp
    (presentation_shortExact (presentation F).X₃).extClass rfl).comp
      (presentation_shortExact F).extClass rfl

def cechTwoClass [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) : F.H' 2 ⊤ :=
  descentClass U (Classical.choice (twoDescent_nonempty U hcover c hn hc))

end CycleQ2FiniteCechDescent

#print axioms CycleQ2FiniteCechDescent.twoDescent_nonempty
#print axioms CycleQ2FiniteCechDescent.cechTwoClass

namespace CycleQ2FiniteCechDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_middle_injective
  app app_res app_comp app_zero sectionExtZero)

variable {X : TopCat.{0}} {ι : Type}
local instance independenceSheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : ι → Opens X)

theorem edgeValue_sub (a b : One F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue F U (a-b) i j W hi hj = edgeValue F U a i j W hi hj -
      edgeValue F U b i j W hi hj := by
  simp only [edgeValue, Pi.sub_apply, map_sub]

theorem faceValue_sub (c c' : Two F U) (i j k : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue F U (c-c') i j k W hi hj hk = faceValue F U c i j k W hi hj hk -
      faceValue F U c' i j k W hi hj hk := by
  simp only [faceValue, Pi.sub_apply, map_sub]

theorem boundaryValue_sub (a b : One F U) (i j k : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    boundaryValue F U (a-b) i j k W hi hj hk =
      boundaryValue F U a i j k W hi hj hk - boundaryValue F U b i j k W hi hj hk := by
  simp only [boundaryValue, edgeValue_sub]
  abel

/-- The zero-cocycle gauge calculation works for every finite cover. It
uses actual injective primitives and uniqueness of actual sheaf gluing. -/
theorem descentClass_zero_cocycle [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (d : TwoDescent U (0 : Two F U)) : descentClass U d = 0 := by
  have hfirst : IsOneCocycle (presentation F).X₂ U d.first := by
    intro i j k W hi hj hk
    have h := d.first_differential i j k W hi hj hk
    simp only [faceValue, Pi.zero_apply, map_zero] at h
    change edgeValue (presentation F).X₂ U d.first i k W hi hk =
      edgeValue (presentation F).X₂ U d.first i j W hi hj +
        edgeValue (presentation F).X₂ U d.first j k W hj hk
    dsimp only [boundaryValue] at h
    linear_combination (norm := abel) -h
  obtain ⟨q, hq⟩ := oneCocycle_has_primitive d.first hfirst
  let v : Zero (presentation (presentation F).X₃).X₂ U := fun i =>
    d.second i - app (presentation (presentation F).X₃).f (U i)
      (app (presentation F).g (U i) (q i))
  have hv : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res (presentation (presentation F).X₃).X₂ hi (v i) =
        res (presentation (presentation F).X₃).X₂ hj (v j) := by
    intro i j W hi hj
    have hd := d.second_differential i j W hi hj
    have hq' := congrArg (fun x => app (presentation (presentation F).X₃).f W
        (app (presentation F).g W x)) (hq i j W hi hj)
    simp only [map_sub] at hq'
    dsimp only [v]
    rw [map_sub, map_sub, ← app_res, ← app_res, ← app_res, ← app_res]
    change _ = app (presentation (presentation F).X₃).f W
      (app (presentation F).g W (edgeValue (presentation F).X₂ U d.first i j W hi hj)) at hq'
    linear_combination (norm := abel) hq' - hd
  obtain ⟨g, hg⟩ := globalZero_exists U hcover v hv
  have hglobal : app (presentation (presentation F).X₃).g ⊤ g = d.globalSection := by
    apply globalZero_injective U hcover
    funext i
    change res _ le_top (app _ ⊤ g) = res _ le_top d.globalSection
    rw [← app_res]
    change app _ (U i) (globalZero U g i) = globalZero U d.globalSection i
    rw [hg]
    dsimp only [v]
    rw [map_sub, app_comp, (presentation (presentation F).X₃).zero, app_zero, sub_zero]
    exact (congrFun d.global_restriction i).symm
  have hδ : (sectionExtZero ⊤ d.globalSection).comp
      (presentation_shortExact (presentation F).X₃).extClass rfl = 0 := by
    rw [← hglobal, CycleQ2CechTwoComparison.sectionExtZero_app,
      Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
  simp only [descentClass, hδ, Ext.zero_comp]

/-- Difference of the literal descent data; every displayed cochain and
the retained global section is subtracted pointwise. -/
def subtractDescents {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    TwoDescent U (c-c') where
  first := d.first-e.first
  first_differential i j k W hi hj hk := by
    rw [boundaryValue_sub, d.first_differential, e.first_differential, faceValue_sub, map_sub]
  second := d.second-e.second
  second_differential i j W hi hj := by
    change res _ hj (d.second j-e.second j) - res _ hi (d.second i-e.second i) = _
    rw [map_sub, map_sub, edgeValue_sub, map_sub, map_sub]
    linear_combination (norm := abel)
      d.second_differential i j W hi hj - e.second_differential i j W hi hj
  globalSection := d.globalSection-e.globalSection
  global_restriction := by
    funext i
    change res _ le_top (d.globalSection-e.globalSection) = app _ (U i) (d.second i-e.second i)
    rw [map_sub, map_sub]
    exact congrArg₂ (fun a b => a-b) (congrFun d.global_restriction i)
      (congrFun e.global_restriction i)

theorem descentClass_sub {c c' : Two F U} (d : TwoDescent U c) (e : TwoDescent U c') :
    descentClass U (subtractDescents U d e) = descentClass U d - descentClass U e := by
  change ((sectionExtZero ⊤ (d.globalSection-e.globalSection)).comp
      (presentation_shortExact (presentation F).X₃).extClass rfl).comp
        (presentation_shortExact F).extClass rfl = _
  rw [CycleQ2CechTwoComparison.sectionExtZero_sub]
  simp only [descentClass, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]

theorem descentClass_zero_of_underlying_zero [Fintype ι]
    (hcover : (⨆ i, U i) = ⊤) {c : Two F U} (d : TwoDescent U c) (hc : c = 0) :
    descentClass U d = 0 := by
  subst c
  exact descentClass_zero_cocycle U hcover d

/-- No choices of local injective primitives or global gluing affect the
actual derived class, on any finite cover. -/
theorem descentClass_independent [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    {c : Two F U} (d e : TwoDescent U c) : descentClass U d = descentClass U e := by
  have h := descentClass_zero_of_underlying_zero U hcover
    (subtractDescents U d e) (sub_self c)
  rw [descentClass_sub] at h
  exact sub_eq_zero.mp h

theorem cechTwoClass_eq_descentClass [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c)
    (d : TwoDescent U c) : cechTwoClass U hcover c hn hc = descentClass U d :=
  descentClass_independent U hcover
    (Classical.choice (twoDescent_nonempty U hcover c hn hc)) d

end CycleQ2FiniteCechDescent

#print axioms CycleQ2FiniteCechDescent.descentClass_independent

namespace CycleQ2FiniteCechDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_left_mono
  app app_res app_comp app_zero app_injective sectionExtZero)

variable {X : TopCat.{0}} {ι : Type}
local instance boundarySheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : ι → Opens X)

/-- An actual degree-one primitive implies the alternating four-face identity
after restriction to every common open. -/
theorem primitive_closed (c : Two F U) (b : One F U)
    (hb : ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
      faceValue F U c i j k W hi hj hk) : IsTwoCocycle F U c := by
  intro i j k l W hi hj hk hl
  rw [← hb j k l W hj hk hl, ← hb i k l W hi hk hl,
    ← hb i j l W hi hj hl, ← hb i j k W hi hj hk]
  dsimp only [boundaryValue]
  abel

/-- The first actual injective primitive forces the underlying cocycle to
be closed, using pointwise injectivity of the presentation monomorphism. -/
theorem TwoDescent.closed {c : Two F U} (d : TwoDescent U c) : IsTwoCocycle F U c := by
  have hclosed := primitive_closed U (mapTwo U (presentation F).f c) d.first (by
    intro i j k W hi hj hk
    rw [faceValue_mapTwo]
    exact d.first_differential i j k W hi hj hk)
  intro i j k l W hi hj hk hl
  apply app_injective (presentation F).f W
  simpa only [map_sub, map_add, map_zero, faceValue_mapTwo] using
    hclosed i j k l W hi hj hk hl

/-- A genuine boundary has the tautological two-stage descent: apply the
first presentation map to its edge primitive and use zero thereafter. -/
def boundaryDescent {c : Two F U} (b : One F U)
    (hb : ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
      faceValue F U c i j k W hi hj hk) : TwoDescent U c where
  first := mapOne U (presentation F).f b
  first_differential i j k W hi hj hk := by
    rw [boundaryValue_mapOne, hb i j k W hi hj hk]
  second := 0
  second_differential i j W hi hj := by
    simp only [Pi.zero_apply, map_zero, sub_zero, edgeValue_mapOne, app_comp,
      (presentation F).zero, app_zero]
  globalSection := 0
  global_restriction := by
    funext i
    simp only [globalZero, mapZero, Pi.zero_apply, map_zero]

theorem boundaryDescent_class {c : Two F U} (b : One F U)
    (hb : ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
      faceValue F U c i j k W hi hj hk) :
    descentClass U (boundaryDescent U b hb) = 0 := by
  change ((sectionExtZero ⊤ (0 : Sections (presentation (presentation F).X₃).X₃ ⊤)).comp
      (presentation_shortExact (presentation F).X₃).extClass rfl).comp
        (presentation_shortExact F).extClass rfl = 0
  simp only [sectionExtZero, map_zero, Ext.mk₀_zero, Ext.zero_comp]

theorem descentClass_eq_zero_of_boundary [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    {c : Two F U} (d : TwoDescent U c) (b : One F U)
    (hb : ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
      faceValue F U c i j k W hi hj hk) : descentClass U d = 0 :=
  (descentClass_independent U hcover d (boundaryDescent U b hb)).trans
    (boundaryDescent_class U b hb)

/-- Two actual finite-cover cocycles with an actual edge primitive for their
difference represent the same derived class. -/
theorem cechTwoClass_eq_of_difference_boundary [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c c' : Two F U) (hn : NormalizedTwo F U c) (hn' : NormalizedTwo F U c')
    (hc : IsTwoCocycle F U c) (hc' : IsTwoCocycle F U c') (b : One F U)
    (hb : ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
      faceValue F U (c-c') i j k W hi hj hk) :
    cechTwoClass U hcover c hn hc = cechTwoClass U hcover c' hn' hc' := by
  let d := Classical.choice (twoDescent_nonempty U hcover c hn hc)
  let d' := Classical.choice (twoDescent_nonempty U hcover c' hn' hc')
  have hz := descentClass_eq_zero_of_boundary U hcover (subtractDescents U d d') b hb
  rw [descentClass_sub] at hz
  exact sub_eq_zero.mp hz

end CycleQ2FiniteCechDescent

#print axioms CycleQ2FiniteCechDescent.cechTwoClass_eq_of_difference_boundary

namespace CycleQ2FiniteCechRefinement

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent
open CycleQ2CechTwoToDerived (presentation app app_res)

variable {X : TopCat.{0}} {ι κ : Type}
local instance refinementSheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : ι → Opens X) (V : κ → Opens X)
  (ρ : κ → ι) (h : ∀ j, V j ≤ U (ρ j))

/-- The actual restrictions of sections along an arbitrary index map of covers. -/
def restrictZero (q : Zero F U) : Zero F V :=
  fun j => res F (h j) (q (ρ j))

def restrictOne (b : One F U) : One F V := fun j k =>
  res F (inf_le_inf (h j) (h k)) (b (ρ j) (ρ k))

def restrictTwo (c : Two F U) : Two F V := fun i j k =>
  res F (inf_le_inf (inf_le_inf (h i) (h j)) (h k)) (c (ρ i) (ρ j) (ρ k))

theorem edgeValue_restrictOne (b : One F U) (i j : κ) (W : Opens X)
    (hi : W ≤ V i) (hj : W ≤ V j) :
    edgeValue F V (restrictOne U V ρ h b) i j W hi hj =
      edgeValue F U b (ρ i) (ρ j) W (hi.trans (h i)) (hj.trans (h j)) :=
  res_comp F _ _ _

theorem faceValue_restrictTwo (c : Two F U) (i j k : κ) (W : Opens X)
    (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k) :
    faceValue F V (restrictTwo U V ρ h c) i j k W hi hj hk =
      faceValue F U c (ρ i) (ρ j) (ρ k) W
        (hi.trans (h i)) (hj.trans (h j)) (hk.trans (h k)) :=
  res_comp F _ _ _

theorem boundaryValue_restrictOne (b : One F U) (i j k : κ) (W : Opens X)
    (hi : W ≤ V i) (hj : W ≤ V j) (hk : W ≤ V k) :
    boundaryValue F V (restrictOne U V ρ h b) i j k W hi hj hk =
      boundaryValue F U b (ρ i) (ρ j) (ρ k) W
        (hi.trans (h i)) (hj.trans (h j)) (hk.trans (h k)) := by
  simp only [boundaryValue, edgeValue_restrictOne]

theorem restrictTwo_normalized (c : Two F U) (hn : NormalizedTwo F U c) :
    NormalizedTwo F V (restrictTwo U V ρ h c) where
  repeat12 i k W hi hk := by
    rw [faceValue_restrictTwo U V ρ h c i i k W hi hi hk]
    exact hn.repeat12 _ _ _ _ _
  repeat23 i j W hi hi' := by
    rw [faceValue_restrictTwo U V ρ h c i j j W hi hi' hi']
    exact hn.repeat23 _ _ _ _ _
  swap12 i j k W hi hj hk := by
    rw [faceValue_restrictTwo U V ρ h c i j k W hi hj hk,
      faceValue_restrictTwo U V ρ h c j i k W hj hi hk]
    exact hn.swap12 _ _ _ _ _ _ _
  swap23 i j k W hi hj hk := by
    rw [faceValue_restrictTwo U V ρ h c i j k W hi hj hk,
      faceValue_restrictTwo U V ρ h c i k j W hi hk hj]
    exact hn.swap23 _ _ _ _ _ _ _

theorem restrictTwo_closed (c : Two F U) (hc : IsTwoCocycle F U c) :
    IsTwoCocycle F V (restrictTwo U V ρ h c) := by
  intro i j k l W hi hj hk hl
  simp only [faceValue_restrictTwo]
  exact hc (ρ i) (ρ j) (ρ k) (ρ l) W
    (hi.trans (h i)) (hj.trans (h j)) (hk.trans (h k)) (hl.trans (h l))

/-- Both local injective primitives are restricted, while the actual global
second-quotient section and both injective presentations are retained. -/
def restrictDescent {c : Two F U} (d : TwoDescent U c) :
    TwoDescent V (restrictTwo U V ρ h c) where
  first := restrictOne U V ρ h d.first
  first_differential i j k W hi hj hk := by
    rw [boundaryValue_restrictOne, faceValue_restrictTwo]
    exact d.first_differential (ρ i) (ρ j) (ρ k) W
      (hi.trans (h i)) (hj.trans (h j)) (hk.trans (h k))
  second := restrictZero U V ρ h d.second
  second_differential i j W hi hj := by
    dsimp only [restrictZero]
    rw [res_comp, res_comp, edgeValue_restrictOne]
    exact d.second_differential (ρ i) (ρ j) W
      (hi.trans (h i)) (hj.trans (h j))
  globalSection := d.globalSection
  global_restriction := by
    funext j
    have hd := congrArg (res (presentation (presentation F).X₃).X₃ (h j))
      (congrFun d.global_restriction (ρ j))
    dsimp only [globalZero, mapZero] at hd ⊢
    rw [res_comp, ← app_res] at hd
    exact hd

theorem descentClass_restriction {c : Two F U} (d : TwoDescent U c) :
    descentClass V (restrictDescent U V ρ h d) = descentClass U d := rfl

/-- Refinement preserves the actual derived degree-two class. The index map
may repeat indices, and the finite covers may have different cardinalities. -/
theorem cechTwoClass_refinement [Fintype ι] [Fintype κ]
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    cechTwoClass V hV (restrictTwo U V ρ h c)
        (restrictTwo_normalized U V ρ h c hn) (restrictTwo_closed U V ρ h c hc) =
      cechTwoClass U hU c hn hc := by
  let d := Classical.choice (twoDescent_nonempty U hU c hn hc)
  rw [cechTwoClass_eq_descentClass V hV _ _ _ (restrictDescent U V ρ h d),
    descentClass_restriction]
  exact (cechTwoClass_eq_descentClass U hU c hn hc d).symm

/-- The genuine common refinement of two families of opens. -/
def commonRefinement : ι × κ → Opens X := fun ij => U ij.1 ⊓ V ij.2

theorem commonRefinement_cover (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    (⨆ ij, commonRefinement U V ij) = ⊤ := by
  apply top_unique
  intro x hx
  have hxU : x ∈ (⨆ i, U i) := by rw [hU]; trivial
  have hxV : x ∈ (⨆ j, V j) := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
  exact Opens.mem_iSup.mpr ⟨(i,j), hi, hj⟩

theorem cechTwoClass_commonRefinement_left [Fintype ι] [Fintype κ]
    (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    cechTwoClass (commonRefinement U V) (commonRefinement_cover U V hU hV)
        (restrictTwo U (commonRefinement U V) Prod.fst (fun _ => inf_le_left) c)
        (restrictTwo_normalized U (commonRefinement U V) Prod.fst
          (fun _ => inf_le_left) c hn)
        (restrictTwo_closed U (commonRefinement U V) Prod.fst
          (fun _ => inf_le_left) c hc) = cechTwoClass U hU c hn hc :=
  cechTwoClass_refinement U (commonRefinement U V) Prod.fst
    (fun _ => inf_le_left) hU (commonRefinement_cover U V hU hV) c hn hc

end CycleQ2FiniteCechRefinement

#print axioms CycleQ2FiniteCechRefinement.cechTwoClass_refinement
#print axioms CycleQ2FiniteCechRefinement.cechTwoClass_commonRefinement_left

namespace CycleQ2FourToFiniteCech

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent
open CycleQ2CechTwoToDerived (presentation presentation_left_mono app app_res app_injective)

variable {X : TopCat.{0}}
local instance fourFiniteSheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (U : Fin 4 → Opens X)

/-- A data eliminator, so the section-valued definitions do not eliminate
finite-membership propositions into arbitrary types. -/
def fourCases {P : Fin 4 → Sort _} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i, P i := Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i))))

theorem fourCases_zero {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 0 < 4) :
    fourCases h0 h1 h2 h3 ⟨0,h⟩ = h0 := rfl

theorem fourCases_one {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 1 < 4) :
    fourCases h0 h1 h2 h3 ⟨1,h⟩ = h1 := rfl

theorem fourCases_two {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 2 < 4) :
    fourCases h0 h1 h2 h3 ⟨2,h⟩ = h2 := rfl

theorem fourCases_three {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 3 < 4) :
    fourCases h0 h1 h2 h3 ⟨3,h⟩ = h3 := rfl


/-- The original six ordered edges, restricted to a common open and extended
with their alternating signs. Repeated vertices give the zero section. -/
def edgeAt (b : CycleQ2CechTwoToDerived.One F U) (i j : Fin 4) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) : Sections F W := by
  revert hi hj
  refine fourCases (P := fun i => W ≤ U i → W ≤ U j → Sections F W) ?_ ?_ ?_ ?_ i <;> intro hi
  all_goals refine fourCases (P := fun j => W ≤ U j → Sections F W) ?_ ?_ ?_ ?_ j <;> intro hj
  · exact 0
  · exact res F (le_inf hi hj) b.1
  · exact res F (le_inf hi hj) b.2.1
  · exact res F (le_inf hi hj) b.2.2.1
  · exact -(res F (le_inf hj hi) b.1)
  · exact 0
  · exact res F (le_inf hi hj) b.2.2.2.1
  · exact res F (le_inf hi hj) b.2.2.2.2.1
  · exact -(res F (le_inf hj hi) b.2.1)
  · exact -(res F (le_inf hj hi) b.2.2.2.1)
  · exact 0
  · exact res F (le_inf hi hj) b.2.2.2.2.2
  · exact -(res F (le_inf hj hi) b.2.2.1)
  · exact -(res F (le_inf hj hi) b.2.2.2.2.1)
  · exact -(res F (le_inf hj hi) b.2.2.2.2.2)
  · exact 0

/-- The original four ordered faces, with actual restrictions and the usual
alternating signs on every ordered triple. -/
def faceAt (c : CycleQ2CechTwoToDerived.Two F U) (i j k : Fin 4) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) : Sections F W := by
  revert hi hj hk
  refine fourCases (P := fun i => W ≤ U i → W ≤ U j → W ≤ U k → Sections F W) ?_ ?_ ?_ ?_ i <;> intro hi
  all_goals refine fourCases (P := fun j => W ≤ U j → W ≤ U k → Sections F W) ?_ ?_ ?_ ?_ j <;> intro hj
  all_goals refine fourCases (P := fun k => W ≤ U k → Sections F W) ?_ ?_ ?_ ?_ k <;> intro hk
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hi hj) hk) c.1
  · exact res F (le_inf (le_inf hi hj) hk) c.2.1
  · exact 0
  · exact -(res F (le_inf (le_inf hi hk) hj) c.1)
  · exact 0
  · exact res F (le_inf (le_inf hi hj) hk) c.2.2.1
  · exact 0
  · exact -(res F (le_inf (le_inf hi hk) hj) c.2.1)
  · exact -(res F (le_inf (le_inf hi hk) hj) c.2.2.1)
  · exact 0
  · exact 0
  · exact 0
  · exact -(res F (le_inf (le_inf hj hi) hk) c.1)
  · exact -(res F (le_inf (le_inf hj hi) hk) c.2.1)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hk hi) hj) c.1
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hi hj) hk) c.2.2.2
  · exact res F (le_inf (le_inf hk hi) hj) c.2.1
  · exact 0
  · exact -(res F (le_inf (le_inf hi hk) hj) c.2.2.2)
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hj hk) hi) c.1
  · exact 0
  · exact -(res F (le_inf (le_inf hj hi) hk) c.2.2.1)
  · exact -(res F (le_inf (le_inf hk hj) hi) c.1)
  · exact 0
  · exact 0
  · exact -(res F (le_inf (le_inf hj hi) hk) c.2.2.2)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hk hi) hj) c.2.2.1
  · exact res F (le_inf (le_inf hk hi) hj) c.2.2.2
  · exact 0
  · exact 0
  · exact 0
  · exact res F (le_inf (le_inf hj hk) hi) c.2.1
  · exact res F (le_inf (le_inf hj hk) hi) c.2.2.1
  · exact 0
  · exact -(res F (le_inf (le_inf hk hj) hi) c.2.1)
  · exact 0
  · exact res F (le_inf (le_inf hj hk) hi) c.2.2.2
  · exact 0
  · exact -(res F (le_inf (le_inf hk hj) hi) c.2.2.1)
  · exact -(res F (le_inf (le_inf hk hj) hi) c.2.2.2)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0

theorem res_edgeAt (b : CycleQ2CechTwoToDerived.One F U) (i j : Fin 4)
    (W W' : Opens X) (h : W' ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) :
    res F h (edgeAt U b i j W hi hj) =
      edgeAt U b i j W' (h.trans hi) (h.trans hj) := by
  fin_cases i <;> fin_cases j <;>
    simp only [edgeAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, map_zero, map_neg, res_comp]

theorem res_faceAt (c : CycleQ2CechTwoToDerived.Two F U) (i j k : Fin 4)
    (W W' : Opens X) (h : W' ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    res F h (faceAt U c i j k W hi hj hk) =
      faceAt U c i j k W' (h.trans hi) (h.trans hj) (h.trans hk) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, map_zero, map_neg, res_comp]

def extendOne (b : CycleQ2CechTwoToDerived.One F U) : One F U :=
  fun i j => edgeAt U b i j (U i ⊓ U j) inf_le_left inf_le_right

def extendTwo (c : CycleQ2CechTwoToDerived.Two F U) : Two F U :=
  fun i j k => faceAt U c i j k ((U i ⊓ U j) ⊓ U k)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

theorem edgeValue_extendOne (b : CycleQ2CechTwoToDerived.One F U)
    (i j : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue F U (extendOne U b) i j W hi hj = edgeAt U b i j W hi hj :=
  res_edgeAt U b i j _ W (le_inf hi hj) _ _

theorem faceValue_extendTwo (c : CycleQ2CechTwoToDerived.Two F U)
    (i j k : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceValue F U (extendTwo U c) i j k W hi hj hk = faceAt U c i j k W hi hj hk :=
  res_faceAt U c i j k _ W (le_inf (le_inf hi hj) hk) _ _ _

theorem edgeAt_mapOne (f : F ⟶ G) (b : CycleQ2CechTwoToDerived.One F U)
    (i j : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeAt U (CycleQ2CechTwoToDerived.mapOne U f b) i j W hi hj =
      app f W (edgeAt U b i j W hi hj) := by
  fin_cases i <;> fin_cases j <;>
    simp only [edgeAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, CycleQ2CechTwoToDerived.mapOne, app_res, map_neg, map_zero]

theorem faceAt_mapTwo (f : F ⟶ G) (c : CycleQ2CechTwoToDerived.Two F U)
    (i j k : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceAt U (CycleQ2CechTwoToDerived.mapTwo U f c) i j k W hi hj hk =
      app f W (faceAt U c i j k W hi hj hk) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, CycleQ2CechTwoToDerived.mapTwo, app_res, map_neg, map_zero]

theorem edgeAt_d0 (q : CycleQ2CechTwoToDerived.Zero F U)
    (i j : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeAt U (CycleQ2CechTwoToDerived.d0 F U q) i j W hi hj =
      res F hj (q j) - res F hi (q i) := by
  fin_cases i <;> fin_cases j
  all_goals simp only [edgeAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three]
  all_goals simp only [CycleQ2CechTwoToDerived.d0, map_sub, res_comp, sub_self]
  all_goals first | rfl | exact neg_sub (α := Sections F W) _ _

set_option maxHeartbeats 600000 in
theorem boundaryValue_extendOne (b : CycleQ2CechTwoToDerived.One F U)
    (i j k : Fin 4) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    boundaryValue F U (extendOne U b) i j k W hi hj hk =
      faceAt U (CycleQ2CechTwoToDerived.d1 F U b) i j k W hi hj hk := by
  simp only [boundaryValue, edgeValue_extendOne]
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp only [faceAt, edgeAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three]
  all_goals simp only [CycleQ2CechTwoToDerived.d1, map_add, map_sub,
    res_comp, sub_self, sub_zero, zero_sub, add_zero, neg_neg,
    neg_add_cancel, add_neg_cancel]
  all_goals abel

set_option maxHeartbeats 600000 in
theorem extendTwo_normalized (c : CycleQ2CechTwoToDerived.Two F U) :
    NormalizedTwo F U (extendTwo U c) where
  repeat12 i k W hi hk := by
    rw [faceValue_extendTwo]
    fin_cases i <;> fin_cases k <;> rfl
  repeat23 i j W hi hj := by
    rw [faceValue_extendTwo]
    fin_cases i <;> fin_cases j <;> rfl
  swap12 i j k W hi hj hk := by
    simp only [faceValue_extendTwo]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, neg_zero, neg_neg]
  swap23 i j k W hi hj hk := by
    simp only [faceValue_extendTwo]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, neg_zero, neg_neg]

/-- The original four-open descent data give finite-family descent data
with exactly the same two presentations and global quotient section. -/
def extendDescent {c : CycleQ2CechTwoToDerived.Two F U}
    (d : CycleQ2CechTwoToDerived.TwoDescent U c) : TwoDescent U (extendTwo U c) where
  first := extendOne U d.first
  first_differential i j k W hi hj hk := by
    rw [boundaryValue_extendOne, d.first_differential, faceAt_mapTwo, faceValue_extendTwo]
  second := d.second
  second_differential i j W hi hj := by
    have h := congrArg (fun b => edgeAt
      (F := (presentation (presentation F).X₃).X₂) U b i j W hi hj) d.second_differential
    rw [edgeAt_d0, edgeAt_mapOne, edgeAt_mapOne] at h
    rw [edgeValue_extendOne]
    exact h
  globalSection := d.globalSection
  global_restriction := d.global_restriction


/-- Closedness follows from the original actual injective descent and its
presentation monomorphism, without a separate acyclicity assumption. -/
theorem extendTwo_closed (hcover : (⨆ i, U i) = ⊤)
    (c : CycleQ2CechTwoToDerived.Two F U)
    (hc : CycleQ2CechTwoToDerived.d2 F U c = 0) : IsTwoCocycle F U (extendTwo U c) :=
  TwoDescent.closed U (extendDescent U
    (Classical.choice (CycleQ2CechTwoToDerived.twoDescent_nonempty U hcover c hc)))

/-- The finite-family construction represents precisely the already checked
four-open derived class, using the same global quotient section. -/
theorem finiteClass_eq_fourClass (hcover : (⨆ i, U i) = ⊤)
    (c : CycleQ2CechTwoToDerived.Two F U)
    (hc : CycleQ2CechTwoToDerived.d2 F U c = 0) :
    cechTwoClass U hcover (extendTwo U c) (extendTwo_normalized U c)
        (extendTwo_closed U hcover c hc) =
      CycleQ2CechTwoToDerived.cechTwoClass U hcover c hc := by
  let d := Classical.choice (CycleQ2CechTwoToDerived.twoDescent_nonempty U hcover c hc)
  rw [cechTwoClass_eq_descentClass U hcover _ _ _ (extendDescent U d)]
  change CycleQ2CechTwoToDerived.descentClass U d = _
  exact (CycleQ2CechTwoComparison.cechTwoClass_eq_descentClass U hcover c hc d).symm

end CycleQ2FourToFiniteCech

#print axioms CycleQ2FourToFiniteCech.extendDescent

#print axioms CycleQ2FourToFiniteCech.finiteClass_eq_fourClass

namespace CycleQ2LiteralCechRefinement

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open AlgebraicGeometry
open CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
open CycleQ2FiniteCechRefinement CycleQ2FourToFiniteCech
open CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIntersections
open CycleQ2ProjectiveCartierDerived

local instance literalRefinementHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original literal four projective Cartier faces, extended with their
actual alternating signs to all ordered triples. -/
def literalFiniteCocycle : Two (additiveSheaf 57 1) (coverFamily 57 1) :=
  extendTwo (coverFamily 57 1) literalCocycle

theorem literalFiniteCocycle_normalized :
    NormalizedTwo (additiveSheaf 57 1) (coverFamily 57 1) literalFiniteCocycle :=
  extendTwo_normalized (coverFamily 57 1) literalCocycle

theorem literalFiniteCocycle_closed :
    IsTwoCocycle (additiveSheaf 57 1) (coverFamily 57 1) literalFiniteCocycle :=
  extendTwo_closed (coverFamily 57 1) literal_cover literalCocycle literalCocycle_closed

theorem literalFiniteClass_eq :
    cechTwoClass (coverFamily 57 1) literal_cover literalFiniteCocycle
        literalFiniteCocycle_normalized literalFiniteCocycle_closed = literalDerivedClassAtTop :=
  finiteClass_eq_fourClass (coverFamily 57 1) literal_cover literalCocycle literalCocycle_closed

variable {κ : Type} [Fintype κ]
  (V : κ → Opens (projectiveSurface 57 1)) (hV : (⨆ j, V j) = ⊤)

/-- The actual derived class of the literal Cartier cocycle restricted to
the genuine common refinement with any finite cover of the same surface. -/
def literalCommonRefinementClass : (additiveSheaf 57 1).H' 2 ⊤ :=
  cechTwoClass (commonRefinement (coverFamily 57 1) V)
    (commonRefinement_cover (coverFamily 57 1) V literal_cover hV)
    (restrictTwo (coverFamily 57 1) (commonRefinement (coverFamily 57 1) V)
      Prod.fst (fun _ => inf_le_left) literalFiniteCocycle)
    (restrictTwo_normalized (coverFamily 57 1) (commonRefinement (coverFamily 57 1) V)
      Prod.fst (fun _ => inf_le_left) literalFiniteCocycle literalFiniteCocycle_normalized)
    (restrictTwo_closed (coverFamily 57 1) (commonRefinement (coverFamily 57 1) V)
      Prod.fst (fun _ => inf_le_left) literalFiniteCocycle literalFiniteCocycle_closed)

/-- In particular, a four-open second cover gives sixteen actual common
opens, and this class remains exactly the original literal derived class. -/
theorem literalCommonRefinementClass_eq :
    literalCommonRefinementClass V hV = literalDerivedClassAtTop := by
  unfold literalCommonRefinementClass
  exact (cechTwoClass_commonRefinement_left (coverFamily 57 1) V literal_cover hV
    literalFiniteCocycle literalFiniteCocycle_normalized literalFiniteCocycle_closed).trans
      literalFiniteClass_eq

theorem literalCommonRefinementClass_ne_zero : literalCommonRefinementClass V hV ≠ 0 := by
  rw [literalCommonRefinementClass_eq V hV]
  exact literalDerivedClassAtTop_ne_zero

end CycleQ2LiteralCechRefinement

#print axioms CycleQ2LiteralCechRefinement.literalCommonRefinementClass_ne_zero


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2CechStaircaseSign
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]

private theorem singletonSubset {s : Finset (Fin 4)} {i : Fin 4} (hi : i ∈ s) :
    {i} ⊆ s := Finset.singleton_subset_iff.mpr hi
private theorem pairSubset {s : Finset (Fin 4)} {i j : Fin 4}
    (hi : i ∈ s) (hj : j ∈ s) : {i,j} ⊆ s := by
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj
private theorem tripleSubset {s : Finset (Fin 4)} {i j k : Fin 4}
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) : {i,j,k} ⊆ s := by
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj hk)

/-- A data eliminator, so the section-valued definitions do not eliminate
finite-membership propositions into arbitrary types. -/
def fourCases {P : Fin 4 → Sort _} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i, P i := Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i))))

theorem fourCases_zero {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 0 < 4) :
    fourCases h0 h1 h2 h3 ⟨0,h⟩ = h0 := rfl

theorem fourCases_one {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 1 < 4) :
    fourCases h0 h1 h2 h3 ⟨1,h⟩ = h1 := rfl

theorem fourCases_two {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 2 < 4) :
    fourCases h0 h1 h2 h3 ⟨2,h⟩ = h2 := rfl

theorem fourCases_three {P : Fin 4 → Sort _}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h : 3 < 4) :
    fourCases h0 h1 h2 h3 ⟨3,h⟩ = h3 := rfl


/-- Restrict a vertex component to an actual larger intersection. -/
def evalZero (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i : Fin 4) (hi : i ∈ s) (q : ZeroCochain V) : V s := by
  revert hi
  refine fourCases (P := fun i => i ∈ s → V s) ?_ ?_ ?_ ?_ i <;> intro hi
  · exact D.res (singletonSubset hi) q.1.1
  · exact D.res (singletonSubset hi) q.1.2
  · exact D.res (singletonSubset hi) q.2.1
  · exact D.res (singletonSubset hi) q.2.2

/-- Restrict an edge with its actual alternating orientation. -/
def evalOne (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (q : OneCochain V) : V s := by
  revert hi hj
  refine fourCases (P := fun i => i ∈ s → j ∈ s → V s) ?_ ?_ ?_ ?_ i <;> intro hi
  all_goals refine fourCases (P := fun j => j ∈ s → V s) ?_ ?_ ?_ ?_ j <;> intro hj
  · exact 0
  · exact D.res (pairSubset hi hj) q.1.1
  · exact D.res (pairSubset hi hj) q.1.2.1
  · exact D.res (pairSubset hi hj) q.1.2.2
  · exact -(D.res (pairSubset hj hi) q.1.1)
  · exact 0
  · exact D.res (pairSubset hi hj) q.2.1
  · exact D.res (pairSubset hi hj) q.2.2.1
  · exact -(D.res (pairSubset hj hi) q.1.2.1)
  · exact -(D.res (pairSubset hj hi) q.2.1)
  · exact 0
  · exact D.res (pairSubset hi hj) q.2.2.2
  · exact -(D.res (pairSubset hj hi) q.1.2.2)
  · exact -(D.res (pairSubset hj hi) q.2.2.1)
  · exact -(D.res (pairSubset hj hi) q.2.2.2)
  · exact 0

/-- Restrict a face with its actual alternating orientation. -/
def evalTwo (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
    (q : TwoCochain V) : V s := by
  revert hi hj hk
  refine fourCases (P := fun i => i ∈ s → j ∈ s → k ∈ s → V s) ?_ ?_ ?_ ?_ i <;> intro hi
  all_goals refine fourCases (P := fun j => j ∈ s → k ∈ s → V s) ?_ ?_ ?_ ?_ j <;> intro hj
  all_goals refine fourCases (P := fun k => k ∈ s → V s) ?_ ?_ ?_ ?_ k <;> intro hk
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hi hj hk) q.1.1
  · exact D.res (tripleSubset hi hj hk) q.1.2
  · exact 0
  · exact -(D.res (tripleSubset hi hk hj) q.1.1)
  · exact 0
  · exact D.res (tripleSubset hi hj hk) q.2.1
  · exact 0
  · exact -(D.res (tripleSubset hi hk hj) q.1.2)
  · exact -(D.res (tripleSubset hi hk hj) q.2.1)
  · exact 0
  · exact 0
  · exact 0
  · exact -(D.res (tripleSubset hj hi hk) q.1.1)
  · exact -(D.res (tripleSubset hj hi hk) q.1.2)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hk hi hj) q.1.1
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hi hj hk) q.2.2
  · exact D.res (tripleSubset hk hi hj) q.1.2
  · exact 0
  · exact -(D.res (tripleSubset hi hk hj) q.2.2)
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hj hk hi) q.1.1
  · exact 0
  · exact -(D.res (tripleSubset hj hi hk) q.2.1)
  · exact -(D.res (tripleSubset hk hj hi) q.1.1)
  · exact 0
  · exact 0
  · exact -(D.res (tripleSubset hj hi hk) q.2.2)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hk hi hj) q.2.1
  · exact D.res (tripleSubset hk hi hj) q.2.2
  · exact 0
  · exact 0
  · exact 0
  · exact D.res (tripleSubset hj hk hi) q.1.2
  · exact D.res (tripleSubset hj hk hi) q.2.1
  · exact 0
  · exact -(D.res (tripleSubset hk hj hi) q.1.2)
  · exact 0
  · exact D.res (tripleSubset hj hk hi) q.2.2
  · exact 0
  · exact -(D.res (tripleSubset hk hj hi) q.2.1)
  · exact -(D.res (tripleSubset hk hj hi) q.2.2)
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0

theorem evalZero_add (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i : Fin 4) (hi : i ∈ s) (q q' : ZeroCochain V) :
    evalZero D s i hi (q+q') = evalZero D s i hi q + evalZero D s i hi q' := by
  fin_cases i <;> simp only [evalZero, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, Prod.fst_add, Prod.snd_add, map_add]

theorem evalZero_sub (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i : Fin 4) (hi : i ∈ s) (q q' : ZeroCochain V) :
    evalZero D s i hi (q-q') = evalZero D s i hi q - evalZero D s i hi q' := by
  fin_cases i <;> simp only [evalZero, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, Prod.fst_sub, Prod.snd_sub, map_sub]

theorem evalOne_sub (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (q q' : OneCochain V) :
    evalOne D s i j hi hj (q-q') = evalOne D s i j hi hj q - evalOne D s i j hi hj q' := by
  fin_cases i <;> fin_cases j <;>
    simp only [evalOne, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, Prod.fst_sub, Prod.snd_sub, map_sub] <;> abel

theorem evalZero_augmentation (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i : Fin 4) (hi : i ∈ s) (q : V ∅) :
    evalZero D s i hi (augmentation D q) = D.res (Finset.empty_subset s) q := by
  fin_cases i <;> simp only [evalZero, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, augmentation, LinearMap.coe_mk, AddHom.coe_mk,
    RestrictionSystem.res_res]

theorem evalOne_d0 (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (q : ZeroCochain V) :
    evalOne D s i j hi hj (d0 D q) = evalZero D s j hj q - evalZero D s i hi q := by
  fin_cases i <;> fin_cases j <;>
    simp only [evalOne, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, evalZero, d0, LinearMap.coe_mk, AddHom.coe_mk,
      map_sub, RestrictionSystem.res_res] <;> abel

set_option maxHeartbeats 600000 in
theorem evalTwo_d1 (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (q : OneCochain V) :
    evalTwo D s i j k hi hj hk (d1 D q) =
      evalOne D s j k hj hk q - evalOne D s i k hi hk q + evalOne D s i j hi hj q := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [evalTwo, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, evalOne, d1, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_sub, RestrictionSystem.res_res] <;> abel

theorem evalZero_map0 {D : RestrictionSystem R V} {E : RestrictionSystem R W}
    (f : SystemMorphism D E) (s : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ s)
    (q : ZeroCochain V) : evalZero E s i hi (f.map0 q) = f.app s (evalZero D s i hi q) := by
  fin_cases i <;>
    simp only [evalZero, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, SystemMorphism.map0, LinearMap.prodMap_apply, SystemMorphism.app_res]

theorem evalOne_map1 {D : RestrictionSystem R V} {E : RestrictionSystem R W}
    (f : SystemMorphism D E) (s : Finset (Fin 4)) (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s)
    (q : OneCochain V) : evalOne E s i j hi hj (f.map1 q) = f.app s (evalOne D s i j hi hj q) := by
  fin_cases i <;> fin_cases j <;>
    simp only [evalOne, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, SystemMorphism.map1, LinearMap.prodMap_apply, SystemMorphism.app_res,
      map_zero, map_neg]

theorem evalTwo_map2 {D : RestrictionSystem R V} {E : RestrictionSystem R W}
    (f : SystemMorphism D E) (s : Finset (Fin 4)) (i j k : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (q : TwoCochain V) :
    evalTwo E s i j k hi hj hk (f.map2 q) = f.app s (evalTwo D s i j k hi hj hk q) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [evalTwo, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, SystemMorphism.map2, LinearMap.prodMap_apply, SystemMorphism.app_res,
      map_zero, map_neg]

end CycleQ2CechStaircaseSign
#print axioms CycleQ2CechStaircaseSign.evalTwo_d1

namespace CycleQ2CechStaircaseSign
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

theorem res_evalZero (D : RestrictionSystem R V) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (i : Fin 4) (hi : i ∈ s) (q : ZeroCochain V) :
    D.res hst (evalZero D s i hi q) = evalZero D t i (hst hi) q := by
  fin_cases i <;> simp only [evalZero, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, RestrictionSystem.res_res]

theorem res_evalOne (D : RestrictionSystem R V) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (i j : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (q : OneCochain V) :
    D.res hst (evalOne D s i j hi hj q) = evalOne D t i j (hst hi) (hst hj) q := by
  fin_cases i <;> fin_cases j <;>
    simp only [evalOne, fourCases_zero, fourCases_one, fourCases_two, fourCases_three, map_zero, map_neg, RestrictionSystem.res_res]

variable {B : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (B s t)] [∀ s t, Module R (B s t)]
variable (D : BiSystem (R := R) B)

/-- Both actual restriction maps on the rectangular common refinement. -/
def biRes {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t') :
    B s t →ₗ[R] B s' t' := (D.left t').res hs |>.comp ((D.right s).res ht)

def xValue (x : OneCochain (fun s => ZeroCochain (B s)))
    (s t : Finset (Fin 4)) (i j a : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (ha : a ∈ t) : B s t :=
  evalZero (D.right s) t a ha (evalOne D.row0 s i j hi hj x)

def yValue (y : ZeroCochain (fun s => OneCochain (B s)))
    (s t : Finset (Fin 4)) (i a b : Fin 4)
    (hi : i ∈ s) (ha : a ∈ t) (hb : b ∈ t) : B s t :=
  evalOne (D.right s) t a b ha hb (evalZero D.row1 s i hi y)

def horizontalValue (c : TwoCochain (fun s => B s ∅))
    (s t : Finset (Fin 4)) (i j k : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) : B s t :=
  (D.right s).res (Finset.empty_subset t) (evalTwo (D.left ∅) s i j k hi hj hk c)

def verticalValue (d : TwoCochain (B ∅))
    (s t : Finset (Fin 4)) (a b c : Fin 4)
    (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) : B s t :=
  (D.left t).res (Finset.empty_subset s) (evalTwo (D.right ∅) t a b c ha hb hc d)

theorem xValue_res (x : OneCochain (fun s => ZeroCochain (B s)))
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t')
    (i j a : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (ha : a ∈ t) :
    biRes D hs ht (xValue D x s t i j a hi hj ha) =
      xValue D x s' t' i j a (hs hi) (hs hj) (ht ha) := by
  dsimp only [biRes, LinearMap.comp_apply, xValue]
  rw [res_evalZero]
  change (D.horizontalMorphism hs).app t'
    (evalZero (D.right s) t' a (ht ha) (evalOne D.row0 s i j hi hj x)) = _
  rw [← evalZero_map0]
  change evalZero (D.right s') t' a (ht ha)
    (D.row0.res hs (evalOne D.row0 s i j hi hj x)) = _
  rw [res_evalOne]

theorem yValue_res (y : ZeroCochain (fun s => OneCochain (B s)))
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t')
    (i a b : Fin 4) (hi : i ∈ s) (ha : a ∈ t) (hb : b ∈ t) :
    biRes D hs ht (yValue D y s t i a b hi ha hb) =
      yValue D y s' t' i a b (hs hi) (ht ha) (ht hb) := by
  dsimp only [biRes, LinearMap.comp_apply, yValue]
  rw [res_evalOne]
  change (D.horizontalMorphism hs).app t'
    (evalOne (D.right s) t' a b (ht ha) (ht hb) (evalZero D.row1 s i hi y)) = _
  rw [← evalOne_map1]
  change evalOne (D.right s') t' a b (ht ha) (ht hb)
    (D.row1.res hs (evalZero D.row1 s i hi y)) = _
  rw [res_evalZero]

theorem horizontal_equation
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (c : TwoCochain (fun s => B s ∅))
    (hx : d1 D.row0 x = D.horizontalAugmentation.map2 c)
    (s t : Finset (Fin 4)) (i j k a : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (ha : a ∈ t) :
    xValue D x s t j k a hj hk ha - xValue D x s t i k a hi hk ha +
      xValue D x s t i j a hi hj ha = horizontalValue D c s t i j k hi hj hk := by
  have h := congrArg (fun q => evalZero (D.right s) t a ha
    (evalTwo D.row0 s i j k hi hj hk q)) hx
  rw [evalTwo_d1, evalTwo_map2] at h
  simp only [evalZero_add, evalZero_sub, BiSystem.horizontalAugmentation] at h
  rw [evalZero_augmentation] at h
  exact h

theorem mixed_equation
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (hxy : d0 D.row1 y = D.vertical0.map1 x)
    (s t : Finset (Fin 4)) (i j a b : Fin 4)
    (hi : i ∈ s) (hj : j ∈ s) (ha : a ∈ t) (hb : b ∈ t) :
    yValue D y s t j a b hj ha hb - yValue D y s t i a b hi ha hb =
      xValue D x s t i j b hi hj hb - xValue D x s t i j a hi hj ha := by
  have h := congrArg (fun q => evalOne (D.right s) t a b ha hb
    (evalOne D.row1 s i j hi hj q)) hxy
  rw [evalOne_d0, evalOne_map1, evalOne_sub] at h
  change _ = evalOne (D.right s) t a b ha hb
    (d0 (D.right s) (evalOne D.row0 s i j hi hj x)) at h
  rw [evalOne_d0] at h
  exact h

theorem vertical_equation
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (d : TwoCochain (B ∅))
    (hy : augmentation D.row2 d = D.vertical1.map0 y)
    (s t : Finset (Fin 4)) (i a b c : Fin 4)
    (hi : i ∈ s) (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) :
    yValue D y s t i b c hi hb hc - yValue D y s t i a c hi ha hc +
      yValue D y s t i a b hi ha hb = verticalValue D d s t a b c ha hb hc := by
  have h := congrArg (fun q => evalTwo (D.right s) t a b c ha hb hc
    (evalZero D.row2 s i hi q)) hy
  rw [evalZero_augmentation, evalZero_map0] at h
  change evalTwo (D.right s) t a b c ha hb hc
    ((D.horizontalMorphism (Finset.empty_subset s)).map2 d) =
      evalTwo (D.right s) t a b c ha hb hc
        (d1 (D.right s) (evalZero D.row1 s i hi y)) at h
  rw [evalTwo_map2, evalTwo_d1] at h
  exact h.symm

/-- The diagonal edge on the sixteen-open common refinement. Its formula
retains the original staircase primitives and their actual restrictions. -/
def diagonalEdge
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (u v : Fin 4 × Fin 4) : B {u.1,v.1} {u.2,v.2} :=
  xValue D x {u.1,v.1} {u.2,v.2} u.1 v.1 v.2
      (by simp) (by simp) (by simp) +
    yValue D y {u.1,v.1} {u.2,v.2} u.1 u.2 v.2
      (by simp) (by simp) (by simp)

theorem diagonalEdge_res
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (s t : Finset (Fin 4)) (u v : Fin 4 × Fin 4)
    (hu : u.1 ∈ s) (hv : v.1 ∈ s) (hu' : u.2 ∈ t) (hv' : v.2 ∈ t) :
    biRes D (pairSubset hu hv) (pairSubset hu' hv') (diagonalEdge D x y u v) =
      xValue D x s t u.1 v.1 v.2 hu hv hv' +
        yValue D y s t u.1 u.2 v.2 hu hu' hv' := by
  rw [diagonalEdge, map_add, xValue_res, yValue_res]

/-- The actual staircase has a plus sign here: the diagonal coboundary is
the sum of the two restricted cocycles. Thus the second representative is
the negative of the first in the ordinary alternating Čech convention. -/
theorem diagonal_boundary
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (c : TwoCochain (fun s => B s ∅)) (d : TwoCochain (B ∅))
    (hx : d1 D.row0 x = D.horizontalAugmentation.map2 c)
    (hxy : d0 D.row1 y = D.vertical0.map1 x)
    (hy : augmentation D.row2 d = D.vertical1.map0 y)
    (s t : Finset (Fin 4)) (u v w : Fin 4 × Fin 4)
    (hu : u.1 ∈ s) (hv : v.1 ∈ s) (hw : w.1 ∈ s)
    (hu' : u.2 ∈ t) (hv' : v.2 ∈ t) (hw' : w.2 ∈ t) :
    biRes D (pairSubset hv hw) (pairSubset hv' hw') (diagonalEdge D x y v w) -
      biRes D (pairSubset hu hw) (pairSubset hu' hw') (diagonalEdge D x y u w) +
      biRes D (pairSubset hu hv) (pairSubset hu' hv') (diagonalEdge D x y u v) =
      horizontalValue D c s t u.1 v.1 w.1 hu hv hw +
        verticalValue D d s t u.2 v.2 w.2 hu' hv' hw' := by
  rw [diagonalEdge_res D x y s t v w hv hw hv' hw',
    diagonalEdge_res D x y s t u w hu hw hu' hw',
    diagonalEdge_res D x y s t u v hu hv hu' hv']
  have h₁ := horizontal_equation D x c hx s t u.1 v.1 w.1 w.2 hu hv hw hw'
  have h₂ := mixed_equation D x y hxy s t u.1 v.1 v.2 w.2 hu hv hv' hw'
  have h₃ := vertical_equation D y d hy s t u.1 u.2 v.2 w.2 hu hu' hv' hw'
  linear_combination (norm := abel) h₁ + h₂ + h₃

/-- Extract the actual diagonal primitive from the existing SecondDescent
relation, with no replacement of its maps or sign convention. -/
theorem secondDescent_diagonal_primitive
    {c : TwoCochain (fun s => B s ∅)} {d : TwoCochain (B ∅)}
    (hcd : D.SecondDescent c d) :
    ∃ x : OneCochain (fun s => ZeroCochain (B s)),
      ∃ y : ZeroCochain (fun s => OneCochain (B s)),
      ∀ (s t : Finset (Fin 4)) (u v w : Fin 4 × Fin 4)
        (hu : u.1 ∈ s) (hv : v.1 ∈ s) (hw : w.1 ∈ s)
        (hu' : u.2 ∈ t) (hv' : v.2 ∈ t) (hw' : w.2 ∈ t),
      biRes D (pairSubset hv hw) (pairSubset hv' hw') (diagonalEdge D x y v w) -
        biRes D (pairSubset hu hw) (pairSubset hu' hw') (diagonalEdge D x y u w) +
        biRes D (pairSubset hu hv) (pairSubset hu' hv') (diagonalEdge D x y u v) =
        horizontalValue D c s t u.1 v.1 w.1 hu hv hw +
          verticalValue D d s t u.2 v.2 w.2 hu' hv' hw' := by
  obtain ⟨x,y,hx,hxy,hy⟩ := hcd
  exact ⟨x,y,diagonal_boundary D x y c d hx hxy hy⟩

end CycleQ2CechStaircaseSign
#print axioms CycleQ2CechStaircaseSign.secondDescent_diagonal_primitive
