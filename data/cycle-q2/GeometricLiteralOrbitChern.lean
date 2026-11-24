import Proposal.GeometricLiteralSheafOneClasses
import Proposal.GeometricFiniteCechHOneRefinement
import Proposal.GeometricFiniteCechOneAdditivity
import Proposal.GeometricLiteralOrbitAction

/-!
# Pullbacks of the original Cartier transitions on a common cover

The structure morphism on open sets pulls the actual native transition
units and curve generators to the source. Their logarithmic differentials
represent the translated Chern classes. On the common refinement of three
translated covers, the product of the three sets of transition units
gives the sum of their logarithmic cocycles.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitChern

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeCartierFrames CycleQ2LiteralNativeCartierTransitions
  CycleQ2LiteralNativeTransitionNaturality CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupSectionValues CycleQ2GeometricDifferentialSheaf
  CycleQ2FiniteInjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteCechHOne CycleQ2FiniteCechOneAdditivity
  CycleQ2GeometricSchemeDifferentialMap CycleQ2LiteralOrbitAction

variable (f : Surface ⟶ Surface)

def chartMap (s : Finset Vertex) (hs : s.Nonempty) (W : Surface.Opens)
    (hW : W ≤ f ⁻¹ᵁ closedOpen s) : ClosedRing s →+* Γ(Surface, W) :=
  (f.appLE (closedOpen s) W hW).hom.comp (closedSectionsEquiv s hs).toRingHom

theorem chartMap_restrict {s t : Finset Vertex} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen t) (x : ClosedRing s) :
    chartMap f s hs W (hW.trans (f.preimage_mono (closedOpen_mono hst))) x =
      chartMap f t ht W hW (closedRestriction hst x) := by
  have h := ConcreteCategory.congr_hom (C := CommRingCat)
    (f.map_appLE hW (homOfLE (closedOpen_mono hst)).op) (closedSectionsEquiv s hs x)
  exact h.symm.trans (congrArg (f.appLE _ W hW) (closedSectionsEquiv_restrict hs ht hst x))

def chartUnit (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen s) :
    Γ(Surface, W)ˣ :=
  Units.map (chartMap f s hs W hW).toMonoidHom (transition s u v hu hv)

theorem chartUnit_generator (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen s) :
    (chartUnit f s hs u v hu hv W hW : Γ(Surface,W)) *
        chartMap f s hs W hW (generator s v hv) = chartMap f s hs W hW (generator s u hu) := by
  change chartMap f s hs W hW _ * chartMap f s hs W hW _ = _
  rw [← map_mul, transition_generator]

private theorem chartUnit_natural {s t : Finset Vertex} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen t) :
    chartUnit f s hs u v hu hv W (hW.trans (f.preimage_mono (closedOpen_mono hst))) =
      chartUnit f t ht u v (hst hu) (hst hv) W hW := by
  apply Units.ext
  let x := (transition s u v hu hv : ClosedRing s)
  have e : closedRestriction hst x = (transition t u v (hst hu) (hst hv) : ClosedRing t) :=
    congrArg Units.val (transition_restrict hst u v hu hv)
  exact (chartMap_restrict f hs ht hst W hW x).trans (congrArg (chartMap f t ht W hW) e)

private theorem pair_le (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ f ⁻¹ᵁ cover u) (hv : W ≤ f ⁻¹ᵁ cover v) : W ≤ f ⁻¹ᵁ closedOpen {u,v} :=
  (le_inf hu hv).trans (f.preimage_mono (common_le_pair u v _ inf_le_left inf_le_right))

def edgeUnit (u v : Vertex) (W : Surface.Opens) (hu : W ≤ f ⁻¹ᵁ cover u)
    (hv : W ≤ f ⁻¹ᵁ cover v) : Γ(Surface, W)ˣ :=
  chartUnit f {u,v} (by simp) u v (by simp) (by simp) W (pair_le f u v W hu hv)

theorem edgeUnit_common (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen s)
    (hU : W ≤ f ⁻¹ᵁ cover u) (hV : W ≤ f ⁻¹ᵁ cover v) :
    edgeUnit f u v W hU hV = chartUnit f s hs u v hu hv W hW := by
  have hst : ({u,v} : Finset Vertex) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  exact chartUnit_natural f (by simp) hs hst u v (by simp) (by simp) W hW

theorem edgeUnit_restrict (u v : Vertex) {W V : Surface.Opens} (h : V ≤ W)
    (hu : W ≤ f ⁻¹ᵁ cover u) (hv : W ≤ f ⁻¹ᵁ cover v) :
    restrictSectionUnit h (edgeUnit f u v W hu hv) = edgeUnit f u v V (h.trans hu) (h.trans hv) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (C := CommRingCat)
    (f.appLE_map (pair_le f u v W hu hv) (homOfLE h).op)
    (closedSectionsEquiv {u,v} (by simp) (transition {u,v} u v (by simp) (by simp)))

theorem edgeUnit_cocycle (u v w : Vertex) (W : Surface.Opens)
    (hu : W ≤ f ⁻¹ᵁ cover u) (hv : W ≤ f ⁻¹ᵁ cover v) (hw : W ≤ f ⁻¹ᵁ cover w) :
    edgeUnit f u v W hu hv * edgeUnit f v w W hv hw = edgeUnit f u w W hu hw := by
  let s : Finset Vertex := {u,v,w}
  have hs : s.Nonempty := by simp [s]
  have hsu : u ∈ s := by simp [s]
  have hsv : v ∈ s := by simp [s]
  have hsw : w ∈ s := by simp [s]
  have hW : W ≤ f ⁻¹ᵁ closedOpen s :=
    (le_inf (le_inf hu hv) hw).trans (f.preimage_mono
      (common_le_triple u v w _ (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) inf_le_right))
  rw [edgeUnit_common f s hs u v hsu hsv W hW, edgeUnit_common f s hs v w hsv hsw W hW,
    edgeUnit_common f s hs u w hsu hsw W hW]
  exact (map_mul _ _ _).symm.trans (congrArg
    (Units.map (chartMap f s hs W hW).toMonoidHom) (transition_cocycle s u v w hsu hsv hsw))

private theorem cover_le_single (u : Vertex) : cover u ≤ closedOpen {u} := by
  rw [closedOpen_eq]
  refine le_iInf (fun x => le_iInf (fun hx => ?_))
  have h : x = u := Finset.mem_singleton.mp hx
  subst x
  exact le_rfl

/-- The original chart equation pulled back to a source subopen. -/
def edgeGenerator (u : Vertex) (W : Surface.Opens) (hu : W ≤ f ⁻¹ᵁ cover u) : Γ(Surface,W) :=
  chartMap f {u} (by simp) W (hu.trans (f.preimage_mono (cover_le_single u)))
    (generator {u} u (by simp))

theorem edgeGenerator_restrict (u : Vertex) {W V : Surface.Opens} (h : V ≤ W)
    (hu : W ≤ f ⁻¹ᵁ cover u) :
    Surface.presheaf.map (homOfLE h).op (edgeGenerator f u W hu) = edgeGenerator f u V (h.trans hu) :=
  ConcreteCategory.congr_hom (C := CommRingCat)
    (f.appLE_map (hu.trans (f.preimage_mono (cover_le_single u))) (homOfLE h).op)
    (closedSectionsEquiv {u} (by simp) (generator {u} u (by simp)))

theorem edgeGenerator_common (s : Finset Vertex) (hs : s.Nonempty) (u : Vertex)
    (hu : u ∈ s) (W : Surface.Opens) (hW : W ≤ f ⁻¹ᵁ closedOpen s)
    (hU : W ≤ f ⁻¹ᵁ cover u) :
    edgeGenerator f u W hU = chartMap f s hs W hW (generator s u hu) := by
  have hst : ({u} : Finset Vertex) ⊆ s := Finset.singleton_subset_iff.mpr hu
  exact (chartMap_restrict f (by simp) hs hst W hW (generator {u} u (by simp))).trans
    (congrArg (chartMap f s hs W hW) (generator_restrict hst u (by simp)))

theorem edgeUnit_mul_generator (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ f ⁻¹ᵁ cover u) (hv : W ≤ f ⁻¹ᵁ cover v) :
    (edgeUnit f u v W hu hv : Γ(Surface,W)) * edgeGenerator f v W hv = edgeGenerator f u W hu := by
  rw [edgeGenerator_common f {u,v} (by simp) v (by simp) W (pair_le f u v W hu hv),
    edgeGenerator_common f {u,v} (by simp) u (by simp) W (pair_le f u v W hu hv)]
  exact chartUnit_generator f {u,v} (by simp) u v (by simp) (by simp) W (pair_le f u v W hu hv)

/-- A translated Chern cocycle on any refinement of the pullback cover. -/
def translatedOne {ι : Type} (U : ι → Surface.Opens) (p : ι → Vertex)
    (h : ∀ i, U i ≤ f ⁻¹ᵁ cover (p i)) : One differentialAddSheaf U :=
  fun i j => sheafLogDifferential _ (edgeUnit f (p i) (p j) (U i ⊓ U j)
    (inf_le_left.trans (h i)) (inf_le_right.trans (h j)))

theorem edgeValue_translatedOne {ι : Type} (U : ι → Surface.Opens) (p : ι → Vertex)
    (h : ∀ i, U i ≤ f ⁻¹ᵁ cover (p i)) (i j : ι) (W : Surface.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue differentialAddSheaf U (translatedOne f U p h) i j W hi hj =
      sheafLogDifferential W (edgeUnit f (p i) (p j) W (hi.trans (h i)) (hj.trans (h j))) := by
  change DifferentialSheaf.val.map (homOfLE (le_inf hi hj)).op
    (sheafLogDifferential _ (edgeUnit f _ _ _ _ _)) = _
  rw [sheafLogDifferential_restrict, edgeUnit_restrict]

theorem translatedOne_closed {ι : Type} (U : ι → Surface.Opens) (p : ι → Vertex)
    (h : ∀ i, U i ≤ f ⁻¹ᵁ cover (p i)) : IsOneCocycle differentialAddSheaf U (translatedOne f U p h) := by
  intro i j k W hi hj hk
  change edgeValue differentialAddSheaf U (translatedOne f U p h) i k W hi hk =
    edgeValue differentialAddSheaf U (translatedOne f U p h) i j W hi hj +
      edgeValue differentialAddSheaf U (translatedOne f U p h) j k W hj hk
  rw [edgeValue_translatedOne, edgeValue_translatedOne, edgeValue_translatedOne,
    ← sheafLogDifferential_mul, edgeUnit_cocycle]

def translatedCover (i : Vertex) : Surface.Opens := f ⁻¹ᵁ cover i

theorem translatedCover_top : (⨆ i, translatedCover f i) = ⊤ := by
  rw [show (⨆ i, translatedCover f i) = f ⁻¹ᵁ (⨆ i, cover i) from (f.preimage_iSup _).symm,
    cover_covers, Scheme.Hom.preimage_top]

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

def translatedClass : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass (translatedCover f) (translatedCover_top f)
    (translatedOne f _ id (fun _ => le_rfl)) (translatedOne_closed f _ id (fun _ => le_rfl))

/-- The identity translation recovers the Chern cochain of the original curve. -/
theorem translatedOne_id :
    translatedOne (𝟙 Surface) cover id (fun _ => le_rfl) = chernOne := by
  funext u v
  unfold translatedOne chernOne chernValue
  rw [nativeChernSection_log]
  change _ = DifferentialSheaf.val.map
    (homOfLE (common_le_pair u v (cover u ⊓ cover v) inf_le_left inf_le_right)).op
    (sheafLogDifferential (closedOpen {u,v}) (sectionUnit {u,v} (by simp)
      (transition {u,v} u v (by simp) (by simp))))
  rw [sheafLogDifferential_restrict]
  apply congrArg (sheafLogDifferential _)
  apply Units.ext
  rfl

theorem schemeDifferentialMap_log (hc : ∀ (U : Surface.Opens) (c : ℂ),
    f.app U (coefficientOn Surface.sheaf globalCoefficient U c) =
      coefficientOn Surface.sheaf globalCoefficient (f ⁻¹ᵁ U) c)
    (U : Surface.Opens) (a : Γ(Surface,U)ˣ) :
    (schemeDifferentialMap f globalCoefficient globalCoefficient hc).val.app (op U)
      (sheafLogDifferential U a) =
        sheafLogDifferential (f ⁻¹ᵁ U) (Units.map (f.app U).hom.toMonoidHom a) := by
  unfold sheafLogDifferential
  rw [map_smul, schemeDifferentialMap_D]
  rfl

theorem edgeUnit_comp (g : Surface ⟶ Surface) (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ f ⁻¹ᵁ cover u) (hv : W ≤ f ⁻¹ᵁ cover v) :
    edgeUnit (g ≫ f) u v (g ⁻¹ᵁ W) (g.preimage_mono hu) (g.preimage_mono hv) =
      Units.map (g.app W).hom.toMonoidHom (edgeUnit f u v W hu hv) := by
  apply Units.ext
  have e := g.appLE_comp_appLE f (closedOpen {u,v}) W (g ⁻¹ᵁ W) (pair_le f u v W hu hv) le_rfl
  rw [← g.app_eq_appLE] at e
  exact ConcreteCategory.congr_hom (C := CommRingCat) e.symm
    (closedSectionsEquiv {u,v} (by simp) (transition {u,v} u v (by simp) (by simp)))

/-- Pulling back a translated cocycle once more applies the canonical
cotangent map to it on every double intersection. -/
theorem translatedOne_comp (g : Surface ⟶ Surface) (hc : ∀ (U : Surface.Opens) (c : ℂ),
    g.app U (coefficientOn Surface.sheaf globalCoefficient U c) =
      coefficientOn Surface.sheaf globalCoefficient (g ⁻¹ᵁ U) c) (u v : Vertex) :
    translatedOne (g ≫ f) (translatedCover (g ≫ f)) id (fun _ => le_rfl) u v =
      (schemeDifferentialMap g globalCoefficient globalCoefficient hc).val.app
        (op (translatedCover f u ⊓ translatedCover f v))
        (translatedOne f (translatedCover f) id (fun _ => le_rfl) u v) := by
  unfold translatedOne
  rw [schemeDifferentialMap_log]
  apply congrArg (sheafLogDifferential _)
  exact edgeUnit_comp f g u v (translatedCover f u ⊓ translatedCover f v) inf_le_left inf_le_right

theorem translatedOne_eq_differentialMap (hc : ∀ (U : Surface.Opens) (c : ℂ),
    f.app U (coefficientOn Surface.sheaf globalCoefficient U c) =
      coefficientOn Surface.sheaf globalCoefficient (f ⁻¹ᵁ U) c) (u v : Vertex) :
    translatedOne f (translatedCover f) id (fun _ => le_rfl) u v =
      (schemeDifferentialMap f globalCoefficient globalCoefficient hc).val.app (op (cover u ⊓ cover v))
        (chernOne u v) := by
  rw [← translatedOne_id]
  unfold translatedOne
  rw [schemeDifferentialMap_log]
  apply congrArg (sheafLogDifferential _)
  apply Units.ext
  let W := cover u ⊓ cover v
  let t := (closedSectionsEquiv {u,v} (by simp) (transition {u,v} u v (by simp) (by simp)))
  have hn := ConcreteCategory.congr_hom (C := CommRingCat)
    (f.naturality (homOfLE (common_le_pair u v W inf_le_left inf_le_right)).op) t
  exact hn.symm

theorem translatedClass_id :
    translatedClass (𝟙 Surface) = CycleQ2LiteralSheafOneClasses.chernDerivedClass := by
  unfold translatedClass CycleQ2LiteralSheafOneClasses.chernDerivedClass
  change cechOneClass cover _ (translatedOne (𝟙 Surface) cover id _) _ = _
  congr 1
  exact translatedOne_id

abbrev Index := Vertex × Vertex × Vertex

variable (g k : Surface ⟶ Surface)

def commonCover (i : Index) : Surface.Opens :=
  translatedCover f i.1 ⊓ (translatedCover g i.2.1 ⊓ translatedCover k i.2.2)

theorem commonCover_top : (⨆ i, commonCover f g k i) = ⊤ := by
  apply top_unique
  intro x _
  have choose (m : Surface ⟶ Surface) : ∃ i, x ∈ translatedCover m i := by
    apply Opens.mem_iSup.mp
    rw [translatedCover_top]
    trivial
  obtain ⟨i,hi⟩ := choose f
  obtain ⟨j,hj⟩ := choose g
  obtain ⟨l,hl⟩ := choose k
  exact Opens.mem_iSup.mpr ⟨(i,j,l), hi,hj,hl⟩

/-- Transition of the tensor product of the three pulled-back inverse ideals. -/
def productUnit (i j : Index) (W : Surface.Opens) (hi : W ≤ commonCover f g k i)
    (hj : W ≤ commonCover f g k j) : Γ(Surface,W)ˣ :=
  edgeUnit f i.1 j.1 W (hi.trans inf_le_left) (hj.trans inf_le_left) *
    edgeUnit g i.2.1 j.2.1 W (hi.trans (inf_le_right.trans inf_le_left))
      (hj.trans (inf_le_right.trans inf_le_left)) *
    edgeUnit k i.2.2 j.2.2 W (hi.trans (inf_le_right.trans inf_le_right))
      (hj.trans (inf_le_right.trans inf_le_right))

def productGenerator (i : Index) (W : Surface.Opens) (hi : W ≤ commonCover f g k i) : Γ(Surface,W) :=
  edgeGenerator f i.1 W (hi.trans inf_le_left) *
    edgeGenerator g i.2.1 W (hi.trans (inf_le_right.trans inf_le_left)) *
    edgeGenerator k i.2.2 W (hi.trans (inf_le_right.trans inf_le_right))

theorem productGenerator_restrict (i : Index) {W V : Surface.Opens} (h : V ≤ W)
    (hi : W ≤ commonCover f g k i) :
    Surface.presheaf.map (homOfLE h).op (productGenerator f g k i W hi) =
      productGenerator f g k i V (h.trans hi) := by
  simp only [productGenerator, map_mul, edgeGenerator_restrict]

theorem productUnit_restrict (i j : Index) {W V : Surface.Opens} (h : V ≤ W)
    (hi : W ≤ commonCover f g k i) (hj : W ≤ commonCover f g k j) :
    restrictSectionUnit h (productUnit f g k i j W hi hj) = productUnit f g k i j V (h.trans hi) (h.trans hj) := by
  change (Units.map _) (_ * _ * _) = _
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (edgeUnit_restrict f _ _ h _ _) (edgeUnit_restrict g _ _ h _ _))
    (edgeUnit_restrict k _ _ h _ _)

theorem productUnit_mul_generator (i j : Index) (W : Surface.Opens)
    (hi : W ≤ commonCover f g k i) (hj : W ≤ commonCover f g k j) :
    (productUnit f g k i j W hi hj : Γ(Surface,W)) * productGenerator f g k j W hj =
      productGenerator f g k i W hi := by
  simp only [productUnit, productGenerator, Units.val_mul]
  rw [← edgeUnit_mul_generator f i.1 j.1 W (hi.trans inf_le_left) (hj.trans inf_le_left),
    ← edgeUnit_mul_generator g i.2.1 j.2.1 W (hi.trans (inf_le_right.trans inf_le_left))
      (hj.trans (inf_le_right.trans inf_le_left)),
    ← edgeUnit_mul_generator k i.2.2 j.2.2 W (hi.trans (inf_le_right.trans inf_le_right))
      (hj.trans (inf_le_right.trans inf_le_right))]
  ring

def productOne : One differentialAddSheaf (commonCover f g k) :=
  fun i j => sheafLogDifferential _ (productUnit f g k i j _ inf_le_left inf_le_right)

private abbrev leftOne := translatedOne f (commonCover f g k) (fun i => i.1) (fun _ => inf_le_left)
private abbrev middleOne := translatedOne g (commonCover f g k) (fun i => i.2.1)
  (fun _ => inf_le_right.trans inf_le_left)
private abbrev rightOne := translatedOne k (commonCover f g k) (fun i => i.2.2)
  (fun _ => inf_le_right.trans inf_le_right)

theorem productOne_eq_sum : productOne f g k =
    leftOne f g k + middleOne f g k + rightOne f g k := by
  funext i j
  change sheafLogDifferential _ (_ * _ * _) = _ + _ + _
  rw [sheafLogDifferential_mul, sheafLogDifferential_mul]
  rfl

theorem productOne_closed : IsOneCocycle differentialAddSheaf (commonCover f g k) (productOne f g k) := by
  rw [productOne_eq_sum]
  let C := oneCocycles (F := differentialAddSheaf) (commonCover f g k)
  exact C.add_mem (C.add_mem (translatedOne_closed f _ _ _) (translatedOne_closed g _ _ _))
    (translatedOne_closed k _ _ _)

def productDerivedClass : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass (commonCover f g k) (commonCover_top f g k) (productOne f g k) (productOne_closed f g k)

theorem translatedOne_refine {ι : Type} (U : ι → Surface.Opens) (p : ι → Vertex)
    (h : ∀ i, U i ≤ translatedCover f (p i)) :
    CycleQ2FiniteCechRefinement.restrictOne (translatedCover f) U p h
      (translatedOne f _ id (fun _ => le_rfl)) = translatedOne f U p h := by
  funext i j
  exact edgeValue_translatedOne f _ id (fun _ => le_rfl) (p i) (p j) (U i ⊓ U j)
    (inf_le_left.trans (h i)) (inf_le_right.trans (h j))

theorem translatedClass_refine {ι : Type} [Fintype ι] (U : ι → Surface.Opens)
    (hU : (⨆ i, U i) = ⊤) (p : ι → Vertex) (h : ∀ i, U i ≤ translatedCover f (p i)) :
    cechOneClass U hU (translatedOne f U p h) (translatedOne_closed f U p h) =
      translatedClass f := by
  unfold translatedClass
  rw [← cechOneClass_refinement (translatedCover f) U p h (translatedCover_top f) hU]
  congr 1
  exact (translatedOne_refine f U p h).symm

/-- The derived class of the actual triple-product units is the sum on the three
original pullback covers. -/
theorem productDerivedClass_eq_sum :
    productDerivedClass f g k = translatedClass f + translatedClass g + translatedClass k := by
  unfold productDerivedClass
  let C := oneCocycles (F := differentialAddSheaf) (commonCover f g k)
  have h₁ : leftOne f g k ∈ C := translatedOne_closed f _ _ _
  have h₂ : middleOne f g k ∈ C := translatedOne_closed g _ _ _
  have h₃ : rightOne f g k ∈ C := translatedOne_closed k _ _ _
  simp only [productOne_eq_sum, cechOneClass_add _ _ _ _ (C.add_mem h₁ h₂) h₃,
    cechOneClass_add _ _ _ _ h₁ h₂]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (translatedClass_refine f _ _ _ _) (translatedClass_refine g _ _ _ _))
    (translatedClass_refine k _ _ _ _)

/-- The product for the literal order-three projective action uses the original
curve, its pullback by the generator, and its pullback by the square. -/
def orbitDerivedClass (z : ℂ) (hz : z^3 = 1) : differentialAddSheaf.H' 1 ⊤ :=
  let a := (closedProjectiveAction z hz).hom
  productDerivedClass (𝟙 Surface) a (a ≫ a)

theorem orbitDerivedClass_eq_sum (z : ℂ) (hz : z^3 = 1) :
    let a := (closedProjectiveAction z hz).hom
    orbitDerivedClass z hz =
      CycleQ2LiteralSheafOneClasses.chernDerivedClass + translatedClass a + translatedClass (a ≫ a) := by
  dsimp only
  unfold orbitDerivedClass
  rw [productDerivedClass_eq_sum, translatedClass_id]

end CycleQ2LiteralOrbitChern

end

#print axioms CycleQ2LiteralOrbitChern.edgeUnit_cocycle
#print axioms CycleQ2LiteralOrbitChern.productDerivedClass_eq_sum

#print axioms CycleQ2LiteralOrbitChern.orbitDerivedClass_eq_sum
#print axioms CycleQ2LiteralOrbitChern.translatedOne_eq_differentialMap
