import Proposal.GeometricCechRefinement
import Proposal.GeometricThreefoldDeRhamDifferential
import Proposal.GeometricLiteralThreefoldLowerBoundaryObstruction

/-!
# The original test in the unfiltered Čech–de Rham complex

Use the original six increasing edges, four faces, and quadruple
intersection. The vertical signs are those of
the differential `δ + (-1)^p d` in Čech degree `p`. The corrected
vertex forms and the original two-form edges give a nonzero class
in degree three on the original cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2FourOpenDeRhamTotal

open CategoryTheory TopologicalSpace
open CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2CechTwoComparison
open CycleQ2GeometricSheafLocalIso (res)

variable {X : TopCat.{0}} (U : Fin 4 → Opens X) (F₀ F₁ F₂ F₃ : AbSheaf X)

abbrev TotalTwo := Zero F₂ U × One F₁ U × Two F₀ U
abbrev TotalThree := Zero F₃ U × One F₂ U × Two F₁ U × Three F₀ U
abbrev TotalFour := One F₃ U × Two F₂ U × Three F₁ U

variable {F₀ F₁ F₂ F₃}
  (d : F₀ ⟶ F₁) (e : F₁ ⟶ F₂) (f : F₂ ⟶ F₃)

private theorem mapZero_zero {F G : AbSheaf X} (g : F ⟶ G) : mapZero U g 0 = 0 := by
  funext i
  exact (app g _).map_zero
private theorem mapOne_zero {F G : AbSheaf X} (g : F ⟶ G) : mapOne U g 0 = 0 := by
  simp [mapOne]
private theorem mapTwo_zero {F G : AbSheaf X} (g : F ⟶ G) : mapTwo U g 0 = 0 := by
  simp [mapTwo]

def boundary : TotalTwo U F₀ F₁ F₂ →+ TotalThree U F₀ F₁ F₂ F₃ where
  toFun x := (mapZero U f x.1, d0 F₂ U x.1 - mapOne U e x.2.1,
    d1 F₁ U x.2.1 + mapTwo U d x.2.2, d2 F₀ U x.2.2)
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero, mapZero_zero, d0_zero, d1_zero, d2_zero,
      mapOne_zero, mapTwo_zero, sub_self, add_zero]
    rfl
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, mapZero_add, mapOne_add, mapTwo_add,
      d0_add, d1_add, d2_add]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> abel

def differential : TotalThree U F₀ F₁ F₂ F₃ →+ TotalFour U F₁ F₂ F₃ where
  toFun x := (d0 F₃ U x.1 - mapOne U f x.2.1,
    d1 F₂ U x.2.1 + mapTwo U e x.2.2.1, d2 F₁ U x.2.2.1 - app d _ x.2.2.2)
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero, d0_zero, d1_zero, d2_zero,
      mapOne_zero, mapTwo_zero, map_zero, sub_self, add_zero]
    rfl
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, mapOne_add, mapTwo_add,
      d0_add, d1_add, d2_add, map_add]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> abel

theorem differential_boundary (hd : d ≫ e = 0) (he : e ≫ f = 0)
    (x : TotalTwo U F₀ F₁ F₂) : differential U d e f (boundary U d e f x) = 0 := by
  have hOne : mapOne U f (mapOne U e x.2.1) = 0 := by
    simp only [mapOne, app_comp, he, app_zero]
    rfl
  have hTwo : mapTwo U e (mapTwo U d x.2.2) = 0 := by
    simp only [mapTwo, app_comp, hd, app_zero]
    rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change d0 F₃ U (mapZero U f x.1) -
      mapOne U f (d0 F₂ U x.1 - mapOne U e x.2.1) = 0
    rw [mapOne_sub, hOne, mapOne_d0, sub_zero, sub_self]
  · change d1 F₂ U (d0 F₂ U x.1 - mapOne U e x.2.1) +
      mapTwo U e (d1 F₁ U x.2.1 + mapTwo U d x.2.2) = 0
    rw [d1_sub, d1_d0, mapTwo_add, hTwo, add_zero, mapTwo_d1, zero_sub, neg_add_cancel]
  · change d2 F₁ U (d1 F₁ U x.2.1 + mapTwo U d x.2.2) - app d _ (d2 F₀ U x.2.2) = 0
    rw [d2_add, d2_d1, zero_add, mapThree_d2, sub_self]

variable (hd : d ≫ e = 0) (he : e ≫ f = 0)

def toCycles : TotalTwo U F₀ F₁ F₂ →+ (differential U d e f).ker where
  toFun x := ⟨boundary U d e f x, differential_boundary U d e f hd he x⟩
  map_zero' := Subtype.ext (boundary U d e f).map_zero
  map_add' x y := Subtype.ext ((boundary U d e f).map_add x y)

/-- Full cohomology in degree three of this Čech total complex. -/
abbrev HThree := (differential U d e f).ker ⧸ (toCycles U d e f hd he).range

theorem class_eq_zero_iff (x : (differential U d e f).ker) :
    (QuotientAddGroup.mk x : HThree U d e f hd he) = 0 ↔
      ∃ b : TotalTwo U F₀ F₁ F₂, boundary U d e f b = x.val := by
  rw [QuotientAddGroup.eq_zero_iff]
  change (∃ b, toCycles U d e f hd he b = x) ↔ _
  exact ⟨fun ⟨b, hb⟩ => ⟨b, congrArg Subtype.val hb⟩,
    fun ⟨b, hb⟩ => ⟨b, Subtype.ext hb⟩⟩

/-- On a subopen of any one vertex, cohomology restricts to ordinary
top-degree sections modulo the genuine exterior differential. -/
abbrev LocalTop (V : Opens X) := Sections F₃ V ⧸ (app f V).range

private def cyclesToLocal (i : Fin 4) (V : Opens X) (h : V ≤ U i) :
    (differential U d e f).ker →+ LocalTop f V where
  toFun x := QuotientAddGroup.mk (res F₃ h (x.val.1 i))
  map_zero' := by
    change (QuotientAddGroup.mk (res F₃ h 0) : LocalTop f V) = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change (QuotientAddGroup.mk (res F₃ h (x.val.1 i + y.val.1 i)) : LocalTop f V) =
      QuotientAddGroup.mk (res F₃ h (x.val.1 i)) + QuotientAddGroup.mk (res F₃ h (y.val.1 i))
    rw [map_add]
    rfl

def restrictVertex (i : Fin 4) (V : Opens X) (h : V ≤ U i) :
    HThree U d e f hd he →+ LocalTop f V :=
  QuotientAddGroup.lift _ (cyclesToLocal U d e f i V h) <| by
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    change (QuotientAddGroup.mk (res F₃ h (app f (U i) (b.1 i))) : LocalTop f V) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨res F₂ h (b.1 i), app_res f h (b.1 i)⟩

/-- A vanishing restriction of a total class supplies an actual local
two-form primitive of its vertex component. -/
theorem restrictVertex_eq_zero_iff (i : Fin 4) (V : Opens X) (h : V ≤ U i)
    (x : (differential U d e f).ker) :
    restrictVertex U d e f hd he i V h (QuotientAddGroup.mk x) = 0 ↔
      ∃ a : Sections F₂ V, app f V a = res F₃ h (x.val.1 i) := by
  change (QuotientAddGroup.mk (res F₃ h (x.val.1 i)) : LocalTop f V) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

end CycleQ2FourOpenDeRhamTotal

#print axioms CycleQ2FourOpenDeRhamTotal.class_eq_zero_iff

namespace CycleQ2LiteralThreefoldUnfilteredCech

open CategoryTheory TopologicalSpace AlgebraicGeometry
open CycleQ2LiteralAmbientCharts (fixedOpen)
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralThreefoldSecondDifferential (Three secondDifferential vertexThree
  first_second_zero secondDifferential_test_edge)
open CycleQ2FourOpenDeRhamTotal
open CycleQ2LiteralThreefoldHodgeCech
open CycleQ2LiteralThreefoldTestEdges (nativeEdge)
open CycleQ2LiteralThreefoldTestClass (face)
open CycleQ2GeometricSheafLocalIso (res res_comp res_self)
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2CechTwoToDerived
open CycleQ2FiniteInjectiveCech (edgeValue boundaryValue)
open CycleQ2FourToFiniteCech
open CycleQ2LiteralThreefoldLowerBoundaryObstruction (Functions LowerBoundary ambient_test_no_lower_boundary)

private def edges : CycleQ2CechTwoToDerived.One Two fixedOpen :=
  (edge nativeEdge 0 1 (by decide) _ le_rfl, edge nativeEdge 0 2 (by decide) _ le_rfl,
    edge nativeEdge 0 3 (by decide) _ le_rfl, edge nativeEdge 1 2 (by decide) _ le_rfl,
    edge nativeEdge 1 3 (by decide) _ le_rfl, edge nativeEdge 2 3 (by decide) _ le_rfl)

private theorem asAlternatingEdges :
    extendOne fixedOpen edges = (hodgeCocycle nativeEdge face).val := by
  funext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [extendOne, edges, hodgeCocycle, edgeAt, fourCases_zero, fourCases_one,
    fourCases_two, fourCases_three, CartierCechFour.fourEdgeCocycle,
    CartierCechFour.fourEdgeCochain, CartierCechFour.quad_mk_0,
    CartierCechFour.quad_mk_1, CartierCechFour.quad_mk_2, CartierCechFour.quad_mk_3]
  all_goals first | rfl | exact res_self Two _ _

private theorem eta_closed : d1 Two fixedOpen edges = 0 := by
  have h (i j k : Fin 4) (W : X.Opens) (hi : W ≤ fixedOpen i)
      (hj : W ≤ fixedOpen j) (hk : W ≤ fixedOpen k) :
      faceAt fixedOpen (d1 Two fixedOpen edges) i j k W hi hj hk = 0 := by
    rw [← boundaryValue_extendOne, asAlternatingEdges]
    let a := edgeValue Two fixedOpen (hodgeCocycle nativeEdge face).val i j W hi hj
    let b := edgeValue Two fixedOpen (hodgeCocycle nativeEdge face).val j k W hj hk
    let c := edgeValue Two fixedOpen (hodgeCocycle nativeEdge face).val i k W hi hk
    have hc : a + b = c := (hodgeCocycle nativeEdge face).condition i j k W hi hj hk
    change b - c + a = 0
    rw [← hc]
    abel
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · have h012 := h 0 1 2 (Triple 0 1 2) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    change res Two (le_refl _) (d1 Two fixedOpen edges).1 = 0 at h012
    exact (res_self Two _ _).symm.trans h012
  · have h013 := h 0 1 3 (Triple 0 1 3) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    change res Two (le_refl _) (d1 Two fixedOpen edges).2.1 = 0 at h013
    exact (res_self Two _ _).symm.trans h013
  · have h023 := h 0 2 3 (Triple 0 2 3) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    change res Two (le_refl _) (d1 Two fixedOpen edges).2.2.1 = 0 at h023
    exact (res_self Two _ _).symm.trans h023
  · have h123 := h 1 2 3 (Triple 1 2 3) (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    change res Two (le_refl _) (d1 Two fixedOpen edges).2.2.2 = 0 at h123
    exact (res_self Two _ _).symm.trans h123

private theorem sameVertex {i j : Fin 4} (hij : i = j) (W : X.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    res Three hi (vertexThree i) = res Three hj (vertexThree j) := by
  subst j
  rfl

private theorem pair_test (i j : Fin 4) (hij : i < j) :
    app secondDifferential (fixedOpen i ⊓ fixedOpen j) (edge nativeEdge i j hij _ le_rfl) =
      res Three inf_le_left (vertexThree i) - res Three inf_le_right (vertexThree j) := by
  let k := slot i j hij
  let W := fixedOpen i ⊓ fixedOpen j
  have hj : i.succAbove k = j := succAbove_slot i j hij
  have h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k) := by
    rw [hj]
  let η := overlapSection i k (fixedOpen i ⊓ fixedOpen (i.succAbove k)) le_rfl (nativeEdge i k)
  let a := res Three (inf_le_left : fixedOpen i ⊓ fixedOpen (i.succAbove k) ≤ fixedOpen i)
    (vertexThree i)
  let b := res Three (inf_le_right :
    fixedOpen i ⊓ fixedOpen (i.succAbove k) ≤ fixedOpen (i.succAbove k))
    (vertexThree (i.succAbove k))
  have hEdge : res Two h η = edge nativeEdge i j hij W le_rfl :=
    overlapSection_restrict i k le_rfl h (nativeEdge i k)
  have he := (congrArg (app secondDifferential W) hEdge.symm).trans
    (app_res secondDifferential h η)
  have hd : app secondDifferential _ η = a - b := secondDifferential_test_edge i k
  have ha : res Three h a = res Three inf_le_left (vertexThree i) := res_comp Three inf_le_left h _
  have hb := (res_comp Three inf_le_right h (vertexThree (i.succAbove k))).trans
    (sameVertex hj W (h.trans inf_le_right) inf_le_right)
  exact he.trans ((congrArg (res Three h) hd).trans
    (((res Three h).map_sub a b).trans (congrArg₂ (· - ·) ha hb)))

def test : TotalThree fixedOpen Functions One Two Three :=
  (fun i => -(vertexThree i), edges, 0, 0)

theorem test_closed : CycleQ2FourOpenDeRhamTotal.differential fixedOpen
    functionDifferential differential secondDifferential test = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change d0 Three fixedOpen (fun i => -vertexThree i) -
      mapOne fixedOpen secondDifferential edges = 0
    apply sub_eq_zero.mpr
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
    all_goals simp only [d0, mapOne, edges, map_neg, neg_sub_neg, pair_test]
  · change d1 Two fixedOpen edges + mapTwo fixedOpen differential 0 = 0
    rw [eta_closed]
    simp [mapTwo]
  · change d2 One fixedOpen 0 - app functionDifferential _ 0 = 0
    rw [CycleQ2CechTwoComparison.d2_zero, map_zero, sub_self]

/-- The signed correction equation on every ordered pair of original
opens, including pairs in reverse order and the diagonal. -/
theorem test_edge_correction (i j : Fin 4) :
    app secondDifferential (fixedOpen i ⊓ fixedOpen j) ((hodgeCocycle nativeEdge face).val i j) =
      res Three inf_le_right (-(vertexThree j)) - res Three inf_le_left (-(vertexThree i)) := by
  let a : Zero Three fixedOpen := fun k => -(vertexThree k)
  let W := fixedOpen i ⊓ fixedOpen j
  have h := congrArg Prod.fst test_closed
  change d0 Three fixedOpen a - mapOne fixedOpen secondDifferential edges = 0 at h
  have hd : d0 Three fixedOpen a = mapOne fixedOpen secondDifferential edges := sub_eq_zero.mp h
  have hp := congrArg (fun x : CycleQ2CechTwoToDerived.One Three fixedOpen =>
    edgeAt fixedOpen x i j W inf_le_left inf_le_right) hd
  have h₀ := edgeAt_d0 fixedOpen a i j W inf_le_left inf_le_right
  have h₁ := edgeAt_mapOne fixedOpen secondDifferential edges i j W inf_le_left inf_le_right
  have he : edgeAt fixedOpen edges i j W inf_le_left inf_le_right = (hodgeCocycle nativeEdge face).val i j :=
    congrFun (congrFun asAlternatingEdges i) j
  exact (congrArg (app secondDifferential W) he).symm.trans
    (h₁.symm.trans (hp.symm.trans h₀))

abbrev Cohomology := HThree fixedOpen functionDifferential differential secondDifferential
  function_differential_zero first_second_zero

/-- The fixed test in total degree three, with the lower cochains allowed. -/
def testClass : Cohomology := QuotientAddGroup.mk ⟨test, test_closed⟩

set_option maxHeartbeats 1200000 in
private theorem faceAt_add {Y : TopCat.{0}} (F : AbSheaf Y) (U : Fin 4 → Opens Y)
    (a b : CycleQ2CechTwoToDerived.Two F U)
    (i j k : Fin 4) (W : Opens Y) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceAt U (a + b) i j k W hi hj hk =
      faceAt U a i j k W hi hj hk + faceAt U b i j k W hi hj hk := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three,
      map_add, Prod.fst_add, Prod.snd_add, neg_add, zero_add]

private theorem faceAt_zero {Y : TopCat.{0}} (F : AbSheaf Y) (U : Fin 4 → Opens Y)
    (i j k : Fin 4) (W : Opens Y) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    faceAt (F := F) U 0 i j k W hi hj hk = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [faceAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three,
      map_zero, Prod.fst_zero, Prod.snd_zero, neg_zero]

private theorem edgeAt_sub {Y : TopCat.{0}} (F : AbSheaf Y) (U : Fin 4 → Opens Y)
    (a b : CycleQ2CechTwoToDerived.One F U)
    (i j : Fin 4) (W : Opens Y) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeAt U (a - b) i j W hi hj = edgeAt U a i j W hi hj - edgeAt U b i j W hi hj := by
  fin_cases i <;> fin_cases j <;>
    simp only [edgeAt, fourCases_zero, fourCases_one, fourCases_two, fourCases_three,
      map_sub, Prod.fst_sub, Prod.snd_sub, neg_sub, neg_sub_neg, sub_self]

theorem testClass_ne_zero : testClass ≠ 0 := by
  intro h
  obtain ⟨b,hb⟩ := (class_eq_zero_iff fixedOpen functionDifferential differential secondDifferential
    function_differential_zero first_second_zero ⟨test,test_closed⟩).mp h
  have hf := congrArg (fun x : TotalThree fixedOpen Functions One Two Three => x.2.2.2) hb
  have h1 := congrArg (fun x : TotalThree fixedOpen Functions One Two Three => x.2.2.1) hb
  have h2 := congrArg (fun x : TotalThree fixedOpen Functions One Two Three => x.2.1) hb
  change d2 Functions fixedOpen b.2.2 = 0 at hf
  change d1 One fixedOpen b.2.1 + mapTwo fixedOpen functionDifferential b.2.2 = 0 at h1
  change d0 Two fixedOpen b.1 - mapOne fixedOpen differential b.2.1 = edges at h2
  apply ambient_test_no_lower_boundary
  refine ⟨⟨b.1, extendOne fixedOpen b.2.1, b.2.2, hf, ?_, ?_⟩⟩
  · intro i j k W hi hj hk
    have he := congrArg (fun x : CycleQ2CechTwoToDerived.Two One fixedOpen =>
      faceAt fixedOpen x i j k W hi hj hk) h1
    have hsum := (faceAt_add One fixedOpen (d1 One fixedOpen b.2.1)
      (mapTwo fixedOpen functionDifferential b.2.2) i j k W hi hj hk).symm.trans
      (he.trans (faceAt_zero One fixedOpen i j k W hi hj hk))
    exact (congrArg₂ (· + ·)
      (boundaryValue_extendOne fixedOpen b.2.1 i j k W hi hj hk)
      (faceAt_mapTwo fixedOpen functionDifferential b.2.2 i j k W hi hj hk).symm).trans hsum
  · intro i j W hi hj
    have he := congrArg (fun x : CycleQ2CechTwoToDerived.One Two fixedOpen =>
      edgeAt fixedOpen x i j W hi hj) h2
    have hsub := (edgeAt_sub Two fixedOpen (d0 Two fixedOpen b.1)
      (mapOne fixedOpen differential b.2.1) i j W hi hj).symm.trans he
    have hD := (congrArg (app differential W)
      (edgeValue_extendOne fixedOpen b.2.1 i j W hi hj)).trans
      (edgeAt_mapOne fixedOpen differential b.2.1 i j W hi hj).symm
    have hη := (congrArg (fun x => edgeValue Two fixedOpen x i j W hi hj)
      asAlternatingEdges.symm).trans (edgeValue_extendOne fixedOpen edges i j W hi hj)
    exact (congrArg₂ (· - ·) (edgeAt_d0 fixedOpen b.1 i j W hi hj).symm hD).trans
      (hsub.trans hη.symm)

end CycleQ2LiteralThreefoldUnfilteredCech

#print axioms CycleQ2LiteralThreefoldUnfilteredCech.testClass_ne_zero
#print axioms CycleQ2FourOpenDeRhamTotal.restrictVertex_eq_zero_iff
