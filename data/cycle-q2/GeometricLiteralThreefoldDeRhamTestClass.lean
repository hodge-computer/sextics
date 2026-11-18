import Proposal.GeometricLiteralThreefoldDeformedCocycle
import Proposal.GeometricLiteralThreefoldTestClass

/-!
# A filtered Čech–de Rham cocycle of total degree three

The vertex three-forms and the ordered overlap two-forms have total degree three
in the truncation beginning with two-forms. With total differential
`δ + (-1)^p d` in Čech degree `p`, the pair component is the target restriction
minus the source restriction minus the exterior derivative of the edge.
The triangle component uses the increasing triples of the four-chart cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldDeRhamTestClass

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldDeformedOverlap CycleQ2LiteralThreefoldDeformedCocycle
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldTestClass CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldExteriorDerivative

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn

abbrev Vertices := ∀ i : Fin 4, CycleQ2LiteralThreefoldCartan.Forms (T i) 3
abbrev TotalThree := Vertices × NativeEdges

local instance vertexGroup (i : Fin 4) : AddCommGroup (CycleQ2LiteralThreefoldCartan.Forms (T i) 3) := inferInstance
local instance nativeEdgeGroup (i : Fin 4) (k : Fin 3) : AddCommGroup (NativeForms i k) := inferInstance
local instance verticesGroup : AddCommGroup Vertices := inferInstance
local instance nativeEdgesGroup : AddCommGroup NativeEdges := inferInstance
local instance totalThreeGroup : AddCommGroup TotalThree := inferInstance
abbrev VertexFour := ∀ (i a : Fin 4), CycleQ2LiteralThreefoldCartan.Forms (Patch i a) 4
abbrev PairThree := ∀ (i : Fin 4) (k : Fin 3) (a b : Fin 4),
  CycleQ2LiteralThreefoldCartan.Forms (CycleQ2LiteralThreefoldDeformedOverlap.Ring i k a b) 3
structure Triangle where
  i : Fin 4
  j : Fin 4
  k : Fin 4
  hij : i < j
  hjk : j < k

abbrev TripleTwo := ∀ t : Triangle, FormsOn (Triple t.i t.j t.k)
abbrev TotalFour := VertexFour × PairThree × TripleTwo

local instance : AddCommGroup VertexFour := inferInstance
local instance : AddCommGroup PairThree := inferInstance
local instance : AddCommGroup TripleTwo := inferInstance
local instance : AddCommGroup TotalFour := inferInstance

/-- The cotangent frame on each gradient open has three elements, so its fourth
exterior power vanishes. -/
theorem vertexFour_subsingleton (i a : Fin 4) :
    Subsingleton (CycleQ2LiteralThreefoldCartan.Forms (Patch i a) 4) := by
  constructor
  intro x y
  apply ((basis i a).exteriorPower 4).repr.injective
  ext s
  have h := Finset.card_le_univ s.1
  simp at h

/-- The family of common gradient localizations used to test the pair
component covers the entire spectrum of the original overlap ring. -/
theorem pair_cover (i : Fin 4) (k : Fin 3) :
    (⨆ a, ⨆ b, PrimeSpectrum.basicOpen (denominator i k a b)) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨a, b, h⟩ := denominator_cover i k p
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, TopologicalSpace.Opens.mem_iSup.mpr ⟨b, h⟩⟩

/-- The mixed Čech and exterior differential on each common gradient open. -/
def pairDifferential (i : Fin 4) (k : Fin 3) (a b : Fin 4) :
    TotalThree →+ CycleQ2LiteralThreefoldCartan.Forms
      (CycleQ2LiteralThreefoldDeformedOverlap.Ring i k a b) 3 where
  toFun c :=
    exteriorDifferentialMap ((κ i k a b).comp (fixedTargetMap i k)) 3 (c.1 (i.succAbove k)) -
    exteriorDifferentialMap ((κ i k a b).comp (sourceMap i k)) 3 (c.1 i) -
    additive (basisOn i k a b) (exteriorDifferentialMap (κ i k a b) 2 (c.2 i k))
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; abel

/-- The alternating sum of the restricted two-forms in the actual triple-open
section ring. -/
def triangleDifferential (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    NativeEdges →+ FormsOn (Triple i j k) where
  toFun ω :=
    edgeForm ω i j hij _ inf_le_left +
    edgeForm ω j k hjk _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) -
    edgeForm ω i k (hij.trans hjk) _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  map_zero' := by simp [edgeForm]
  map_add' x y := by simp only [edgeForm, Pi.add_apply, map_add]; abel

/-- The degree-three differential of the filtered complex, evaluated on the
gradient covers of vertices and pairs. The vertex target is zero by
`vertexFour_subsingleton`. -/
def differential : TotalThree →+ TotalFour where
  toFun c := (0, fun i k a b => pairDifferential i k a b c,
    fun t => triangleDifferential t.i t.j t.k t.hij t.hjk c.2)
  map_zero' := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i k a b
      exact (pairDifferential i k a b).map_zero
    · funext t
      exact (triangleDifferential t.i t.j t.k t.hij t.hjk).map_zero
  map_add' x y := by
    refine Prod.ext (zero_add _).symm (Prod.ext ?_ ?_)
    · funext i k a b
      exact (pairDifferential i k a b).map_add x y
    · funext t
      exact (triangleDifferential t.i t.j t.k t.hij t.hjk).map_add x.2 y.2

/-- The sign on the vertex form uses the chosen total differential. -/
def testCochain : TotalThree := (fun i => -chartThreeForm i, nativeEdge)

private theorem pair_sign {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ C) (g : B →+ C) (x : A) (y : B) (z : C) (h : f x - g y = z) :
    g (-y) - f (-x) - z = 0 := by rw [map_neg, map_neg, neg_sub_neg, h, sub_self]

theorem testCochain_closed : differential testCochain = 0 := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i k a b
    exact pair_sign
      (exteriorDifferentialMap ((κ i k a b).comp (sourceMap i k)) 3).toAddMonoidHom
      (exteriorDifferentialMap ((κ i k a b).comp (fixedTargetMap i k)) 3).toAddMonoidHom
      _ _ _ (pair_patch i k a b)
  · funext t
    exact sub_eq_zero.mpr (face t.i t.j t.k t.hij t.hjk)

/-- The actual degree-three element in the kernel of the total differential. -/
def testCocycle : differential.ker := ⟨testCochain, testCochain_closed⟩

/-- The alternating Čech convention keeps the six increasing edges. -/
structure IncreasingEdge where
  i : Fin 4
  k : Fin 3
  inc : i < i.succAbove k

abbrev IncreasingEdges := ∀ e : IncreasingEdge, NativeForms e.i e.k
abbrev IncreasingThree := Vertices × IncreasingEdges
local instance increasingEdgesGroup : AddCommGroup IncreasingEdges := inferInstance
local instance increasingThreeGroup : AddCommGroup IncreasingThree := inferInstance
abbrev IncreasingPairThree :=
  ∀ (e : IncreasingEdge) (a b : Fin 4),
    CycleQ2LiteralThreefoldCartan.Forms (CycleQ2LiteralThreefoldDeformedOverlap.Ring e.i e.k a b) 3
abbrev IncreasingFour := VertexFour × IncreasingPairThree × TripleTwo

local instance : AddCommGroup IncreasingPairThree := inferInstance
local instance : AddCommGroup IncreasingFour := inferInstance

def increasingThree : TotalThree →+ IncreasingThree where
  toFun c := (c.1, fun e => c.2 e.i e.k)
  map_zero' := rfl
  map_add' _ _ := rfl

private def extendAt (i : Fin 4) (k : Fin 3) : IncreasingThree →+ NativeForms i k :=
  if h : i < i.succAbove k then
    { toFun := fun c => c.2 ⟨i, k, h⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  else 0

/-- Extend a cochain on the six increasing pairs by zero on the unused orientations. -/
def extendThree : IncreasingThree →+ TotalThree where
  toFun c := (c.1, fun i k => extendAt i k c)
  map_zero' := Prod.ext rfl (funext fun i => funext fun k => (extendAt i k).map_zero)
  map_add' x y := Prod.ext rfl (funext fun i => funext fun k => (extendAt i k).map_add x y)

theorem extendThree_at (c : TotalThree) (i : Fin 4) (k : Fin 3) (h : i < i.succAbove k) :
    (extendThree (increasingThree c)).2 i k = c.2 i k := by
  change extendAt i k (increasingThree c) = c.2 i k
  simp [extendAt, h, increasingThree]

def increasingFour : TotalFour →+ IncreasingFour where
  toFun c := (c.1, fun e a b => c.2.1 e.i e.k a b, c.2.2)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The degree-three differential on the increasing-index Čech complex. -/
def increasingDifferential : IncreasingThree →+ IncreasingFour :=
  increasingFour.comp (differential.comp extendThree)

private theorem pair_extend (c : TotalThree) (i : Fin 4) (k : Fin 3)
    (h : i < i.succAbove k) (a b : Fin 4) :
    pairDifferential i k a b (extendThree (increasingThree c)) = pairDifferential i k a b c := by
  apply congrArg (fun z => exteriorDifferentialMap ((κ i k a b).comp (fixedTargetMap i k)) 3
    (c.1 (i.succAbove k)) - exteriorDifferentialMap ((κ i k a b).comp (sourceMap i k)) 3 (c.1 i) -
    additive (basisOn i k a b) (exteriorDifferentialMap (κ i k a b) 2 z))
  exact extendThree_at c i k h

private theorem edgeForm_extend (c : TotalThree) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (h : W ≤ CycleQ2LiteralAmbientCharts.fixedOpen i ⊓
        CycleQ2LiteralAmbientCharts.fixedOpen j) :
    edgeForm (extendThree (increasingThree c)).2 i j hij W h = edgeForm c.2 i j hij W h := by
  unfold edgeForm
  exact congrArg _ (extendThree_at c i (slot i j hij) (by simpa only [succAbove_slot] using hij))

private theorem triangle_extend (c : TotalThree) (t : Triangle) :
    triangleDifferential t.i t.j t.k t.hij t.hjk (extendThree (increasingThree c)).2 =
      triangleDifferential t.i t.j t.k t.hij t.hjk c.2 := by
  exact congrArg₂ (· - ·) (congrArg₂ (· + ·) (edgeForm_extend c t.i t.j t.hij _ _)
    (edgeForm_extend c t.j t.k t.hjk _ _)) (edgeForm_extend c t.i t.k (t.hij.trans t.hjk) _ _)

private def nativeFour (c : TotalThree) : IncreasingFour :=
  (0, fun e a b => pairDifferential e.i e.k a b c,
    fun t => triangleDifferential t.i t.j t.k t.hij t.hjk c.2)

private theorem restrict_differential (c : TotalThree) :
    increasingFour (differential c) = nativeFour c := rfl

private theorem increasing_differential (c : IncreasingThree) :
    increasingDifferential c = nativeFour (extendThree c) := rfl

private theorem nativeFour_extend (c : TotalThree) :
    nativeFour (extendThree (increasingThree c)) = nativeFour c :=
  Prod.ext rfl (Prod.ext (funext fun e => funext fun a => funext fun b => pair_extend c e.i e.k e.inc a b)
    (funext fun t => triangle_extend c t))

theorem increasingDifferential_restrict (c : TotalThree) :
    increasingDifferential (increasingThree c) = increasingFour (differential c) :=
  (increasing_differential (increasingThree c)).trans
    ((nativeFour_extend c).trans (restrict_differential c).symm)

/-- The six increasing edges and four vertex forms give a cocycle in the
ordinary increasing-index Čech convention. -/
def increasingTestCocycle : increasingDifferential.ker :=
  ⟨increasingThree testCochain, (increasingDifferential_restrict testCochain).trans
    ((congrArg increasingFour testCochain_closed).trans increasingFour.map_zero)⟩

theorem faces_of_closed (c : differential.ker) (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    Face c.1.2 i j k hij hjk := by
  have h : differential c.1 = 0 := c.2
  exact sub_eq_zero.mp (congrArg (fun v : TotalFour => v.2.2 ⟨i, j, k, hij, hjk⟩) h)

/-- The edge of a filtered total cocycle defines a class in the derived
sheaf group H¹ of the exterior square of the cotangent sheaf. -/
def hodgeComponent (c : differential.ker) : Hodge21 :=
  hodgeClass c.1.2 (faces_of_closed c)

theorem hodgeComponent_testCocycle :
    hodgeComponent testCocycle = ambientTestClass := rfl

end CycleQ2LiteralThreefoldDeRhamTestClass
end

#print axioms CycleQ2LiteralThreefoldDeRhamTestClass.vertexFour_subsingleton
#print axioms CycleQ2LiteralThreefoldDeRhamTestClass.pair_cover
#print axioms CycleQ2LiteralThreefoldDeRhamTestClass.testCocycle
#print axioms CycleQ2LiteralThreefoldDeRhamTestClass.increasingTestCocycle
#print axioms CycleQ2LiteralThreefoldDeRhamTestClass.hodgeComponent_testCocycle
