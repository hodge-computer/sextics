import Proposal.GeometricLiteralThreefoldDeRhamTestClass
import Proposal.GeometricLiteralThreefoldExteriorDescentNative
import Proposal.GeometricLiteralThreefoldOrbitGauge

/-!
# The filtered Čech cohomology class of the fixed threefold

In filtration two the degree-two cochains consist of four vertex two-forms.
Their differential has the vertex exterior derivatives and the Čech differences
on the six increasing pairs. This defines the boundaries in the kernel of the
degree-three differential of the four-chart cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldFilteredCechQuotient

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldDeformedOverlap CycleQ2LiteralThreefoldHodgeCech
  CycleQ2LiteralThreefoldDeRhamTestClass CycleQ2LiteralThreefoldExteriorDerivative
  CycleQ2LiteralThreefoldExteriorDescentNative CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2GeometricSheafLocalIso
  CycleQ2ChartExteriorBinding CycleQ2LiteralThreefoldOrbitCech
  CycleQ2FiniteCechHOne CycleQ2FiniteInjectiveCech CycleQ2InjectiveCech
  CycleQ2LiteralThreefoldTestClass CycleQ2LiteralThreefoldTestEdges

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn
  sourceFixedAlgebra sourceFixedTower

abbrev TotalTwo := CycleQ2LiteralThreefoldOrbitGauge.VertexForms

attribute [local instance] CycleQ2LiteralThreefoldDeRhamTestClass.vertexGroup
  CycleQ2LiteralThreefoldDeRhamTestClass.nativeEdgeGroup
  CycleQ2LiteralThreefoldDeRhamTestClass.verticesGroup
  CycleQ2LiteralThreefoldDeRhamTestClass.nativeEdgesGroup
  CycleQ2LiteralThreefoldDeRhamTestClass.totalThreeGroup
local instance : AddCommGroup TotalTwo := inferInstance
local instance : AddCommGroup IncreasingThree := inferInstance
local instance : AddCommGroup IncreasingFour := inferInstance

/-- The Čech differential of a vertex two-form in the original overlap ring. -/
def edgeBoundary (v : TotalTwo) (i : Fin 4) (k : Fin 3) : NativeForms i k :=
  exteriorDifferentialMap (fixedTargetMap i k) 2 (v (i.succAbove k)) -
    exteriorDifferentialMap (sourceMap i k) 2 (v i)

/-- The degree-two differential with all orientations available for restriction. -/
def directedBoundary : TotalTwo →+ TotalThree where
  toFun v := (fun i => CycleQ2LiteralThreefoldExteriorDescent.differential (chartSeparated i) (v i),
    edgeBoundary v)
  map_zero' := by
    refine Prod.ext ?_ ?_
    · funext i
      exact (CycleQ2LiteralThreefoldExteriorDescent.differential (chartSeparated i)).map_zero
    · funext i k
      simp [edgeBoundary]
  map_add' v w := by
    refine Prod.ext ?_ ?_
    · funext i
      exact (CycleQ2LiteralThreefoldExteriorDescent.differential (chartSeparated i)).map_add _ _
    · funext i k
      change edgeBoundary (v+w) i k = edgeBoundary v i k + edgeBoundary w i k
      simp only [edgeBoundary, Pi.add_apply, map_add]
      abel

private theorem differential_in_frame {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (hA : CycleQ2LiteralThreefoldExteriorDescent.Separated A) (f : A →ₐ[ℂ] B)
    (g : B →ₐ[ℂ] C) (w : CycleQ2LiteralThreefoldCartan.Forms A 2)
    (e : Module.Basis (Fin 3) C (CycleQ2LiteralThreefoldCartan.OneForms C))
    (u : Fin 3 → C) (hu : ∀ r, e r = KaehlerDifferential.D ℂ C (u r)) :
    exteriorDifferentialMap (g.comp f) 3
      (CycleQ2LiteralThreefoldExteriorDescent.differential hA w) =
    additive e (exteriorDifferentialMap g 2 (exteriorDifferentialMap f 2 w)) :=
  (CycleQ2LiteralThreefoldExteriorDescent.differential_represents hA w C (g.comp f) e u hu).trans
    (congrArg (additive e) (CycleQ2LiteralThreefoldExteriorDescent.map_comp f g 2 w).symm)

private theorem pair_boundary (v : TotalTwo) (i : Fin 4) (k : Fin 3) (a b : Fin 4) :
    pairDifferential i k a b (directedBoundary v) = 0 := by
  let E := additive (basisOn i k a b)
  let u : Fin 3 → Ring i k a b := fun r => targetMap i k a b (coord (i.succAbove k) (b.succAbove r))
  have deriv (j : Fin 4) (f : T j →ₐ[ℂ] FixedOverlap i k) :
      exteriorDifferentialMap ((κ i k a b).comp f) 3
        (CycleQ2LiteralThreefoldExteriorDescent.differential (chartSeparated j) (v j)) =
      E (exteriorDifferentialMap (κ i k a b) 2 (exteriorDifferentialMap f 2 (v j))) :=
    differential_in_frame (chartSeparated j) f (κ i k a b) (v j)
      (basisOn i k a b) u (basisOn_apply i k a b)
  change _ - _ - E (exteriorDifferentialMap (κ i k a b) 2 (edgeBoundary v i k)) = 0
  apply sub_eq_zero.mpr
  have hm : E (exteriorDifferentialMap (κ i k a b) 2 (edgeBoundary v i k)) =
      E (exteriorDifferentialMap (κ i k a b) 2
        (exteriorDifferentialMap (fixedTargetMap i k) 2 (v (i.succAbove k)))) -
      E (exteriorDifferentialMap (κ i k a b) 2
        (exteriorDifferentialMap (sourceMap i k) 2 (v i))) :=
    (congrArg E ((exteriorDifferentialMap (κ i k a b) 2).map_sub _ _)).trans (E.map_sub _ _)
  exact (congrArg₂ (· - ·) (deriv (i.succAbove k) (fixedTargetMap i k))
    (deriv i (sourceMap i k))).trans hm.symm

private def vertexOn (v : TotalTwo) (i : Fin 4) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) : FormsOn W :=
  exteriorDifferentialMap (chartAlgebraMap i W hi) 2 (v i)

private theorem restrict_boundary (v : TotalTwo) (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    restrictNative i k W h (edgeBoundary v i k) =
      vertexOn v (i.succAbove k) W (h.trans inf_le_right) - vertexOn v i W (h.trans inf_le_left) := by
  unfold edgeBoundary restrictNative vertexOn
  change exteriorDifferentialMap (overlapAlgebraMap i k W h) 2
    (exteriorDifferentialMap (fixedTargetMap i k) 2 (v (i.succAbove k)) -
      exteriorDifferentialMap (sourceMap i k) 2 (v i)) = _
  rw [map_sub, CycleQ2LiteralThreefoldExteriorDescent.map_comp,
    CycleQ2LiteralThreefoldExteriorDescent.map_comp,
    overlapAlgebraMap_target, sourceMap, overlapAlgebraMap_source]


private theorem vertexOn_eq (v : TotalTwo) {i j : Fin 4} (e : i = j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    vertexOn v i W hi = vertexOn v j W hj := by
  cases e
  rfl

private theorem ordered_boundary (v : TotalTwo) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (h : W ≤ fixedOpen i ⊓ fixedOpen j) :
    edgeForm (edgeBoundary v) i j hij W h =
      vertexOn v j W (h.trans inf_le_right) - vertexOn v i W (h.trans inf_le_left) := by
  unfold edgeForm
  rw [restrict_boundary]
  exact congrArg₂ (· - ·) (vertexOn_eq v (succAbove_slot i j hij) W _ _) rfl

theorem directedBoundary_closed (v : TotalTwo) :
    CycleQ2LiteralThreefoldDeRhamTestClass.differential (directedBoundary v) = 0 := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i k a b
    exact pair_boundary v i k a b
  · funext t
    change edgeForm (edgeBoundary v) t.i t.j t.hij _ _ +
      edgeForm (edgeBoundary v) t.j t.k t.hjk _ _ -
      edgeForm (edgeBoundary v) t.i t.k (t.hij.trans t.hjk) _ _ = 0
    rw [ordered_boundary, ordered_boundary, ordered_boundary]
    abel

abbrev Cycles := increasingDifferential.ker

/-- The degree-two coboundary as a homomorphism into actual degree-three cycles. -/
def boundary : TotalTwo →+ Cycles where
  toFun v := ⟨increasingThree (directedBoundary v), by
    change increasingDifferential (increasingThree (directedBoundary v)) = 0
    exact (increasingDifferential_restrict (directedBoundary v)).trans
      ((congrArg increasingFour (directedBoundary_closed v)).trans increasingFour.map_zero)⟩
  map_zero' := Subtype.ext ((increasingThree.comp directedBoundary).map_zero)
  map_add' v w := Subtype.ext ((increasingThree.comp directedBoundary).map_add v w)

/-- Degree-three cohomology of the filtered Čech complex of this cover. -/
abbrev FilteredCechHThree := Cycles ⧸ boundary.range

def testClass : FilteredCechHThree := QuotientAddGroup.mk increasingTestCocycle

open CycleQ2FiniteCechOneAdditivity
open CycleQ2LiteralThreefoldOrbitGauge (vertexSection)

private theorem chart_over (i : Fin 4) :
    (fixedChart i).symm.inv ≫ (fixedOpen i).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i))) := by
  simpa only [Category.assoc, Iso.symm_inv, chartInclusion] using chartInclusion_overComplex i

private abbrev pairOpen (i : Fin 4) (k : Fin 3) :=
  fixedOpen i ⊓ fixedOpen (i.succAbove k)

private theorem overlap_over (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (pairOpen i k).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FixedOverlap i k))) := by
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, chartInclusion_overComplex,
    ← Spec.map_comp]
  rfl_cat

private theorem vertex_restrict (v : TotalTwo) (i : Fin 4) (k : Fin 3) (j : Fin 4)
    (h : pairOpen i k ≤ fixedOpen j) (f : T j →ₐ[ℂ] FixedOverlap i k)
    (hf : (overlapIso i k).hom ≫ (pairOpen i k).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ chartInclusion j) :
    res HodgeSheaf h (vertexSection v j) = overlapSection i k (pairOpen i k) le_rfl
      (exteriorDifferentialMap f 2 (v j)) := by
  calc
    _ = chartExteriorSheafSection (fixedChart j).symm structureMap (chart_over j)
        2 (Over.mk (homOfLE h)) (v j) :=
      chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 (fixedOpen j))) 2 _
    _ = _ := (chartExteriorSheafSection_differentialMap (fixedChart j).symm (overlapIso i k).symm
      h structureMap (chart_over j) (overlap_over i k) f hf (Over.mk (𝟙 (pairOpen i k))) 2 _).symm

private theorem boundarySection (v : TotalTwo) (i : Fin 4) (k : Fin 3)
    (W : Threefold.Opens) (h : W ≤ pairOpen i k) :
    overlapSection i k W h (edgeBoundary v i k) =
      res HodgeSheaf (h.trans inf_le_right) (vertexSection v (i.succAbove k)) -
      res HodgeSheaf (h.trans inf_le_left) (vertexSection v i) := by
  have hp : overlapSection i k (pairOpen i k) le_rfl (edgeBoundary v i k) =
      res HodgeSheaf inf_le_right (vertexSection v (i.succAbove k)) -
      res HodgeSheaf inf_le_left (vertexSection v i) := by
    let m := overlapSection i k (pairOpen i k) le_rfl
    have ht := vertex_restrict v i k (i.succAbove k) inf_le_right (fixedTargetMap i k)
      (overlapIso_hom_ι_target i k)
    have hs := vertex_restrict v i k i inf_le_left (sourceMap i k) (overlapIso_hom_ι i k)
    exact (m.map_sub _ _).trans (congrArg₂ (· - ·) ht.symm hs.symm)
  let r := res HodgeSheaf h
  have q := congrArg r hp
  have hl := overlapSection_restrict i k le_rfl h (edgeBoundary v i k)
  have he := r.map_sub
    (res HodgeSheaf inf_le_right (vertexSection v (i.succAbove k)))
    (res HodgeSheaf inf_le_left (vertexSection v i))
  exact hl.symm.trans (q.trans (he.trans (congrArg₂ (· - ·)
    (res_comp HodgeSheaf inf_le_right h _)
    (res_comp HodgeSheaf inf_le_left h _))))


private theorem vertexSection_eq (v : TotalTwo) {i j : Fin 4} (e : i = j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    res HodgeSheaf hi (vertexSection v i) = res HodgeSheaf hj (vertexSection v j) := by
  cases e
  rfl

private theorem edge_boundary (v : TotalTwo) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edge (edgeBoundary v) i j hij W (le_inf hi hj) =
      res HodgeSheaf hj (vertexSection v j) - res HodgeSheaf hi (vertexSection v i) := by
  unfold edge
  rw [boundarySection, vertexSection_eq v (succAbove_slot i j hij) W _ hj]

private def edges (c : Cycles) : NativeEdges := (extendThree c.1).2

private theorem faces (c : Cycles) (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    Face (edges c) i j k hij hjk := by
  have h : increasingDifferential c.1 = 0 := c.2
  exact sub_eq_zero.mp (congrArg (fun v : IncreasingFour => v.2.2 ⟨i,j,k,hij,hjk⟩) h)

private def sheafOne (c : Cycles) := (hodgeCocycle (edges c) (faces c)).val

private theorem sheafOne_closed (c : Cycles) : IsOneCocycle HodgeSheaf fixedOpen (sheafOne c) :=
  fun i j k W hi hj hk => ((hodgeCocycle (edges c) (faces c)).condition i j k W hi hj hk).symm

private theorem sheafOne_at (c : Cycles) (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edgeValue HodgeSheaf fixedOpen (sheafOne c) i j W hi hj =
      edge (edges c) i j hij W (le_inf hi hj) :=
  hodgeCocycle_edge_lt _ _ _ _ hij _ _ _

private theorem edge_extended (c : TotalThree) (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen j) :
    edge (extendThree (increasingThree c)).2 i j hij W h = edge c.2 i j hij W h := by
  unfold edge
  exact congrArg _ (extendThree_at c i (slot i j hij) (by simpa only [succAbove_slot] using hij))

private theorem edge_sum (c d : Cycles) (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen j) :
    edge (edges (c+d)) i j hij W h = edge (edges c) i j hij W h + edge (edges d) i j hij W h := by
  have e : edges (c+d) = edges c + edges d :=
    congrArg Prod.snd (extendThree.map_add c.1 d.1)
  rw [e]
  simp only [edge, Pi.add_apply, map_add]

private def edgeClass (c : Cycles) : Hodge21 := hodgeClass (edges c) (faces c)

private theorem edgeClass_add (c d : Cycles) : edgeClass (c+d) = edgeClass c + edgeClass d := by
  let C := oneCocycles (F := HodgeSheaf) fixedOpen
  have H := class_eq_of_vertex_corrections fixedOpen fixedOpen_cover
    (sheafOne c + sheafOne d) (sheafOne (c+d)) (C.add_mem (sheafOne_closed c) (sheafOne_closed d))
    (sheafOne_closed _) 0 (by
      intro i j hij W hi hj
      have hs : edgeValue HodgeSheaf fixedOpen (sheafOne c + sheafOne d) i j W hi hj =
          edgeValue HodgeSheaf fixedOpen (sheafOne c) i j W hi hj +
          edgeValue HodgeSheaf fixedOpen (sheafOne d) i j W hi hj :=
        (res HodgeSheaf (le_inf hi hj)).map_add _ _
      rw [hs, sheafOne_at c i j hij, sheafOne_at d i j hij, sheafOne_at (c+d) i j hij,
        edge_sum]
      simp)
  exact H.trans (cechOneClass_add fixedOpen fixedOpen_cover _ _ (sheafOne_closed c) (sheafOne_closed d))

def edgeClassHom : Cycles →+ Hodge21 := AddMonoidHom.mk' edgeClass edgeClass_add

theorem boundary_projects_zero (v : TotalTwo) : edgeClassHom (boundary v) = 0 := by
  let C := oneCocycles (F := HodgeSheaf) fixedOpen
  have H := class_eq_of_vertex_corrections fixedOpen fixedOpen_cover 0 (sheafOne (boundary v))
    C.zero_mem (sheafOne_closed _) (vertexSection v) (by
      intro i j hij W hi hj
      have h : edge (edges (boundary v)) i j hij W (le_inf hi hj) =
          edge (edgeBoundary v) i j hij W (le_inf hi hj) := edge_extended (directedBoundary v) _ _ _ _ _
      rw [sheafOne_at (boundary v) i j hij W hi hj, h, edge_boundary v i j hij W hi hj]
      simp only [edgeValue, Pi.zero_apply, map_zero, zero_add]
      abel)
  exact H.trans ((cechOneClassHom (F := HodgeSheaf) fixedOpen fixedOpen_cover).map_zero)

/-- Projection of the filtered cohomology class to the actual derived sheaf H¹ of two-forms. -/
def hodgeProjection : FilteredCechHThree →+ Hodge21 :=
  QuotientAddGroup.lift boundary.range edgeClassHom fun z hz => by
    obtain ⟨v, rfl⟩ := hz
    exact boundary_projects_zero v

theorem hodgeProjection_testClass : hodgeProjection testClass = ambientTestClass := by
  apply class_eq_of_vertex_corrections fixedOpen fixedOpen_cover (hodgeCocycle nativeEdge face).val
    (sheafOne increasingTestCocycle)
    (fun i j k W hi hj hk => ((hodgeCocycle nativeEdge face).condition i j k W hi hj hk).symm)
    (sheafOne_closed _) 0
  intro i j hij W hi hj
  rw [hodgeCocycle_edge_lt nativeEdge face i j hij, sheafOne_at _ i j hij]
  have e := edge_extended testCochain i j hij W (le_inf hi hj)
  change edge nativeEdge i j hij W _ + _ = _ + edge (extendThree (increasingThree testCochain)).2 _ _ _ _ _
  rw [e]
  simp [testCochain]

end CycleQ2LiteralThreefoldFilteredCechQuotient
end

#print axioms CycleQ2LiteralThreefoldFilteredCechQuotient.directedBoundary_closed
#print axioms CycleQ2LiteralThreefoldFilteredCechQuotient.testClass

#print axioms CycleQ2LiteralThreefoldFilteredCechQuotient.boundary_projects_zero
#print axioms CycleQ2LiteralThreefoldFilteredCechQuotient.hodgeProjection_testClass
