import Proposal.GeometricLiteralThreefoldOrbitCech
import Proposal.GeometricLiteralThreefoldTestGauge

/-!
# Chart corrections for the Čech class of the threefold test

A correction two-form on each affine chart gives an actual vertex section.
The native edge equalities then compare classes in the exterior-square
cotangent sheaf of the projective threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldOrbitGauge

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechHOne CycleQ2GeometricAffineChartSections
  CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldTestClass CycleQ2LiteralThreefoldTestGauge
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldOverlapAtlas
  CycleQ2LiteralThreefoldOrbitCech CycleQ2ThreefoldContractionAlongMap

attribute [local instance] sourceFixedAlgebra sourceFixedTower

local instance sheafHasExt (S : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

private theorem chart_complex (j : Fin 4) :
    (fixedChart j).symm.inv ≫ (fixedOpen j).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T j))) := by
  simpa only [Iso.symm_inv, chartInclusion, Category.assoc] using chartInclusion_overComplex j

private theorem overlap_complex (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FixedOverlap i k))) := by
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, chartInclusion_overComplex, ← Spec.map_comp]
  rfl_cat

abbrev VertexForms := ∀ i : Fin 4, Forms (T i) 2

def vertexSection (v : VertexForms) (i : Fin 4) : HodgeSheaf.obj.obj (op (fixedOpen i)) :=
  chartExteriorSheafSection (fixedChart i).symm structureMap (chart_complex i)
    2 (Over.mk (𝟙 (fixedOpen i))) (v i)

private abbrev pair (i : Fin 4) (k : Fin 3) := fixedOpen i ⊓ fixedOpen (i.succAbove k)

private theorem vertexSection_restrict (v : VertexForms) (i : Fin 4) (k : Fin 3) (j : Fin 4)
    (h : pair i k ≤ fixedOpen j) (f : T j →ₐ[ℂ] FixedOverlap i k)
    (hf : (overlapIso i k).hom ≫ (pair i k).ι =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ chartInclusion j) :
    res HodgeSheaf h (vertexSection v j) =
      overlapSection i k (pair i k) le_rfl (exteriorDifferentialMap f 2 (v j)) := by
  calc
    _ = chartExteriorSheafSection (fixedChart j).symm structureMap (chart_complex j)
        2 (Over.mk (homOfLE h)) (v j) :=
      chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 (fixedOpen j))) 2 _
    _ = _ := (chartExteriorSheafSection_differentialMap (fixedChart j).symm (overlapIso i k).symm
      h structureMap (chart_complex j) (overlap_complex i k) f hf (Over.mk (𝟙 (pair i k))) 2 _).symm

/-- This equation is tested in the degree-two exterior power of the actual
ring of a projective overlap. -/
def NativeComparison (v : VertexForms) (ω : NativeEdges) (i : Fin 4) (k : Fin 3) : Prop :=
  nativeEdge i k + exteriorDifferentialMap (fixedTargetMap i k) 2 (v (i.succAbove k)) =
    exteriorDifferentialMap (sourceMap i k) 2 (v i) + ω i k

/-- The discrepancy between the original Bézout splitting and another
splitting over the same affine chart. -/
def vertexOfLift (l : ∀ i, Lift i (T i)) (hl : ∀ i, LiesOver (l i) (AlgHom.id ℂ _)) :
    VertexForms := fun i => value (canonical i (AlgHom.id ℂ _)) (l i)
      (fun a => (canonical_fst i _ a).trans (hl i a).symm)

theorem mapped_liesOver {S : Type} [CommRing S] [Algebra ℂ S] {i : Fin 4}
    (l : Lift i (T i)) (hl : LiesOver l (AlgHom.id ℂ _)) (f : T i →ₐ[ℂ] S) :
    LiesOver (mapLift f l) f := fun a => congrArg f (hl a)

private theorem vertexOfLift_map {S : Type} [CommRing S] [Algebra ℂ S]
    (l : ∀ i, Lift i (T i)) (hl : ∀ i, LiesOver (l i) (AlgHom.id ℂ _))
    (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    exteriorDifferentialMap f 2 (vertexOfLift l hl i) =
      value (canonical i f) (mapLift f (l i))
        (fun a => (canonical_fst i f a).trans (mapped_liesOver (l i) (hl i) f a).symm) := by
  exact value_map (canonical i (AlgHom.id ℂ _)) (l i) _ f

/-- Identify a transformed edge by its normalized source lift and its target
lift. The two actual vertex corrections then give its native comparison. -/
theorem nativeComparison_of_lifts
    (l : ∀ i, Lift i (T i)) (hl : ∀ i, LiesOver (l i) (AlgHom.id ℂ _))
    (ω : NativeEdges) (i : Fin 4) (k : Fin 3)
    (z : Lift (i.succAbove k) (FixedOverlap i k))
    (hn : Normalizes (mapLift (sourceMap i k) (l i)) z)
    (hz : LiesOver z (fixedTargetMap i k))
    (hω : value z (mapLift (fixedTargetMap i k) (l (i.succAbove k)))
      (fun a => (hz a).trans (mapped_liesOver _ (hl _) _ a).symm) = ω i k) :
    NativeComparison (vertexOfLift l hl) ω i k := by
  let xt := mapLift (fixedTargetMap i k) (l (i.succAbove k))
  let xs := mapLift (sourceMap i k) (l i)
  have ht := vertexOfLift_map l hl (i.succAbove k) (fixedTargetMap i k)
  have hs := vertexOfLift_map l hl i (sourceMap i k)
  have hc := nativeEdge_change_of_lifts i k (AlgHom.id ℂ _) xs z xt hn
    (mapped_liesOver (l i) (hl i) (sourceMap i k)) hz
    (mapped_liesOver (l (i.succAbove k)) (hl (i.succAbove k)) (fixedTargetMap i k))
  exact (congrArg (fun a => nativeEdge i k + a) ht).trans
    (hc.trans (congrArg₂ (· + ·) hs.symm hω))

private theorem compare_at_pair (v : VertexForms) (ω : NativeEdges)
    (i : Fin 4) (k : Fin 3) (h : NativeComparison v ω i k) :
    overlapSection i k (pair i k) le_rfl (nativeEdge i k) +
      res HodgeSheaf inf_le_right (vertexSection v (i.succAbove k)) =
    res HodgeSheaf inf_le_left (vertexSection v i) + overlapSection i k (pair i k) le_rfl (ω i k) := by
  let m := overlapSection i k (pair i k) le_rfl
  have ht := vertexSection_restrict v i k (i.succAbove k) inf_le_right
    (fixedTargetMap i k) (overlapIso_hom_ι_target i k)
  have hs := vertexSection_restrict v i k i inf_le_left (sourceMap i k) (overlapIso_hom_ι i k)
  exact (congrArg (fun a => m (nativeEdge i k) + a) ht).trans
    ((map_add m _ _).symm.trans ((congrArg m h).trans
      ((map_add m _ _).trans (congrArg (fun a => a + m (ω i k)) hs.symm))))

private theorem compare_on (v : VertexForms) (ω : NativeEdges)
    (i : Fin 4) (k : Fin 3) (h : NativeComparison v ω i k)
    (W : Threefold.Opens) (hW : W ≤ pair i k) :
    overlapSection i k W hW (nativeEdge i k) +
      res HodgeSheaf (hW.trans inf_le_right) (vertexSection v (i.succAbove k)) =
    res HodgeSheaf (hW.trans inf_le_left) (vertexSection v i) +
      overlapSection i k W hW (ω i k) := by
  have e := congrArg (res HodgeSheaf hW) (compare_at_pair v ω i k h)
  simpa only [map_add, res_comp, overlapSection_restrict] using e

private theorem vertex_eq (v : VertexForms) {a b : Fin 4} (hab : a = b) (W : Threefold.Opens)
    (ha : W ≤ fixedOpen a) (hb : W ≤ fixedOpen b) :
    res HodgeSheaf ha (vertexSection v a) = res HodgeSheaf hb (vertexSection v b) := by
  cases hab
  rfl

private theorem compare_at_ordered_pair (v : VertexForms) (ω : NativeEdges)
    (h : ∀ i k, NativeComparison v ω i k) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    edge nativeEdge i j hij W (le_inf hi hj) + res HodgeSheaf hj (vertexSection v j) =
    res HodgeSheaf hi (vertexSection v i) + edge ω i j hij W (le_inf hi hj) := by
  let k := slot i j hij
  have hk : i.succAbove k = j := succAbove_slot i j hij
  have ht : W ≤ fixedOpen (i.succAbove k) := hk.symm ▸ hj
  have hW : W ≤ pair i k := le_inf hi ht
  exact (congrArg (fun t => overlapSection i k W hW (nativeEdge i k) + t)
    (vertex_eq v hk W ht hj).symm).trans (compare_on v ω i k (h i k) W hW)

theorem class_eq_ambientTestClass (v : VertexForms) (ω : NativeEdges)
    (h : ∀ i k, NativeComparison v ω i k)
    (d : One HodgeSheaf fixedOpen) (hd : IsOneCocycle HodgeSheaf fixedOpen d)
    (he : ∀ i j (hij : i < j), d i j = edge ω i j hij _ le_rfl) :
    cechOneClass fixedOpen fixedOpen_cover d hd = ambientTestClass := by
  apply class_eq_of_vertex_corrections fixedOpen fixedOpen_cover (hodgeCocycle nativeEdge face).val d
    (fun i j k W hi hj hk => ((hodgeCocycle nativeEdge face).condition i j k W hi hj hk).symm) hd (vertexSection v)
  intro i j hij W hi hj
  rw [hodgeCocycle_edge_lt nativeEdge face i j hij W hi hj]
  change _ = _ + res HodgeSheaf (le_inf hi hj) (d i j)
  rw [he i j hij, edge_restrict]
  exact compare_at_ordered_pair v ω h i j hij W hi hj

end CycleQ2LiteralThreefoldOrbitGauge
end

#print axioms CycleQ2LiteralThreefoldOrbitGauge.class_eq_ambientTestClass
