import Proposal.GeometricLiteralThreefoldTestEdges
import Proposal.GeometricLiteralThreefoldTriangleLifts
import Proposal.GeometricLiteralThreefoldHodgeCech

/-!
# The Hodge class of the actual weighted-sextic test deformation

The edge on a pair of charts is the tangent from their two lifts evaluated
against the regular threefold volume. A third chart carries both lifts to a
common normalization, where the three differences add. The resulting four
face identities give a class in the actual first sheaf cohomology of two-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTestClass

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldHodgeCech
  CycleQ2ThreefoldContractionAlongMap CycleQ2LiteralAmbientCharts

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn

variable {S : Type} [CommRing S] [Algebra ℂ S]

theorem value_normalizes {i j : Fin 4} (hij : i ≠ j)
    {x y : Lift i S} {x' y' : Lift j S} (hx : Normalizes x x') (hy : Normalizes y y')
    (h : ∀ a, (x.x a).fst = (y.x a).fst) (h' : ∀ a, (x'.x a).fst = (y'.x a).fst) :
    value x' y' h' = value x y h := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hij.symm
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  exact value_change i k x y h u v hu hv h'

private def Represents {i j : Fin 4} (f : T i →ₐ[ℂ] S) (g : T j →ₐ[ℂ] S)
    (e : Forms S 2) : Prop :=
  ∃ (x : Lift j S) (_ : Normalizes (canonical i f) x)
    (h : ∀ a, (x.x a).fst = ((canonical j g).x a).fst), e = value x (canonical j g) h

private theorem represents_triangle {i j k : Fin 4} (hjk : j ≠ k)
    {f : T i →ₐ[ℂ] S} {g : T j →ₐ[ℂ] S} {h : T k →ₐ[ℂ] S}
    {a b c : Forms S 2} (hab : Represents f g a) (hbc : Represents g h b)
    (hac : Represents f h c) : a + b = c := by
  obtain ⟨x,hx,h₁,rfl⟩ := hab
  obtain ⟨y,hy,h₂,rfl⟩ := hbc
  obtain ⟨z,hz,h₃,rfl⟩ := hac
  have hzy (t : Index) : (z.x t).fst = (y.x t).fst := (h₃ t).trans (h₂ t).symm
  rw [← value_normalizes hjk (normalizes_common_source hx hz) hy h₁ hzy]
  exact (value_cocycle z y (canonical k h) hzy h₂).symm

private theorem represents_native (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    Represents (chartAlgebraMap i W (h.trans inf_le_left))
      (chartAlgebraMap (i.succAbove k) W (h.trans inf_le_right))
      (restrictNative i k W h (nativeEdge i k)) := by
  let ρ := overlapAlgebraMap i k W h
  have hs := overlapAlgebraMap_source i k W h
  have ht := overlapAlgebraMap_target i k W h
  change Represents _ _ (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap ρ 2 (nativeEdge i k))
  rw [nativeEdge_restrict, ← hs, ← ht]
  exact ⟨normalizedLift i k ρ, normalizedLift_normalizes i k ρ, normalizedLift_fst i k ρ, rfl⟩

private theorem represents_change_index {i l j : Fin 4} (W : Threefold.Opens) (hi : W ≤ fixedOpen i)
    (hl : W ≤ fixedOpen l) (hj : W ≤ fixedOpen j) (e : FormsOn W) (hlj : l = j)
    (h : Represents (i := i) (j := l) (chartAlgebraMap i W hi) (chartAlgebraMap l W hl) e) :
    Represents (i := i) (j := j) (chartAlgebraMap i W hi) (chartAlgebraMap j W hj) e := by
  subst j
  exact h

private theorem represents_edge (i j : Fin 4) (hij : i < j) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) :
    Represents (S := RingOn W) (i := i) (j := j) (chartAlgebraMap i W hi) (chartAlgebraMap j W hj)
      (edgeForm nativeEdge i j hij W (le_inf hi hj)) := by
  let k := slot i j hij
  have hk : i.succAbove k = j := succAbove_slot i j hij
  have h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k) := by rw [hk]; exact le_inf hi hj
  exact represents_change_index W hi (h.trans inf_le_right) hj
    (restrictNative i k W h (nativeEdge i k)) hk (represents_native i k W h)

/-- The edge forms from the four actual Bézout lifts satisfy each genuine face equation. -/
theorem face (i j k : Fin 4) (hij : i < j) (hjk : j < k) :
    Face nativeEdge i j k hij hjk := by
  let W := Triple i j k
  have hi : W ≤ fixedOpen i := inf_le_left.trans inf_le_left
  have hj : W ≤ fixedOpen j := inf_le_left.trans inf_le_right
  have hk : W ≤ fixedOpen k := inf_le_right
  exact represents_triangle (S := RingOn W) (i := i) (j := j) (k := k) (ne_of_lt hjk)
    (represents_edge i j hij W hi hj) (represents_edge j k hjk W hj hk)
    (represents_edge i k (hij.trans hjk) W hi hk)

/-- The degree (2,1) coherent Hodge class on the smooth proper literal threefold. -/
def ambientTestClass : Hodge21 := hodgeClass nativeEdge face

end CycleQ2LiteralThreefoldTestClass
end

#print axioms CycleQ2LiteralThreefoldTestClass.face
#print axioms CycleQ2LiteralThreefoldTestClass.ambientTestClass
