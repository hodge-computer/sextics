import Proposal.GeometricLiteralCartierProjectionBinding

/-!
# The actual frame-gauge edge cochain on the twelve-open cover

The values are sections of the original additive structure sheaf,
obtained from the actual native intersection rings. The original
coordinate frame gauge is used on increasing lexicographic vertex
pairs and extended with alternating signs. Its actual Cech boundary is
normalized and closed in the existing finite-cover complex.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeGaugeSections

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralNativeFrameGauge

abbrev coefficientSheaf := CycleQ2ProjectiveCartierIntersections.additiveSheaf 57 1

def cover (v : Vertex) : Opens (projectiveSurface 57 1) := refinedOpen 57 1 v.1 v.2

theorem cover_covers : (⨆ v : Vertex, cover v) = ⊤ := by
  change (⨆ v : Vertex, refinedOpen 57 1 v.1 v.2) = ⊤
  rw [iSup_prod]
  exact literal_refinedOpen_cover

theorem cover_first (v : Vertex) : cover v ≤ coverFamily 57 1 v.1 := by
  rw [cover, refinedOpen_eq]
  exact inf_le_left

def rank (v : Vertex) : ℕ := 3 * v.1.val + v.2.val

theorem rank_injective : Function.Injective rank := by
  intro u v huv
  have hu := u.2.isLt
  have hv := v.2.isLt
  dsimp only [rank] at huv
  have hfirst : u.1.val = v.1.val := by omega
  apply Prod.ext
  · exact Fin.ext hfirst
  · apply Fin.ext
    omega

theorem rank_first_mono {u v : Vertex} (h : rank u ≤ rank v) : u.1 ≤ v.1 := by
  have hu := u.2.isLt
  have hv := v.2.isLt
  change u.1.val ≤ v.1.val
  dsimp only [rank] at h
  omega

theorem common_le_pair (u v : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) : W ≤ closedOpen {u,v} := by
  rw [closedOpen_eq]
  refine le_iInf (fun x => le_iInf (fun hx => ?_))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hu
  · exact hv

def rawGaugeValue (u v : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) : Sections coefficientSheaf W :=
  res coefficientSheaf (common_le_pair u v W hu hv)
    (closedSectionsEquiv {u,v} (by simp) (frameGauge {u,v} u v (by simp) (by simp)))

theorem rawGaugeValue_restrict (u v : Vertex) {W V : Opens (projectiveSurface 57 1)}
    (hVW : V ≤ W) (hu : W ≤ cover u) (hv : W ≤ cover v) :
    res coefficientSheaf hVW (rawGaugeValue u v W hu hv) =
      rawGaugeValue u v V (hVW.trans hu) (hVW.trans hv) := res_comp coefficientSheaf _ _ _

def gaugeOne : One coefficientSheaf cover := fun u v =>
  if rank u < rank v then rawGaugeValue u v (cover u ⊓ cover v) inf_le_left inf_le_right
  else if rank v < rank u then -rawGaugeValue v u (cover u ⊓ cover v) inf_le_right inf_le_left
  else 0

theorem edgeValue_gaugeOne (u v : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue coefficientSheaf cover gaugeOne u v W hu hv =
      if rank u < rank v then rawGaugeValue u v W hu hv
      else if rank v < rank u then -rawGaugeValue v u W hv hu else 0 := by
  unfold edgeValue gaugeOne
  split_ifs
  · exact rawGaugeValue_restrict u v (le_inf hu hv) inf_le_left inf_le_right
  · rw [map_neg, rawGaugeValue_restrict]
  · exact map_zero _

theorem edgeValue_gaugeOne_self (u : Vertex) (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover u) :
    edgeValue coefficientSheaf cover gaugeOne u u W hu hu = 0 := by
  rw [edgeValue_gaugeOne]
  simp only [lt_self_iff_false, if_false]

theorem edgeValue_gaugeOne_reverse (u v : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue coefficientSheaf cover gaugeOne u v W hu hv =
      -edgeValue coefficientSheaf cover gaugeOne v u W hv hu := by
  rw [edgeValue_gaugeOne, edgeValue_gaugeOne]
  by_cases h : rank u < rank v
  · have hn : ¬ rank v < rank u := Nat.not_lt_of_ge (Nat.le_of_lt h)
    simp only [h, hn, if_true, if_false, neg_neg]
  · by_cases h' : rank v < rank u
    · simp only [h, h', if_true, if_false]
    · simp only [h, h', if_false, neg_zero]

def gaugeBoundary : Two coefficientSheaf cover := fun u v w =>
  boundaryValue coefficientSheaf cover gaugeOne u v w ((cover u ⊓ cover v) ⊓ cover w)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

theorem faceValue_gaugeBoundary (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    faceValue coefficientSheaf cover gaugeBoundary u v w W hu hv hw =
      boundaryValue coefficientSheaf cover gaugeOne u v w W hu hv hw := by
  unfold faceValue gaugeBoundary boundaryValue edgeValue
  simp only [map_add, map_sub, res_comp]

theorem gaugeBoundary_normalized : NormalizedTwo coefficientSheaf cover gaugeBoundary where
  repeat12 u w W hu hw := by
    rw [faceValue_gaugeBoundary]
    unfold boundaryValue
    rw [edgeValue_gaugeOne_self]
    abel
  repeat23 u v W hu hv := by
    rw [faceValue_gaugeBoundary]
    unfold boundaryValue
    rw [edgeValue_gaugeOne_self]
    abel
  swap12 u v w W hu hv hw := by
    rw [faceValue_gaugeBoundary, faceValue_gaugeBoundary]
    unfold boundaryValue
    rw [edgeValue_gaugeOne_reverse u v W hu hv]
    abel
  swap23 u v w W hu hv hw := by
    rw [faceValue_gaugeBoundary, faceValue_gaugeBoundary]
    unfold boundaryValue
    rw [edgeValue_gaugeOne_reverse v w W hv hw]
    abel

theorem gaugeBoundary_closed : IsTwoCocycle coefficientSheaf cover gaugeBoundary := by
  intro u v w z W hu hv hw hz
  simp only [faceValue_gaugeBoundary, boundaryValue]
  abel

end CycleQ2LiteralNativeGaugeSections

end

#print axioms CycleQ2LiteralNativeGaugeSections.gaugeBoundary_normalized
#print axioms CycleQ2LiteralNativeGaugeSections.gaugeBoundary_closed
