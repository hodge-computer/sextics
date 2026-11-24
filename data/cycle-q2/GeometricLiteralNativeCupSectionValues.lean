import Proposal.GeometricLiteralGaugeAdjustedCohomology

/-!
# Actual section values of the native cup and the frame gauge

All values live in the original additive structure sheaf on common
opens. The actual native restriction laws identify pair gauge sections
with their values on the genuine triple intersection. On increasing
vertices the existing finite Cech gauge boundary is precisely the local
frameGaugeBoundary, with no antisymmetry imposed on raw native cups.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeCupSectionValues

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2CartierProjectiveCover CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeFrameGauge
  CycleQ2LiteralNativeCupFrameGauge CycleQ2LiteralNativeGaugeNaturality
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralCartierProjectionBinding

def intersectionValue (s : Finset Vertex) (hs : s.Nonempty) (W : Opens (projectiveSurface 57 1))
    (hW : W ≤ closedOpen s) : ClosedRing s →+ Sections coefficientSheaf W :=
  (res coefficientSheaf hW).comp (closedSectionsEquiv s hs).toAddEquiv.toAddMonoidHom

theorem intersectionValue_restrict {s t : Finset Vertex} (hst : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty)
    (W : Opens (projectiveSurface 57 1)) (hW : W ≤ closedOpen t) (x : ClosedRing s) :
    intersectionValue t ht W hW (closedRestriction hst x) =
      intersectionValue s hs W (hW.trans (closedOpen_mono hst)) x := by
  change res coefficientSheaf hW (closedSectionsEquiv t ht (closedRestriction hst x)) = _
  rw [← closedSectionsEquiv_restrict hs ht hst x]
  exact res_comp coefficientSheaf _ _ _

theorem rawGaugeValue_common (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Opens (projectiveSurface 57 1)) (hW : W ≤ closedOpen s)
    (hU : W ≤ cover u) (hV : W ≤ cover v) :
    rawGaugeValue u v W hU hV = intersectionValue s hs W hW (frameGauge s u v hu hv) := by
  have hpair : ({u,v} : Finset Vertex) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  rw [← frameGauge_restrict hpair u v (by simp) (by simp)]
  exact (intersectionValue_restrict hpair (by simp) hs W hW _).symm

theorem common_le_triple (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) : W ≤ closedOpen {u,v,w} := by
  rw [closedOpen_eq]
  refine le_iInf (fun x => le_iInf (fun hx => ?_))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hu
  · exact hv
  · exact hw

def nativeCupValue (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) : Sections coefficientSheaf W :=
  intersectionValue {u,v,w} (by simp) W (common_le_triple u v w W hu hv hw)
    (nativeCup {u,v,w} u v w (by simp) (by simp) (by simp))

def coneCupValue (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) : Sections coefficientSheaf W :=
  intersectionValue {u,v,w} (by simp) W (common_le_triple u v w W hu hv hw)
    (projectedConeCup {u,v,w} u v w (by simp) (by simp) (by simp))

def gaugeBoundaryValue (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) : Sections coefficientSheaf W :=
  intersectionValue {u,v,w} (by simp) W (common_le_triple u v w W hu hv hw)
    (frameGaugeBoundary {u,v,w} u v w (by simp) (by simp) (by simp))

theorem nativeCupValue_eq_cone_sub_boundary (u v w : Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    nativeCupValue u v w W hu hv hw = coneCupValue u v w W hu hv hw - gaugeBoundaryValue u v w W hu hv hw := by
  change intersectionValue _ _ _ _ (nativeCup _ _ _ _ _ _ _) = _
  rw [nativeCup_eq_projectedConeCup_sub_boundary, map_sub]
  rfl

theorem gaugeBoundaryValue_increasing (u v w : Vertex) (huv : rank u < rank v) (hvw : rank v < rank w)
    (W : Opens (projectiveSurface 57 1)) (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    boundaryValue coefficientSheaf cover gaugeOne u v w W hu hv hw = gaugeBoundaryValue u v w W hu hv hw := by
  have huw := lt_trans huv hvw
  unfold boundaryValue
  rw [edgeValue_gaugeOne, edgeValue_gaugeOne, edgeValue_gaugeOne,
    if_pos hvw, if_pos huw, if_pos huv]
  rw [rawGaugeValue_common {u,v,w} (by simp) v w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    rawGaugeValue_common {u,v,w} (by simp) u w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    rawGaugeValue_common {u,v,w} (by simp) u v (by simp) (by simp) W (common_le_triple u v w W hu hv hw)]
  change intersectionValue _ _ _ _ _ - intersectionValue _ _ _ _ _ + intersectionValue _ _ _ _ _ =
    intersectionValue {u,v,w} (by simp) W (common_le_triple u v w W hu hv hw)
      (frameGauge {u,v,w} v w (by simp) (by simp) - frameGauge {u,v,w} u w (by simp) (by simp) +
        frameGauge {u,v,w} u v (by simp) (by simp))
  rw [map_add, map_sub]

theorem intersectionValue_projectSection (s : Finset Vertex) (t : Finset (Fin 4))
    (ht : CycleQ2LiteralConeIntersectionTransport.Admits s t) (hs : s.Nonempty) (hnt : t.Nonempty)
    (W : Opens (projectiveSurface 57 1)) (hW : W ≤ closedOpen s)
    (x : CycleQ2LiteralConeIntersectionTransport.OldClosed t) :
    intersectionValue s hs W hW (CycleQ2LiteralProjectiveIntersectionProjection.closedProjection s
      (CycleQ2LiteralConeIntersectionTransport.closedMap s t ht x)) =
      res coefficientSheaf (hW.trans (closedOpen_le_coverPatch s t ht))
        (CycleQ2LiteralCartierProjectedCup.projectSection t hnt
          (CycleQ2LiteralCartierSplittings.closedRingEquiv t x)) := by
  change res coefficientSheaf hW (closedSectionsEquiv s hs _) = _
  rw [projectSection_closedMap s t ht hs hnt x]
  exact res_comp coefficientSheaf _ _ _

end CycleQ2LiteralNativeCupSectionValues

end

#print axioms CycleQ2LiteralNativeCupSectionValues.rawGaugeValue_common
#print axioms CycleQ2LiteralNativeCupSectionValues.gaugeBoundaryValue_increasing
#print axioms CycleQ2LiteralNativeCupSectionValues.intersectionValue_projectSection
