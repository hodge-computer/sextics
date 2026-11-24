import Proposal.GeometricLiteralNativeDifferentialSections

/-!
# The original Cartier dlog cocycle in the actual differential sheaf

The native inverse-ideal transitions give sections of the original
projective differential sheaf on the twelve-open cover. Their genuine
restriction laws and multiplicative cocycle prove the additive Chern
cocycle on every common subopen, including repeated Cartier indices.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeChernCocycle

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeCartierTransitions
  CycleQ2LiteralNativeTransitionNaturality CycleQ2LiteralNativeDifferentialSections
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricAffineOverlap
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeCupSectionValues

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

abbrev differentialAddSheaf := CycleQ2GeometricModuleLocalIso.addSheaf DifferentialSheaf

def nativeChernSection (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) : Sections differentialAddSheaf (closedOpen s) :=
  nativeFormToSheaf s hs (logDifferential (K := ℂ) (transition s u v hu hv))

theorem nativeChernSection_log (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) :
    nativeChernSection s hs u v hu hv =
      sheafLogDifferential (closedOpen s) (sectionUnit s hs (transition s u v hu hv)) :=
  nativeFormToSheaf_logDifferential s hs _

theorem nativeChernSection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    res differentialAddSheaf (closedOpen_mono hst) (nativeChernSection s hs u v hu hv) =
      nativeChernSection t ht u v (hst hu) (hst hv) := by
  change DifferentialSheaf.val.map (homOfLE (closedOpen_mono hst)).op
      (nativeFormToSheaf s hs _) = nativeFormToSheaf t ht _
  calc
    _ = nativeFormToSheaf t ht
        (differentialMap (closedRestrictionAlgHom hst)
          (logDifferential (K := ℂ) (transition s u v hu hv))) :=
      nativeFormToSheaf_restrict hst hs ht _
    _ = _ := by
      rw [differentialMap_logDifferential]
      change nativeFormToSheaf t ht (logDifferential (K := ℂ)
          (restrictClosedUnit hst (transition s u v hu hv))) = _
      rw [transition_restrict hst u v hu hv]

theorem nativeChernSection_cocycle (s : Finset Vertex) (hs : s.Nonempty) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    nativeChernSection s hs u w hu hw =
      nativeChernSection s hs u v hu hv + nativeChernSection s hs v w hv hw := by
  change nativeFormToSheaf s hs (logDifferential (K := ℂ) (transition s u w hu hw)) = _
  rw [← transition_cocycle s u v w hu hv hw, logDifferential_mul, map_add]
  rfl

def chernValue (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v) :
    Sections differentialAddSheaf W :=
  res differentialAddSheaf (common_le_pair u v W hu hv)
    (nativeChernSection {u,v} (by simp) u v (by simp) (by simp))

theorem chernValue_restrict (u v : Vertex) {W V : Surface.Opens} (hVW : V ≤ W)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    res differentialAddSheaf hVW (chernValue u v W hu hv) =
      chernValue u v V (hVW.trans hu) (hVW.trans hv) :=
  res_comp differentialAddSheaf _ _ _

theorem chernValue_common (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ closedOpen s)
    (hU : W ≤ cover u) (hV : W ≤ cover v) :
    chernValue u v W hU hV = res differentialAddSheaf hW (nativeChernSection s hs u v hu hv) := by
  have hpair : ({u,v} : Finset Vertex) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  rw [← nativeChernSection_restrict hpair (by simp) hs u v (by simp) (by simp)]
  exact (res_comp differentialAddSheaf _ _ _).symm

def chernOne : One differentialAddSheaf cover := fun u v =>
  chernValue u v (cover u ⊓ cover v) inf_le_left inf_le_right

theorem edgeValue_chernOne (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue differentialAddSheaf cover chernOne u v W hu hv = chernValue u v W hu hv :=
  chernValue_restrict u v (le_inf hu hv) inf_le_left inf_le_right

theorem chernOne_closed : IsOneCocycle differentialAddSheaf cover chernOne := by
  intro u v w W hu hv hw
  change edgeValue differentialAddSheaf cover chernOne u w W hu hw =
    edgeValue differentialAddSheaf cover chernOne u v W hu hv +
      edgeValue differentialAddSheaf cover chernOne v w W hv hw
  rw [edgeValue_chernOne, edgeValue_chernOne, edgeValue_chernOne,
    chernValue_common {u,v,w} (by simp) u w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    chernValue_common {u,v,w} (by simp) u v (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    chernValue_common {u,v,w} (by simp) v w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    nativeChernSection_cocycle, map_add]

def chernCocycle : CartierCechCoverTransfer.OneCocycle differentialAddSheaf cover where
  val := chernOne
  condition u v w W hu hv hw := (chernOne_closed u v w W hu hv hw).symm

end CycleQ2LiteralNativeChernCocycle

end

#print axioms CycleQ2LiteralNativeChernCocycle.nativeChernSection_restrict
#print axioms CycleQ2LiteralNativeChernCocycle.chernOne_closed
