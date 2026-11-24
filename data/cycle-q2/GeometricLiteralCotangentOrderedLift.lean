import Proposal.GeometricLiteralNativeCotangent
import Proposal.GeometricLiteralNativeChernCocycle

/-!
# Alternating lifts of the actual native Chern edges

On every original finite intersection, choose the cotangent splitting of
the lower-ranked end of an edge and extend by the alternating sign. Its
reduction is the original Chern dlog for either orientation. Its boundary
is the epsilon inclusion of the ordered original cup, including repeated
vertices.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentOrderedLift

open scoped TensorProduct
open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeCartierTransitions
  CycleQ2LiteralNativeTransitionNaturality CycleQ2LiteralNativeCupFrameGauge
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeCotangent
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroReducedCotangent
  CycleQ2GeometricAffineOverlap

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

section Alternation

variable {I A B : Type*} [AddCommGroup A] [AddCommGroup B]
  (ord : I → ℕ)

private def orderEdge (b : I → I → A) (u v : I) : A :=
  if ord u < ord v then b u v else if ord v < ord u then -b v u else 0

private def orderFace (c : I → I → I → B) (u v w : I) : B :=
  if ord u < ord v ∧ ord v < ord w then c u v w
  else if ord u < ord w ∧ ord w < ord v then -c u w v
  else if ord v < ord u ∧ ord u < ord w then -c v u w
  else if ord v < ord w ∧ ord w < ord u then c v w u
  else if ord w < ord u ∧ ord u < ord v then c w u v
  else if ord w < ord v ∧ ord v < ord u then -c w v u
  else 0

private theorem orderEdge_reverse (b : I → I → A) (u v : I) :
    orderEdge ord b v u = -orderEdge ord b u v := by
  unfold orderEdge
  split_ifs <;> first | omega | simp

private theorem orderedBoundary (hinj : Function.Injective ord) (b : I → I → A)
    (c : I → I → I → B) (i : B →+ A)
    (h : ∀ u v w, b v w - b u w + b u v = i (c u v w)) (u v w : I) :
    orderEdge ord b v w - orderEdge ord b u w + orderEdge ord b u v =
      i (orderFace ord c u v w) := by
  let d (x y z : I) := orderEdge ord b y z - orderEdge ord b x z + orderEdge ord b x y
  change d u v w = _
  have inc (x y z : I) (hxy : ord x < ord y) (hyz : ord y < ord z) :
      d x y z = i (c x y z) := by
    simpa only [d, orderEdge, if_pos hxy, if_pos hyz, if_pos (lt_trans hxy hyz)]
      using h x y z
  have swap₁ (x y z : I) : d x y z = -d y x z := by
    dsimp only [d]
    rw [orderEdge_reverse ord b x y]
    abel
  have swap₂ (x y z : I) : d x y z = -d x z y := by
    dsimp only [d]
    rw [orderEdge_reverse ord b y z]
    abel
  unfold orderFace
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆
  · exact inc _ _ _ h₁.1 h₁.2
  · rw [swap₂, inc _ _ _ h₂.1 h₂.2, map_neg]
  · rw [swap₁, inc _ _ _ h₃.1 h₃.2, map_neg]
  · rw [swap₁ u v w, swap₂ v u w, inc _ _ _ h₄.1 h₄.2, neg_neg]
  · rw [swap₂ u v w, swap₁ u w v, inc _ _ _ h₅.1 h₅.2, neg_neg]
  · rw [swap₂ u v w, swap₁ u w v, swap₂ w u v, inc _ _ _ h₆.1 h₆.2, neg_neg, map_neg]
  · have eqs : ord u = ord v ∨ ord v = ord w ∨ ord u = ord w := by omega
    rcases eqs with huv | hvw | huw
    · obtain rfl := hinj huv
      simp [d, orderEdge]
    · obtain rfl := hinj hvw
      simp [d, orderEdge]
    · obtain rfl := hinj huw
      dsimp only [d]
      rw [orderEdge_reverse ord b u v]
      simp [orderEdge]

end Alternation

private abbrev vertexRank (s : Finset Vertex) (u : s) := rank u.val

def orderedLift (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    NativeCotangent s :=
  orderEdge (vertexRank s)
    (fun x y => nativeCotangentTransitionLift s x.val y.val x.property y.property) ⟨u,hu⟩ ⟨v,hv⟩

def orderedCup (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) : ClosedRing s :=
  orderFace (vertexRank s)
    (fun x y z => nativeCup s x.val y.val z.val x.property y.property z.property)
    ⟨u,hu⟩ ⟨v,hv⟩ ⟨w,hw⟩

theorem orderedLift_reverse (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    orderedLift s v u hv hu = -orderedLift s u v hu hv := orderEdge_reverse _ _ _ _

theorem orderedLift_reduce (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    nativeCotangentReduction s (orderedLift s u v hu hv) =
      logDifferential (K := ℂ) (transition s u v hu hv) := by
  have raw (x y : Vertex) (hx : x ∈ s) (hy : y ∈ s) :
      nativeCotangentReduction s (nativeCotangentTransitionLift s x y hx hy) =
        logDifferential (K := ℂ) (transition s x y hx hy) :=
    LinearMap.congr_fun (nativeCotangentReduction_splitting s x.1 ⟨x.2,hx⟩)
      (logDifferential (K := ℂ) (transition s x y hx hy))
  dsimp only [orderedLift, orderEdge, vertexRank]
  split_ifs with huv hvu
  · exact raw _ _ _ _
  · rw [map_neg, raw, transition_reverse s u v hu hv, logDifferential_inv, neg_neg]
  · have e : u = v := rank_injective (by omega)
    subst v
    rw [map_zero, transition_self, logDifferential_one]

theorem orderedLift_boundary (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    orderedLift s v w hv hw - orderedLift s u w hu hw + orderedLift s u v hu hv =
      nativeEpsilonInclusion s (orderedCup s u v w hu hv hw) := by
  unfold orderedLift orderedCup
  exact orderedBoundary (vertexRank s) (fun _ _ h => Subtype.ext (rank_injective h))
    (fun x y => nativeCotangentTransitionLift s x.val y.val x.property y.property)
    (fun x y z => nativeCup s x.val y.val z.val x.property y.property z.property)
    (nativeEpsilonInclusion s).toAddMonoidHom
    (fun x y z => nativeCotangentTransitionLift_boundary s x.val y.val z.val
      x.property y.property z.property) ⟨u,hu⟩ ⟨v,hv⟩ ⟨w,hw⟩

/-- Restriction of the reduced tensor along the two actual intersection ring maps. -/
def nativeTensorRestriction {s t : Finset Vertex} (hst : s ⊆ t) :
    NativeCotangent s →ₛₗ[thickRestriction hst] NativeCotangent t := by
  let f : ClosedRing s →ₛₗ[thickRestriction hst] ClosedRing t :=
    { toFun := closedRestriction hst
      map_add' := map_add _
      map_smul' := fun a x => by
        change closedRestriction hst (nativeReduction s a * x) =
          nativeReduction t (thickRestriction hst a) * closedRestriction hst x
        rw [map_mul, nativeReduction_restrict] }
  let g : KaehlerDifferential ℂ (ThickRing s) →ₛₗ[thickRestriction hst]
      KaehlerDifferential ℂ (ThickRing t) :=
    { toFun := differentialMap (thickRestrictionAlgHom hst)
      map_add' := map_add _
      map_smul' := differentialMap_smul (thickRestrictionAlgHom hst) }
  exact TensorProduct.map f g

theorem nativeTensorRestriction_tmul {s t : Finset Vertex} (hst : s ⊆ t)
    (a : ClosedRing s) (b : KaehlerDifferential ℂ (ThickRing s)) :
    nativeTensorRestriction hst (a ⊗ₜ[ThickRing s] b) =
      closedRestriction hst a ⊗ₜ[ThickRing t] differentialMap (thickRestrictionAlgHom hst) b := rfl

private theorem rawLift_tmul (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    nativeCotangentTransitionLift s u v hu hv =
      (↑((transition s u v hu hv)⁻¹) : ClosedRing s) ⊗ₜ[ThickRing s]
        KaehlerDifferential.D ℂ (ThickRing s)
          (projectiveSplittingAlgHom s u.1 ⟨u.2,hu⟩ (transition s u v hu hv : ClosedRing s)) := by
  unfold nativeCotangentTransitionLift logDifferential
  rw [map_smul]
  unfold nativeCotangentSplitting
  rw [splittingLift_D]
  change _ • ((1 : ClosedRing s) ⊗ₜ[ThickRing s] _) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

private theorem rawLift_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) :
    nativeTensorRestriction hst (nativeCotangentTransitionLift s u v hu hv) =
      nativeCotangentTransitionLift t u v (hst hu) (hst hv) := by
  rw [rawLift_tmul, rawLift_tmul, nativeTensorRestriction_tmul, differentialMap_D,
    projectiveSplittingAlgHom_restrict]
  have he := transition_restrict hst u v hu hv
  have hval := congrArg (fun x : (ClosedRing t)ˣ => (x : ClosedRing t)) he
  have hinv := congrArg (fun x : (ClosedRing t)ˣ => (↑(x⁻¹) : ClosedRing t)) he
  exact congrArg₂ (fun a b => a ⊗ₜ[ThickRing t]
    KaehlerDifferential.D ℂ (ThickRing t)
      (projectiveSplittingAlgHom t u.1 ⟨u.2,hst hu⟩ b)) hinv hval

theorem orderedLift_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) :
    nativeTensorRestriction hst (orderedLift s u v hu hv) =
      orderedLift t u v (hst hu) (hst hv) := by
  dsimp only [orderedLift, orderEdge, vertexRank]
  split_ifs
  · exact rawLift_restrict hst u v hu hv
  · rw [map_neg, rawLift_restrict]
  · exact map_zero _

open TopologicalSpace CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2FiniteInjectiveCech CycleQ2LiteralNativeCupSectionValues
  CycleQ2LiteralNativeCupDerivedClass CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeGaugeNaturality

private theorem restrict_nativeCupValue (s : Finset Vertex) (hs : s.Nonempty)
    (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s)
    {V W : Opens Surface} (hWV : W ≤ V) (hW : W ≤ closedOpen s)
    (hU : V ≤ cover u) (hV : V ≤ cover v) (hT : V ≤ cover w) :
    res coefficientSheaf hWV (nativeCupValue u v w V hU hV hT) =
      intersectionValue s hs W hW (nativeCup s u v w hu hv hw) := by
  have hst : ({u,v,w} : Finset Vertex) ⊆ s := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu ⟨hv,hw⟩
  rw [← nativeCup_restrict hst u v w (by simp) (by simp) (by simp),
    intersectionValue_restrict]
  exact res_comp coefficientSheaf _ _ _

/-- The scalar in the ordered native boundary represents the previously
defined scalar cup on every common subopen of the original chart. -/
theorem faceValue_eq_orderedCup (s : Finset Vertex) (hs : s.Nonempty)
    (u v w : Vertex) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s)
    (W : Opens Surface) (hW : W ≤ closedOpen s)
    (hU : W ≤ cover u) (hV : W ≤ cover v) (hT : W ≤ cover w) :
    faceValue coefficientSheaf cover nativeCupCocycle u v w W hU hV hT =
      intersectionValue s hs W hW (orderedCup s u v w hu hv hw) := by
  dsimp only [faceValue, nativeCupCocycle, orderedCup, orderFace, vertexRank]
  split_ifs
  · exact restrict_nativeCupValue s hs u v w hu hv hw _ hW _ _ _
  · rw [map_neg, map_neg, restrict_nativeCupValue s hs u w v hu hw hv _ hW]
  · rw [map_neg, map_neg, restrict_nativeCupValue s hs v u w hv hu hw _ hW]
  · exact restrict_nativeCupValue s hs v w u hv hw hu _ hW _ _ _
  · exact restrict_nativeCupValue s hs w u v hw hu hv _ hW _ _ _
  · rw [map_neg, map_neg, restrict_nativeCupValue s hs w v u hw hv hu _ hW]
  · rw [map_zero, map_zero]

end CycleQ2LiteralCotangentOrderedLift

end

#print axioms CycleQ2LiteralCotangentOrderedLift.orderedLift_reduce
#print axioms CycleQ2LiteralCotangentOrderedLift.orderedLift_boundary

#print axioms CycleQ2LiteralCotangentOrderedLift.orderedLift_restrict

#print axioms CycleQ2LiteralCotangentOrderedLift.faceValue_eq_orderedCup
