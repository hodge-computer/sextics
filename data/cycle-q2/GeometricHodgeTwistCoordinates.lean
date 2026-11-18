import Proposal.GeometricHodgeTwistCech
import Proposal.GeometricHodgeTwistDerived
import Proposal.GeometricAffineHigherChartRestriction

/-!
# Laurent coordinates on a four-open cover and ordinary twist cohomology

Restrictions to a common intersection give every standard chart section
one Laurent expansion. Its coefficient group on a face specifies exactly
which poles are allowed. These coordinate identifications transfer finite
Laurent primitives back to actual sheaf sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistCoordinates

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open CycleQ2HodgeTwistCech CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent (Zero)

variable {X : TopCat.{0}} {A : Type} [AddCommGroup A] {t : ℤ}
variable {F : AbSheaf X} {U : Vertex → Opens X}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- Expansion on a common intersection of the four opens. -/
structure Chart (F : AbSheaf X) (U : Vertex → Opens X) (A : Type) [AddCommGroup A] where
  common : Opens X
  le : ∀ i, common ≤ U i
  coordinates : Sections F common →+ NormalForm A

variable (C : Chart F U A)

def read {W : Opens X} (h : C.common ≤ W) : Sections F W →+ NormalForm A :=
  C.coordinates.comp (res F h)

theorem read_res {V W : Opens X} (hV : C.common ≤ V) (h : V ≤ W) (p : Sections F W) :
    read C hV (res F h p) = read C (hV.trans h) p := by
  simp only [read, AddMonoidHom.comp_apply, res_comp]

private theorem common_le (S : Finset Vertex) : C.common ≤ S.inf U :=
  Finset.le_inf fun i _ => C.le i

/-- Each nonempty standard intersection embeds, with image exactly its twisted Laurent sections. -/
structure HasLaurentSections (t : ℤ) : Prop where
  injective (S : Finset Vertex) (hS : S.Nonempty) : Function.Injective (read C (common_le C S))
  range_eq (S : Finset Vertex) (hS : S.Nonempty) : (read C (common_le C S)).range = sections A t S

variable {C} (M : HasLaurentSections C t)
include M

private theorem range_eq {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (h : W = S.inf U)
    (hw : C.common ≤ W) : (read C hw).range = sections A t S := by
  subst W
  exact M.range_eq S hs

private theorem injective {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (h : W = S.inf U)
    (hw : C.common ≤ W) : Function.Injective (read C hw) := by
  subst W
  exact M.injective S hs

private theorem in_sections {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (h : W = S.inf U)
    (hw : C.common ≤ W) (p : Sections F W) : read C hw p ∈ sections A t S := by
  rw [← range_eq M hs h hw]
  exact ⟨p,rfl⟩

private theorem lift {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (h : W = S.inf U)
    (hw : C.common ≤ W) (v : sections A t S) : ∃ p : Sections F W, read C hw p = v.val := by
  exact Eq.mpr (congrArg (fun G : AddSubgroup (NormalForm A) => v.val ∈ G) (range_eq M hs h hw)) v.property

private def coordOne (c : One F U) : C1 A t := fun i j =>
  ⟨read C (le_inf (C.le i) (C.le j)) (c i j),
    in_sections M (by simp) (by simp) _ _⟩

private def coordTwo (c : Two F U) : C2 A t := fun i j k =>
  ⟨read C (le_inf (le_inf (C.le i) (C.le j)) (C.le k)) (c i j k),
    in_sections M (by simp) (by simp [inf_assoc]) _ _⟩

private theorem coordOne_closed (c : One F U) (hc : IsOneCocycle F U c) : d1 (coordOne M c) = 0 := by
  funext i j k
  apply Subtype.ext
  have h := congrArg C.coordinates (hc i j k C.common (C.le i) (C.le j) (C.le k))
  rw [map_add] at h
  change (coordOne M c j k).val - (coordOne M c i k).val + (coordOne M c i j).val = 0
  change (coordOne M c i k).val = (coordOne M c i j).val + (coordOne M c j k).val at h
  rw [h]
  abel

private theorem coordTwo_closed (c : Two F U) (hc : IsTwoCocycle F U c) : d2 (coordTwo M c) = 0 := by
  funext i j k l
  apply Subtype.ext
  have h := congrArg C.coordinates (hc i j k l C.common (C.le i) (C.le j) (C.le k) (C.le l))
  simp only [map_sub, map_add, map_zero] at h
  exact h

theorem one_primitive (c : One F U) (hc : IsOneCocycle F U c) : ∃ p : Zero F U,
    ∀ i j W hi hj, res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj := by
  let v := h1 (coordOne M c)
  choose p hp using fun i => lift M (by simp) (show U i = ({i} : Finset Vertex).inf U by simp) (C.le i) (v i)
  refine ⟨p, ?_⟩
  intro i j W hi hj
  have e : res F (inf_le_right : U i ⊓ U j ≤ U j) (p j) - res F inf_le_left (p i) = c i j := by
    apply injective M (S := {i,j}) (by simp) (by simp) (le_inf (C.le i) (C.le j))
    rw [map_sub, read_res, read_res, hp, hp]
    exact congrArg (fun z : C1 A t => (z i j).val) (exact_one _ (coordOne_closed M c hc))
  simpa only [map_sub, res_comp, edgeValue] using congrArg (res F (le_inf hi hj)) e

theorem two_primitive (c : Two F U) (hc : IsTwoCocycle F U c) : ∃ b : One F U,
    ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk = faceValue F U c i j k W hi hj hk := by
  let v := h2 (coordTwo M c)
  choose b hb using fun i j => lift M (by simp) (show U i ⊓ U j = ({i,j} : Finset Vertex).inf U by simp)
    (le_inf (C.le i) (C.le j)) (v i j)
  refine ⟨b, ?_⟩
  intro i j k W hi hj hk
  let V := (U i ⊓ U j) ⊓ U k
  have vi : V ≤ U i := inf_le_left.trans inf_le_left
  have vj : V ≤ U j := inf_le_left.trans inf_le_right
  have vk : V ≤ U k := inf_le_right
  have e : boundaryValue F U b i j k V vi vj vk = c i j k := by
    apply injective M (S := {i,j,k}) (by simp) (by simp [V,inf_assoc]) (le_inf (le_inf (C.le i) (C.le j)) (C.le k))
    let hv : C.common ≤ V := le_inf (le_inf (C.le i) (C.le j)) (C.le k)
    have hread (m n : Vertex) (hm : V ≤ U m) (hn : V ≤ U n) :
        read C hv (edgeValue F U b m n V hm hn) = (v m n).val :=
      (read_res C hv (le_inf hm hn) (b m n)).trans (hb m n)
    rw [boundaryValue, map_add, map_sub, hread, hread, hread]
    exact congrArg (fun z : C2 A t => (z i j k).val) (exact_two _ (coordTwo_closed M c hc))
  let hWV : W ≤ V := le_inf (le_inf hi hj) hk
  have hres (m n : Vertex) (hm : V ≤ U m) (hn : V ≤ U n) :
      res F hWV (edgeValue F U b m n V hm hn) = edgeValue F U b m n W (hWV.trans hm) (hWV.trans hn) :=
    res_comp F (le_inf hm hn) hWV _
  have he := congrArg (res F hWV) e
  rw [boundaryValue, map_add, map_sub, hres, hres, hres] at he
  exact he

theorem hOne (hcover : (⨆ i, U i) = ⊤) (hvertex : ∀ i, Subsingleton (F.H' 1 (U i))) :
    Subsingleton (F.H 1) := CycleQ2HodgeTwistDerived.hOne_of_primitives F U hcover hvertex (one_primitive M)

theorem hTwo (hcover : (⨆ i, U i) = ⊤) (hvertex : ∀ i, Subsingleton (F.H' 2 (U i)))
    (hedge : ∀ i j, Subsingleton (F.H' 1 (U i ⊓ U j))) : Subsingleton (F.H 2) :=
  CycleQ2HodgeTwistDerived.hTwo_of_primitives F U hcover hvertex hedge (two_primitive M)

omit M
section AffineCharts

open AlgebraicGeometry CycleQ2GeometricProjectiveHOne CycleQ2GeometricAffineHTwo

/-- Only affine chart and transition data are needed for a line bundle with these Laurent
coordinates. The local cohomology hypotheses follow from the affine structure sheaf. -/
theorem ordinary_vanishing {Y : Scheme.{0}} {G : AbSheaf Y} {V : Vertex → Y.Opens}
    {D : Chart G V A} (H : HasLaurentSections D t) (hcover : (⨆ i, V i) = ⊤)
    (hvertex : ∀ i, IsAffineOpen (V i)) (hedge : ∀ i j, IsAffineOpen (V i ⊓ V j))
    (frame : ∀ i, PatchIso G (structureAdditiveSheaf Y) (V i)) :
    Subsingleton (G.H 1) ∧ Subsingleton (G.H 2) := by
  refine ⟨hOne H hcover (fun i => affineFrameHOne_subsingleton (hvertex i).isoSpec G
    (overIsoOfPatchIso (frame i))), hTwo H hcover ?_ ?_⟩
  · intro i
    exact affineFrameHTwo_subsingleton (hvertex i).isoSpec G (overIsoOfPatchIso (frame i))
      (affine_H_two_subsingleton _)
  · intro i j
    let fr : PatchIso G (structureAdditiveSheaf Y) (V i ⊓ V j) := {
      app := fun W hW => (frame i).app W (hW.trans inf_le_left)
      naturality := fun h hW x => (frame i).naturality h (hW.trans inf_le_left) x }
    exact affineFrameHOne_subsingleton (hedge i j).isoSpec G (overIsoOfPatchIso fr)

end AffineCharts

end CycleQ2HodgeTwistCoordinates
end

#print axioms CycleQ2HodgeTwistCoordinates.hOne
#print axioms CycleQ2HodgeTwistCoordinates.hTwo

#print axioms CycleQ2HodgeTwistCoordinates.ordinary_vanishing
