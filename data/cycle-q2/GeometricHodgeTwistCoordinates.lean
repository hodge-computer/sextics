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

/-! ## The top trace on actual sheaf sections

All quotients below are formed from sections of `F` on its actual standard
intersections. The Laurent model is used only to compute the restriction
map and its kernel.
-/

/-- Native sections of a nonempty intersection, in the common Laurent coordinates. -/
def faceCoordinates (S : Finset Vertex) (hS : S.Nonempty) :
    Sections F (S.inf U) ≃+ sections A t S := by
  let f : Sections F (S.inf U) →+ sections A t S :=
    (read C (common_le C S)).codRestrict _ (fun s =>
      (M.range_eq S hS) ▸ (show read C (common_le C S) s ∈
        (read C (common_le C S)).range from ⟨s, rfl⟩))
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact M.injective S hS (congrArg Subtype.val h)
  · intro p
    obtain ⟨s, hs⟩ := lift M hS rfl (common_le C S) p
    exact ⟨s, Subtype.ext hs⟩

@[simp] theorem faceCoordinates_val (S : Finset Vertex) (hS : S.Nonempty)
    (s : Sections F (S.inf U)) :
    (faceCoordinates M S hS s).val = read C (common_le C S) s := rfl

omit M in
private theorem topFace_nonempty (i : Vertex) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩

omit M in
private theorem top_le_face (i : Vertex) :
    Finset.univ.inf U ≤ (Finset.univ.erase i).inf U :=
  Finset.le_inf (fun j _ => Finset.inf_le (Finset.mem_univ j))

abbrev NativeTopFaces := (i : Vertex) → Sections F ((Finset.univ.erase i).inf U)

/-- The actual increasing four-open Čech restriction in degree two. -/
def nativeTopBoundary : NativeTopFaces (F := F) (U := U) →+
    Sections F (Finset.univ.inf U) where
  toFun c := res F (top_le_face 0) (c 0) - res F (top_le_face 1) (c 1) +
    res F (top_le_face 2) (c 2) - res F (top_le_face 3) (c 3)
  map_zero' := by simp
  map_add' c d := by
    simp only [Pi.add_apply, map_add]
    abel

def nativeFaceCoordinates (c : NativeTopFaces (F := F) (U := U)) : TopFaces A t :=
  fun i => faceCoordinates M (Finset.univ.erase i) (topFace_nonempty i) (c i)

def nativeTopCoordinates : Sections F (Finset.univ.inf U) ≃+ Top A t :=
  faceCoordinates M Finset.univ (by simp)

theorem nativeTopCoordinates_boundary (c : NativeTopFaces (F := F) (U := U)) :
    nativeTopCoordinates M (nativeTopBoundary c) = topBoundary (nativeFaceCoordinates M c) := by
  apply Subtype.ext
  change read C (common_le C Finset.univ)
      (res F (top_le_face 0) (c 0) - res F (top_le_face 1) (c 1) +
        res F (top_le_face 2) (c 2) - res F (top_le_face 3) (c 3)) = _
  rw [map_sub, map_add, map_sub, read_res, read_res, read_res, read_res]
  rfl

theorem nativeFaceCoordinates_surjective :
    Function.Surjective (nativeFaceCoordinates M) := by
  intro c
  refine ⟨fun i => (faceCoordinates M (Finset.univ.erase i)
    (topFace_nonempty i)).symm (c i), ?_⟩
  funext i
  exact (faceCoordinates M (Finset.univ.erase i) (topFace_nonempty i)).apply_symm_apply (c i)

/-- The top section extends from alternating triple sections exactly when its
Laurent normal form has no strictly negative part. -/
theorem native_top_mem_boundary_iff (s : Sections F (Finset.univ.inf U)) :
    s ∈ (nativeTopBoundary (F := F) (U := U)).range ↔
      negativePart (nativeTopCoordinates M s) = 0 := by
  rw [← top_mem_boundary_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨nativeFaceCoordinates M c, (nativeTopCoordinates_boundary M c).symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := nativeFaceCoordinates_surjective M c
    refine ⟨b, (nativeTopCoordinates M).injective ?_⟩
    exact (nativeTopCoordinates_boundary M b).trans hc

/-- The degree-three section quotient, formed before choosing Laurent coordinates. -/
abbrev NativeTopQuotient := Sections F (Finset.univ.inf U) ⧸
  (nativeTopBoundary (F := F) (U := U)).range

omit M in
def nativeTopSectionTrace (H : HasLaurentSections C 0) :
    Sections F (Finset.univ.inf U) →+ A :=
  topCoefficient.comp (nativeTopCoordinates H).toAddMonoidHom

omit M in
theorem native_top_mem_boundary_iff_trace_zero (H : HasLaurentSections C 0)
    (s : Sections F (Finset.univ.inf U)) :
    s ∈ (nativeTopBoundary (F := F) (U := U)).range ↔ nativeTopSectionTrace H s = 0 :=
  (native_top_mem_boundary_iff H s).trans (negativePart_eq_zero_iff _)

omit M in
/-- The distinguished Laurent residue on the actual degree-three section quotient. -/
def nativeTopTrace (H : HasLaurentSections C 0) :
    NativeTopQuotient (F := F) (U := U) →+ A :=
  QuotientAddGroup.lift _ (nativeTopSectionTrace H) (fun s hs =>
    (native_top_mem_boundary_iff_trace_zero H s).mp hs)

omit M in
theorem nativeTopTrace_bijective (H : HasLaurentSections C 0) :
    Function.Bijective (nativeTopTrace H) := by
  refine ⟨(QuotientAddGroup.injective_lift_iff _ _ _).2 ?_, ?_⟩
  · ext s
    exact native_top_mem_boundary_iff_trace_zero H s
  · intro a
    let s := (nativeTopCoordinates H).symm (topGenerator a)
    refine ⟨QuotientAddGroup.mk s, ?_⟩
    change topCoefficient (nativeTopCoordinates H s) = a
    rw [show nativeTopCoordinates H s = topGenerator a from
      (nativeTopCoordinates H).apply_symm_apply (topGenerator a), topCoefficient_topGenerator]

omit M in
def nativeTopTraceEquiv (H : HasLaurentSections C 0) :
    NativeTopQuotient (F := F) (U := U) ≃+ A :=
  AddEquiv.ofBijective (nativeTopTrace H) (nativeTopTrace_bijective H)

theorem nativeTopBoundary_surjective_of_positive (ht : 0 < t) :
    Function.Surjective (nativeTopBoundary (F := F) (U := U)) := by
  intro s
  obtain ⟨c, hc⟩ := topBoundary_surjective_of_positive ht (nativeTopCoordinates M s)
  obtain ⟨b, rfl⟩ := nativeFaceCoordinates_surjective M c
  exact ⟨b, (nativeTopCoordinates M).injective ((nativeTopCoordinates_boundary M b).trans hc)⟩

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
#print axioms CycleQ2HodgeTwistCoordinates.nativeTopTraceEquiv
#print axioms CycleQ2HodgeTwistCoordinates.nativeTopBoundary_surjective_of_positive

/-!
## The same native quotient in derived H³

The only changes of coordinates below are restrictions along proved
equalities of opens. The actual three Mayer--Vietoris boundaries from
`CycleQ2FourOpenH3` therefore compute the quotient already used above.
-/

noncomputable section
namespace CycleQ2HodgeTwistTopDerived

open CategoryTheory Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricSheafLocalIso (res res_self res_comp)
open CycleQ2HodgeTwistCech (Vertex)
open CycleQ2HodgeTwistCoordinates
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2FourOpenH3 (QuadOpen)

variable {X : TopCat.{0}} (F : AbSheaf X) (U : Vertex → Opens X)
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

private def sectionEq {V W : Opens X} (h : V = W) : Sections F V ≃+ Sections F W where
  toFun := res F h.ge
  invFun := res F h.le
  left_inv s := by rw [res_comp, res_self]
  right_inv s := by rw [res_comp, res_self]
  map_add' := (res F h.ge).map_add

private theorem face_zero : (Finset.univ.erase (0 : Vertex)).inf U =
    (U 1 ⊓ U 3) ⊓ (U 2 ⊓ U 3) := by
  rw [show Finset.univ.erase (0 : Vertex) = {1,2,3} from by decide]
  simp [inf_assoc, inf_left_comm, inf_comm]

private theorem face_one : (Finset.univ.erase (1 : Vertex)).inf U =
    (U 0 ⊓ U 3) ⊓ (U 2 ⊓ U 3) := by
  rw [show Finset.univ.erase (1 : Vertex) = {0,2,3} from by decide]
  simp [inf_assoc, inf_left_comm, inf_comm]

private theorem face_two : (Finset.univ.erase (2 : Vertex)).inf U =
    (U 0 ⊓ U 3) ⊓ (U 1 ⊓ U 3) := by
  rw [show Finset.univ.erase (2 : Vertex) = {0,1,3} from by decide]
  simp [inf_assoc, inf_left_comm, inf_comm]

private theorem face_three : (Finset.univ.erase (3 : Vertex)).inf U =
    TripleOpen (U 0) (U 1) (U 2) := by
  rw [show Finset.univ.erase (3 : Vertex) = {0,1,2} from by decide]
  simp [TripleOpen, inf_assoc, inf_left_comm, inf_comm]

theorem full_quad : Finset.univ.inf U = QuadOpen (U 0) (U 1) (U 2) (U 3) := by
  rw [show (Finset.univ : Finset Vertex) = {0,1,2,3} from by decide]
  simp [QuadOpen, TripleOpen, inf_assoc, inf_left_comm, inf_comm]

def nativeQuadEquiv : Sections F (Finset.univ.inf U) ≃+
    Sections F (QuadOpen (U 0) (U 1) (U 2) (U 3)) := sectionEq F (full_quad U)

def nativeTripleEquiv : NativeTopFaces (F := F) (U := U) ≃+
    CycleQ2FourOpenH3.TripleSections F (U 0) (U 1) (U 2) (U 3) where
  toFun c := (sectionEq F (face_three U) (c 3), sectionEq F (face_two U) (c 2),
    sectionEq F (face_one U) (c 1), sectionEq F (face_zero U) (c 0))
  invFun p i := by
    fin_cases i
    · exact (sectionEq F (face_zero U)).symm p.2.2.2
    · exact (sectionEq F (face_one U)).symm p.2.2.1
    · exact (sectionEq F (face_two U)).symm p.2.1
    · exact (sectionEq F (face_three U)).symm p.1
  left_inv c := by
    funext i
    fin_cases i <;> exact AddEquiv.symm_apply_apply _ _
  right_inv p := by
    rcases p with ⟨p₃,p₂,p₁,p₀⟩
    simp only [AddEquiv.apply_symm_apply]
  map_add' c d := by
    simp only [Pi.add_apply, map_add, Prod.mk_add_mk]

theorem nativeQuad_boundary (c : NativeTopFaces (F := F) (U := U)) :
    nativeQuadEquiv F U (nativeTopBoundary c) =
      CycleQ2FourOpenH3.boundary F (U 0) (U 1) (U 2) (U 3) (nativeTripleEquiv F U c) := by
  change res F _
      (res F _ (c 0) - res F _ (c 1) + res F _ (c 2) - res F _ (c 3)) =
    res F _ (res F _ (c 0)) - res F _ (res F _ (c 1)) +
      res F _ (res F _ (c 2)) - res F _ (res F _ (c 3))
  simp only [map_sub, map_add, res_comp]

theorem union_cover (hcover : (⨆ i, U i) = ⊤) :
    ((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3 = ⊤ := by
  have he : ((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3 = ⨆ i, U i := by
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (le_iSup U 2)) (le_iSup U 3)
    · apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
  exact he.trans hcover

def unionCohomologyEquiv (hcover : (⨆ i, U i) = ⊤) :
    F.H' 3 (((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3) ≃+ F.H' 3 ⊤ :=
  ((F.cohomologyPresheaf 3).mapIso (eqToIso (union_cover U hcover).symm).op).addCommGroupIsoToAddEquiv

/-- The actual three successive connecting maps on the native quadruple section. -/
def nativeTopConnecting (hcover : (⨆ i, U i) = ⊤) :
    Sections F (Finset.univ.inf U) →+ F.H' 3 ⊤ :=
  (unionCohomologyEquiv F U hcover).toAddMonoidHom.comp
    ((CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)).comp
      (nativeQuadEquiv F U).toAddMonoidHom)

/-- The original finite intersection is the ordered quadruple
intersection used by the injective Čech comparison. -/
theorem nativeTopOpen_eq_ordered : Finset.univ.inf U =
    ((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3 := by
  rw [show (Finset.univ : Finset Vertex) = {0,1,2,3} from by decide]
  simp [inf_assoc]

/-- Only restriction along equality changes a native top section into
the ordered four-open convention. -/
def nativeTopOrdered : Sections F (Finset.univ.inf U) →+
    CycleQ2CechTwoToDerived.Three F U :=
  res F (nativeTopOpen_eq_ordered U).ge

theorem orderedConnecting_nativeTopOrdered (hcover : (⨆ i, U i) = ⊤)
    (s : Sections F (Finset.univ.inf U)) :
    CycleQ2FourOpenTopMayerVietoris.orderedConnecting U hcover (nativeTopOrdered F U s) =
      nativeTopConnecting F U hcover s := by
  have he : (homOfLE (union_cover U hcover).ge :
      (⊤ : Opens X) ⟶ ((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3) =
      eqToHom (union_cover U hcover).symm := Subsingleton.elim _ _
  change (F.cohomologyPresheaf 3).map (homOfLE (union_cover U hcover).ge).op
      (CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)
        (res F _ (res F _ s))) =
    (F.cohomologyPresheaf 3).map (eqToHom (union_cover U hcover).symm).op
      (CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3) (res F _ s))
  rw [res_comp, he]

/-- The native top section represents the negative of its original
three-Mayer--Vietoris image under the injective Čech convention. -/
theorem cechThreeClass_nativeTopOrdered (hcover : (⨆ i, U i) = ⊤)
    (s : Sections F (Finset.univ.inf U)) :
    CycleQ2FourOpenTopCoefficientBoundary.cechThreeClass U hcover
      (nativeTopOrdered F U s) = -nativeTopConnecting F U hcover s := by
  rw [CycleQ2FourOpenTopMayerVietoris.cechThreeClass_eq_neg_orderedConnecting,
    orderedConnecting_nativeTopOrdered]

/-- The coefficient boundary of an actual four-face lift has precisely
the native top section and the proved negative sign. -/
theorem coefficient_connecting_nativeTop
    {S : CategoryTheory.ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (hcover : (⨆ i, U i) = ⊤) (b : CycleQ2CechTwoToDerived.Two S.X₂ U)
    (s : Sections S.X₁ (Finset.univ.inf U))
    (hb : CycleQ2CechTwoToDerived.d2 S.X₂ U b =
      CycleQ2CechTwoToDerived.app S.f _ (nativeTopOrdered S.X₁ U s)) :
    (CycleQ2CechTwoToDerived.cechTwoClass U hcover
      (CycleQ2CechTwoToDerived.mapTwo U S.g b)
      (CycleQ2FourOpenTopCoefficientBoundary.reducedTwo_closed U b
        (nativeTopOrdered S.X₁ U s) hb)).comp hS.extClass rfl =
      -nativeTopConnecting S.X₁ U hcover s :=
  (CycleQ2FourOpenTopCoefficientBoundary.cechTwoClass_connecting U hS hcover b
    (nativeTopOrdered S.X₁ U s) hb).trans
      (cechThreeClass_nativeTopOrdered S.X₁ U hcover s)

theorem nativeTopConnecting_boundary (hcover : (⨆ i, U i) = ⊤)
    (c : NativeTopFaces (F := F) (U := U)) :
    nativeTopConnecting F U hcover (nativeTopBoundary c) = 0 := by
  change unionCohomologyEquiv F U hcover
    (CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)
      (nativeQuadEquiv F U (nativeTopBoundary c))) = 0
  rw [nativeQuad_boundary, CycleQ2FourOpenH3.connecting_boundary, map_zero]

/-- Vanishing on the nonempty standard intersections; in the application
these are the actual affine charts with the proved twist frames. -/
def FaceAcyclic : Prop := ∀ (S : Finset Vertex), S.Nonempty → ∀ n : ℕ,
  Subsingleton (F.H' (n+1) (S.inf U))

private theorem single_vanishing (H : FaceAcyclic F U) (i : Vertex) (n : ℕ) :
    Subsingleton (F.H' (n+1) (U i)) := by
  simpa using H {i} (by simp) n

private theorem pair_vanishing (H : FaceAcyclic F U) (i j : Vertex) (n : ℕ) :
    Subsingleton (F.H' (n+1) (U i ⊓ U j)) := by
  simpa using H {i,j} (by simp) n

private theorem triple_vanishing (H : FaceAcyclic F U) (i j k : Vertex) (n : ℕ) :
    Subsingleton (F.H' (n+1) (TripleOpen (U i) (U j) (U k))) := by
  simpa [TripleOpen, inf_assoc, inf_left_comm, inf_comm] using H {i,j,k} (by simp) n

theorem nativeTopConnecting_eq_zero_iff (hcover : (⨆ i, U i) = ⊤)
    (H : FaceAcyclic F U) (s : Sections F (Finset.univ.inf U)) :
    nativeTopConnecting F U hcover s = 0 ↔ s ∈ (nativeTopBoundary (F := F) (U := U)).range := by
  letI singleTwo (i : Vertex) : Subsingleton (F.H' 2 (U i)) := single_vanishing F U H i 1
  letI pairOne (i j : Vertex) : Subsingleton (F.H' 1 (U i ⊓ U j)) := pair_vanishing F U H i j 0
  constructor
  · intro hs
    have hz : CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)
        (nativeQuadEquiv F U s) = 0 :=
      (unionCohomologyEquiv F U hcover).injective
        (hs.trans (unionCohomologyEquiv F U hcover).map_zero.symm)
    obtain ⟨p, hp⟩ := (CycleQ2FourOpenH3.connecting_eq_zero_iff
      F (U 0) (U 1) (U 2) (U 3) _).mp hz
    obtain ⟨c, rfl⟩ := (nativeTripleEquiv F U).surjective p
    exact ⟨c, (nativeQuadEquiv F U).injective ((nativeQuad_boundary F U c).trans hp)⟩
  · rintro ⟨c, rfl⟩
    exact nativeTopConnecting_boundary F U hcover c

theorem nativeTopConnecting_surjective (hcover : (⨆ i, U i) = ⊤)
    (H : FaceAcyclic F U) : Function.Surjective (nativeTopConnecting F U hcover) := by
  letI singleThree (i : Vertex) : Subsingleton (F.H' 3 (U i)) := single_vanishing F U H i 2
  letI pairTwo (i j : Vertex) : Subsingleton (F.H' 2 (U i ⊓ U j)) := pair_vanishing F U H i j 1
  letI tripleOne (i j k : Vertex) : Subsingleton (F.H' 1 (TripleOpen (U i) (U j) (U k))) :=
    triple_vanishing F U H i j k 0
  exact (unionCohomologyEquiv F U hcover).surjective.comp
    ((CycleQ2FourOpenH3.connecting_surjective F (U 0) (U 1) (U 2) (U 3)).comp
      (nativeQuadEquiv F U).surjective)

def nativeTopCohomology (hcover : (⨆ i, U i) = ⊤) :
    NativeTopQuotient (F := F) (U := U) →+ F.H' 3 ⊤ :=
  QuotientAddGroup.lift _ (nativeTopConnecting F U hcover)
    (by rintro _ ⟨c,rfl⟩; exact nativeTopConnecting_boundary F U hcover c)

theorem nativeTopCohomology_bijective (hcover : (⨆ i, U i) = ⊤)
    (H : FaceAcyclic F U) : Function.Bijective (nativeTopCohomology F U hcover) := by
  refine ⟨(QuotientAddGroup.injective_lift_iff _ _ _).2 ?_, ?_⟩
  · ext s
    exact (nativeTopConnecting_eq_zero_iff F U hcover H s).symm
  · intro x
    obtain ⟨s,hs⟩ := nativeTopConnecting_surjective F U hcover H x
    exact ⟨QuotientAddGroup.mk s,hs⟩

/-- This equivalence is induced by the actual Mayer--Vietoris maps. -/
def nativeTopCohomologyEquiv (hcover : (⨆ i, U i) = ⊤) (H : FaceAcyclic F U) :
    NativeTopQuotient (F := F) (U := U) ≃+ F.H' 3 ⊤ :=
  AddEquiv.ofBijective (nativeTopCohomology F U hcover)
    (nativeTopCohomology_bijective F U hcover H)

variable {A : Type} [AddCommGroup A] {C : Chart F U A}

/-- The coefficient-one residue on the actual derived degree-three group. -/
def derivedTopTraceEquiv (M : HasLaurentSections C 0)
    (hcover : (⨆ i, U i) = ⊤) (H : FaceAcyclic F U) : F.H' 3 ⊤ ≃+ A :=
  (nativeTopCohomologyEquiv F U hcover H).symm.trans (nativeTopTraceEquiv M)

theorem derivedTopTrace_connecting (M : HasLaurentSections C 0)
    (hcover : (⨆ i, U i) = ⊤) (H : FaceAcyclic F U)
    (s : Sections F (Finset.univ.inf U)) :
    derivedTopTraceEquiv F U M hcover H (nativeTopConnecting F U hcover s) =
      nativeTopSectionTrace M s := by
  change nativeTopTraceEquiv M
    ((nativeTopCohomologyEquiv F U hcover H).symm
      ((nativeTopCohomologyEquiv F U hcover H) (QuotientAddGroup.mk s))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem derived_hThree_of_positive {t : ℤ} (M : HasLaurentSections C t)
    (ht : 0 < t) (hcover : (⨆ i, U i) = ⊤) (H : FaceAcyclic F U) :
    Subsingleton (F.H' 3 ⊤) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective F U hcover H x
  obtain ⟨c,rfl⟩ := nativeTopBoundary_surjective_of_positive M ht s
  exact nativeTopConnecting_boundary F U hcover c

end CycleQ2HodgeTwistTopDerived
end

#print axioms CycleQ2HodgeTwistTopDerived.nativeTopCohomologyEquiv
#print axioms CycleQ2HodgeTwistTopDerived.derivedTopTraceEquiv
#print axioms CycleQ2HodgeTwistTopDerived.derived_hThree_of_positive
