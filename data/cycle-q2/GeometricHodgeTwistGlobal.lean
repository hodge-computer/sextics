import Proposal.GeometricHodgeTwistCoordinates

/-!
# Global sections from the weighted Laurent charts

The intersection of the four individual chart images consists precisely of
the polynomial normal forms of the requested degree, including the three
possible powers of the cubic generator. The sheaf axiom gives a unique
global section with each such normal form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistGlobal
open CategoryTheory TopologicalSpace CycleQ2HodgeTwistCech
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2HodgeTwistCoordinates

variable {A : Type} [AddCommGroup A] {t : ℤ}

theorem mem_all_singletons (p : NormalForm A) :
    (∀ i : Vertex, p ∈ sections A t {i}) ↔ p ∈ sections A t ∅ := by
  constructor
  · intro h j e hn
    by_contra hz
    have hall (i : Vertex) : Allowed t {i} j e := by
      by_contra hbad
      exact hz (h i j e hbad)
    apply hn
    refine ⟨(hall 0).1, fun a ha => ?_⟩
    have h0 := Finset.mem_singleton.mp ((hall 0).2 a ha)
    have h1 := Finset.mem_singleton.mp ((hall 1).2 a ha)
    exact False.elim ((by decide : (0 : Vertex) ≠ 1) (h0.symm.trans h1))
  · intro hp i
    exact (restrict (Finset.empty_subset {i}) (⟨p,hp⟩ : sections A t ∅)).property

variable {X : TopCat.{0}} {F : AbSheaf X} {U : Vertex → Opens X}
variable {C : Chart F U A} (M : HasLaurentSections C t)
include M

private theorem face_range {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (hw : W = S.inf U)
    (hc : C.common ≤ W) : (read C hc).range = sections A t S := by
  subst W
  exact M.range_eq S hs

private theorem face_injective {S : Finset Vertex} (hs : S.Nonempty) {W : Opens X} (hw : W = S.inf U)
    (hc : C.common ≤ W) : Function.Injective (read C hc) := by
  subst W
  exact M.injective S hs

private theorem single_range (i : Vertex) : (read C (C.le i)).range = sections A t {i} := by
  exact face_range M (by simp) (by simp) _

private theorem single_injective (i : Vertex) : Function.Injective (read C (C.le i)) := by
  exact face_injective M (S := {i}) (by simp) (by simp) _

private theorem pair_injective (i j : Vertex) :
    Function.Injective (read C (le_inf (C.le i) (C.le j))) := by
  exact face_injective M (S := {i,j}) (by simp) (by simp) _

/-- The chart expansion of a global section contains only nonnegative exponents. -/
def globalMap : Sections F ⊤ →+ sections A t ∅ := (read C le_top).codRestrict _ (by
  intro x
  apply (mem_all_singletons _).mp
  intro i
  rw [← single_range M i]
  exact ⟨res F le_top x, read_res C (C.le i) le_top x⟩)

variable (cover : (⨆ i, U i) = ⊤)
include cover

theorem globalMap_injective : Function.Injective (globalMap M) := by
  intro x y h
  apply (show TopCat.Sheaf AddCommGrpCat X from F).eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) cover.ge
  intro i
  apply single_injective M i
  change read C (C.le i) (res F le_top x) = read C (C.le i) (res F le_top y)
  rw [read_res, read_res]
  exact congrArg Subtype.val h

theorem globalMap_surjective : Function.Surjective (globalMap M) := by
  intro p
  have hm := (mem_all_singletons p.val).mpr p.property
  have exists_local (i : Vertex) : ∃ y : Sections F (U i), read C (C.le i) y = p.val := by
    exact Eq.mpr (congrArg (fun G : AddSubgroup (NormalForm A) => p.val ∈ G) (single_range M i)) (hm i)
  choose q hq using exists_local
  have hcompat : TopCat.Presheaf.IsCompatible (show TopCat.Sheaf AddCommGrpCat X from F).obj U q := by
    intro i j
    apply pair_injective M i j
    change read C _ (res F inf_le_left (q i)) = read C _ (res F inf_le_right (q j))
    rw [read_res,read_res,hq,hq]
  obtain ⟨y,hy,_⟩ := (show TopCat.Sheaf AddCommGrpCat X from F).existsUnique_gluing'
    U ⊤ (fun _ => homOfLE le_top) cover.ge q hcompat
  refine ⟨y, Subtype.ext ?_⟩
  change read C le_top y = p.val
  rw [← read_res C (C.le 0) le_top y]
  exact (congrArg (read C (C.le 0)) (hy 0)).trans (hq 0)

/-- Global sections are the homogeneous polynomial normal forms with w-degree at most two. -/
def globalCoordinates : Sections F ⊤ ≃+ sections A t ∅ :=
  AddEquiv.ofBijective (globalMap M) ⟨globalMap_injective M cover, globalMap_surjective M cover⟩

end CycleQ2HodgeTwistGlobal
end

#print axioms CycleQ2HodgeTwistGlobal.globalCoordinates
