import Proposal.GeometricHodgeTwistAnchor
import Proposal.GeometricHodgeTwistCoordinates
import Proposal.GeometricHodgeTwistGlobal

/-!
# A common Laurent chart for the actual twist on the weighted threefold

Frame evaluation on the open where all four weight-one coordinates are
units compares the Laurent expansions from different anchors. Each
standard intersection embeds into the common expansion with exactly the
exponents allowed on that intersection.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistTorusChart

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold vertexCoefficient coordinateOpen)
open CycleQ2HodgeThreefoldTwist (twist chartFrame chartFrame_transition)
open CycleQ2HodgeTwistMonomials (evaluate evaluate_change)
open CycleQ2HodgeTwistRatios (transition)
open CycleQ2HodgeTwistCubicFaces (twistCoordinates)
open CycleQ2HodgeTwistCoordinates (Chart read HasLaurentSections)
open CycleQ2HodgeTwistCech (Vertex NormalForm sections restrict)
open CycleQ2GeometricSheafLocalIso (res res_self)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2HodgeTwistAnchor (torus torus_le torus_le_face commonCoefficient face_frame_evaluation)

local instance (X : TopCat.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf X) := HasExt.standard _

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)
  (h : IsUnit (φ vertexCoefficient)) (k : ℤ)

abbrev F := addSheaf (twist φ k)

private abbrev full := twistCoordinates φ 0 h Finset.univ (Finset.mem_univ 0) k

/-- Global choice of Laurent coordinates using the zeroth weight-one frame on the common torus. -/
def chart : Chart (F φ k) (coordinateOpen φ) R where
  common := torus φ
  le := torus_le φ
  coordinates := (sections R k Finset.univ).subtype.comp (full φ h k).toAddMonoidHom

/-- The Laurent expansion read through the zeroth frame is the native expansion in
any chosen anchor of the original face. -/
theorem read_face (i : Vertex) (S : Finset Vertex) (hi : i ∈ S)
    (s : Γ(twist φ k, S.inf (coordinateOpen φ))) :
    read (chart φ h k) (torus_le_face φ S) s = (twistCoordinates φ i h S hi k s).val := by
  let W := torus φ
  let u := res (F φ k) (torus_le_face φ S) s
  let p := twistCoordinates φ i h S hi k s
  let extP := restrict (Finset.subset_univ S) p
  let v := (full φ h k).symm extP
  have hv : chartFrame φ k 0 W (torus_le φ 0) v =
      evaluate φ W (torus_le φ) (commonCoefficient φ) 0 p.val := by
    have e := face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ _) k v
    change chartFrame φ k 0 W (torus_le φ 0) (res (F φ k) (show W ≤ W from le_rfl) v) =
      evaluate φ W (torus_le φ) (commonCoefficient φ) 0 (((full φ h k) v).val) at e
    rw [res_self] at e
    simpa only [v, AddEquiv.apply_symm_apply, extP, CycleQ2HodgeTwistCech.restrict] using e
  have hu : u = v := by
    apply (chartFrame φ k 0 W (torus_le φ 0)).injective
    calc
      chartFrame φ k 0 W _ u =
          (transition φ 0 i W _ _ ^ k : Γ(threefold φ,W)ˣ).val * chartFrame φ k i W _ u :=
        chartFrame_transition φ k 0 i W _ _ u
      _ = (transition φ 0 i W _ _ ^ k : Γ(threefold φ,W)ˣ).val *
            evaluate φ W (torus_le φ) (commonCoefficient φ) i p.val :=
        congrArg _ (face_frame_evaluation φ i h S hi k s)
      _ = evaluate φ W (torus_le φ) (commonCoefficient φ) 0 p.val :=
        (evaluate_change φ W (torus_le φ) (commonCoefficient φ) 0 i p).symm
      _ = _ := hv.symm
  change ((full φ h k) u).val = p.val
  rw [hu]
  exact congrArg Subtype.val ((full φ h k).apply_symm_apply extP)

/-- All integral twists of the actual monic weighted sextic have these common
coordinates simultaneously on all fifteen nonempty standard intersections. -/
theorem nativeLaurentSections : HasLaurentSections (chart φ h k) k where
  injective S hS := by
    obtain ⟨i,hi⟩ := hS
    intro x y e
    change read (chart φ h k) (torus_le_face φ S) x =
      read (chart φ h k) (torus_le_face φ S) y at e
    rw [read_face φ h k i S hi, read_face φ h k i S hi] at e
    exact (twistCoordinates φ i h S hi k).injective (Subtype.ext e)
  range_eq S hS := by
    obtain ⟨i,hi⟩ := hS
    ext p
    constructor
    · rintro ⟨s,rfl⟩
      rw [read_face φ h k i S hi]
      exact (twistCoordinates φ i h S hi k s).property
    · intro hp
      let v : sections R k S := ⟨p,hp⟩
      refine ⟨(twistCoordinates φ i h S hi k).symm v, ?_⟩
      rw [read_face φ h k i S hi, AddEquiv.apply_symm_apply]

/-- Global sections are the homogeneous Laurent normal forms with no poles. -/
def globalSections :
    CycleQ2InjectiveCech.Sections (F φ k) ⊤ ≃+ sections R k ∅ :=
  CycleQ2HodgeTwistGlobal.globalCoordinates (nativeLaurentSections φ h k) (by
    exact CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)

include h in
/-- Both intermediate cohomology groups of every integral twist vanish on the actual threefold. -/
theorem ordinary_vanishing :
    Subsingleton ((F φ k).H 1) ∧ Subsingleton ((F φ k).H 2) := by
  have ha (S : Finset Vertex) (i : Vertex) (hi : i ∈ S) :
      IsAffineOpen (S.inf (coordinateOpen φ)) := by
    rw [← CycleQ2HodgeTwistFaces.face_inf φ i S hi]
    exact CycleQ2HodgeTwistFaces.face_affine φ i _
  apply CycleQ2HodgeTwistCoordinates.ordinary_vanishing (nativeLaurentSections φ h k)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)
  · intro i
    simpa using ha {i} i (by simp)
  · intro i j
    simpa using ha {i,j} i (by simp)
  · intro i
    refine { app := fun V hV => (chartFrame φ k i V hV).toAddEquiv, naturality := ?_ }
    intro V W hW hV s
    exact (CycleQ2HodgeAtlasLine.coordinate_restrict (CycleQ2HodgeThreefoldTwist.cocycle φ k) i hV hW s).symm

open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)

/-- Degree-zero frame coordinates read sections of the actual structure sheaf. -/
def structureChart : Chart (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ) R where
  common := torus φ
  le := torus_le φ
  coordinates := (chart φ h 0).coordinates.comp
    (chartFrame φ 0 0 (torus φ) (torus_le φ 0)).symm.toAddEquiv.toAddMonoidHom

private abbrev structureFace (i : Vertex) (S : Finset Vertex) (hi : i ∈ S) :=
  (chartFrame φ 0 i (S.inf (coordinateOpen φ)) (Finset.inf_le hi)).symm.toAddEquiv.trans
    (twistCoordinates φ i h S hi 0)

theorem read_structure_face (i : Vertex) (S : Finset Vertex) (hi : i ∈ S)
    (s : Γ(threefold φ, S.inf (coordinateOpen φ))) :
    read (structureChart φ h) (torus_le_face φ S) s = (structureFace φ h i S hi s).val := by
  let si := (chartFrame φ 0 i (S.inf (coordinateOpen φ)) (Finset.inf_le hi)).symm s
  let r := torus_le_face φ S
  let W := torus φ
  let o := structureAdditiveSheaf (threefold φ)
  have hframe : (chartFrame φ 0 0 W (torus_le φ 0)).symm (res o r s) =
      res (F φ 0) r si := by
    apply (chartFrame φ 0 0 W (torus_le φ 0)).injective
    rw [LinearEquiv.apply_symm_apply, chartFrame_transition φ 0 0 i W (torus_le φ 0) (torus_le φ i)]
    simp only [zpow_zero, Units.val_one, one_mul]
    have hr := CycleQ2HodgeAtlasLine.coordinate_restrict (CycleQ2HodgeThreefoldTwist.cocycle φ 0)
      i (Finset.inf_le hi) r si
    change chartFrame φ 0 i W (torus_le φ i) (res (F φ 0) r si) = res o r (chartFrame φ 0 i (S.inf (coordinateOpen φ)) (Finset.inf_le hi) si) at hr
    simpa only [si, LinearEquiv.apply_symm_apply] using hr.symm
  change (chart φ h 0).coordinates ((chartFrame φ 0 0 W (torus_le φ 0)).symm (res o r s)) = _
  rw [hframe]
  exact read_face φ h 0 i S hi si

/-- The common Laurent chart also computes the native structure sheaf directly. -/
theorem structureLaurentSections : HasLaurentSections (structureChart φ h) 0 where
  injective S hS := by
    obtain ⟨i,hi⟩ := hS
    intro x y e
    change read (structureChart φ h) (torus_le_face φ S) x =
      read (structureChart φ h) (torus_le_face φ S) y at e
    rw [read_structure_face φ h i S hi, read_structure_face φ h i S hi] at e
    exact (structureFace φ h i S hi).injective (Subtype.ext e)
  range_eq S hS := by
    obtain ⟨i,hi⟩ := hS
    ext p
    constructor
    · rintro ⟨s,rfl⟩
      rw [read_structure_face φ h i S hi]
      exact (structureFace φ h i S hi s).property
    · intro hp
      let v : sections R 0 S := ⟨p,hp⟩
      refine ⟨(structureFace φ h i S hi).symm v, ?_⟩
      rw [read_structure_face φ h i S hi, AddEquiv.apply_symm_apply]

end CycleQ2HodgeTwistTorusChart

#print axioms CycleQ2HodgeTwistTorusChart.nativeLaurentSections
#print axioms CycleQ2HodgeTwistTorusChart.globalSections

#print axioms CycleQ2HodgeTwistTorusChart.ordinary_vanishing

#print axioms CycleQ2HodgeTwistTorusChart.structureLaurentSections
