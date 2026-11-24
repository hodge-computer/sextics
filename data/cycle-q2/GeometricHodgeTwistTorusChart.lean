import Proposal.GeometricHodgeTwistAnchor
import Proposal.GeometricHodgeTwistCoordinates
import Proposal.GeometricHodgeTwistGlobal
import Proposal.GeometricHodgeTwistMultiplication

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

/-! ## Top residues of the actual moving threefold

These are section quotients on the original four projective opens. The
normalization is the coefficient of the homogeneous degree-zero fraction
`w²/(x₀x₁x₂x₃)`; a canonical-form identification is a separate map.
-/

def structureTopSectionTrace : Γ(threefold φ, torus φ) →+ R :=
  CycleQ2HodgeTwistCoordinates.nativeTopSectionTrace (structureLaurentSections φ h)

def structureTopTraceEquiv :
    CycleQ2HodgeTwistCoordinates.NativeTopQuotient
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ) ≃+ R :=
  CycleQ2HodgeTwistCoordinates.nativeTopTraceEquiv (structureLaurentSections φ h)

theorem structure_top_boundary_iff_trace_zero (s : Γ(threefold φ, torus φ)) :
    s ∈ (CycleQ2HodgeTwistCoordinates.nativeTopBoundary
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ)).range ↔
      structureTopSectionTrace φ h s = 0 :=
  CycleQ2HodgeTwistCoordinates.native_top_mem_boundary_iff_trace_zero
    (structureLaurentSections φ h) s

def structureTopGenerator (a : R) : Γ(threefold φ, torus φ) :=
  (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
    (structureLaurentSections φ h)).symm (CycleQ2HodgeTwistCech.topGenerator a)

@[simp] theorem structureTopSectionTrace_generator (a : R) :
    structureTopSectionTrace φ h (structureTopGenerator φ h a) = a := by
  change CycleQ2HodgeTwistCech.topCoefficient
    (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
      ((CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
        (structureLaurentSections φ h)).symm (CycleQ2HodgeTwistCech.topGenerator a))) = a
  rw [AddEquiv.apply_symm_apply, CycleQ2HodgeTwistCech.topCoefficient_topGenerator]

/-- The actual structure section is the evaluation of its common Laurent expansion. -/
theorem structureTopCoordinates_evaluate (s : Γ(threefold φ, torus φ)) :
    s = evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      ((CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
        (structureLaurentSections φ h) s).val) := by
  let v := (chartFrame φ 0 0 (torus φ) (torus_le φ 0)).symm s
  have he := face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ 0) 0 v
  have hc : (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
      (structureLaurentSections φ h) s).val =
      (twistCoordinates φ 0 h Finset.univ (Finset.mem_univ 0) 0 v).val :=
    read_structure_face φ h 0 Finset.univ (Finset.mem_univ 0) s
  rw [hc]
  simpa only [res_self, v, LinearEquiv.apply_symm_apply] using he

/-- This generator is the original homogeneous fraction, not a formally
adjoined class with a prescribed trace. -/
theorem structureTopGenerator_fraction (a : R) :
    structureTopGenerator φ h a = commonCoefficient φ a *
      CycleQ2HodgeTwistMonomials.monomial φ (torus φ) (torus_le φ) 0 2
        CycleQ2HodgeTwistCech.negativeExponent := by
  rw [structureTopCoordinates_evaluate φ h (structureTopGenerator φ h a)]
  change evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
    ((CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
      ((CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
        (structureLaurentSections φ h)).symm (CycleQ2HodgeTwistCech.topGenerator a))).val) = _
  rw [AddEquiv.apply_symm_apply]
  classical
  simp [evaluate, CycleQ2HodgeTwistCech.topGenerator]

theorem structureTopSectionTrace_fraction :
    structureTopSectionTrace φ h
      (CycleQ2HodgeTwistMonomials.monomial φ (torus φ) (torus_le φ) 0 2
        CycleQ2HodgeTwistCech.negativeExponent) = 1 := by
  have hg := structureTopGenerator_fraction φ h (1 : R)
  rw [map_one, one_mul] at hg
  rw [← hg, structureTopSectionTrace_generator]

/-- Scalar multiplication in the original coefficient ring acts on every
Laurent coefficient through its actual structure-section map. -/
theorem structureTopCoordinates_mul_constant (a : R) (s : Γ(threefold φ, torus φ)) :
    CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
      (commonCoefficient φ a * s) =
        CycleQ2HodgeTwistCech.scalarSection a
          (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h) s) := by
  let E := CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
  let p := CycleQ2HodgeTwistCech.scalarSection a (E s)
  let v := E.symm p
  have hv : v = commonCoefficient φ a * s := by
    rw [structureTopCoordinates_evaluate φ h v]
    change evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      ((E (E.symm p)).val) = _
    rw [AddEquiv.apply_symm_apply]
    change evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      (a • (E s).val) = _
    rw [CycleQ2HodgeTwistMonomials.evaluate_smul]
    exact congrArg (fun z => commonCoefficient φ a * z)
      (structureTopCoordinates_evaluate φ h s).symm
  change E (commonCoefficient φ a * s) = p
  rw [← hv]
  exact E.apply_symm_apply p

theorem structureTopSectionTrace_mul_constant (a : R) (s : Γ(threefold φ, torus φ)) :
    structureTopSectionTrace φ h (commonCoefficient φ a * s) =
      a * structureTopSectionTrace φ h s := by
  change CycleQ2HodgeTwistCech.topCoefficient
    (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
      (commonCoefficient φ a * s)) = _
  rw [structureTopCoordinates_mul_constant, CycleQ2HodgeTwistCech.topCoefficient_scalarSection]
  rfl

/-- Evaluation of the common Laurent expansion of a twist section,
including when its original face does not contain the zeroth chart. -/
theorem frame_read_evaluate {W : (threefold φ).Opens} (hW : torus φ ≤ W)
    (s : Γ(twist φ k, W)) :
    chartFrame φ k 0 (torus φ) (torus_le φ 0)
      (res (F φ k) hW s) =
        evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
          (read (chart φ h k) hW s) := by
  let v := res (F φ k) hW s
  have he := face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ 0) k v
  simpa only [res_self] using he

private theorem omittedFace_nonempty (i : Vertex) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩

/-- The native degree-one section `w²/∏_{j≠i} xⱼ` on its actual triple open. -/
def partialGenerator (i : Vertex) :
    Γ(twist φ 1, (Finset.univ.erase i).inf (coordinateOpen φ)) :=
  (CycleQ2HodgeTwistCoordinates.faceCoordinates (nativeLaurentSections φ h 1)
    (Finset.univ.erase i) (omittedFace_nonempty i)).symm
      (CycleQ2HodgeTwistCech.partialGenerator i (1 : R))

theorem partialGenerator_read (i : Vertex) :
    read (chart φ h 1) (torus_le_face φ (Finset.univ.erase i))
      (partialGenerator φ h i) =
        (CycleQ2HodgeTwistCech.partialGenerator i (1 : R)).val := by
  exact congrArg Subtype.val
    ((CycleQ2HodgeTwistCoordinates.faceCoordinates (nativeLaurentSections φ h 1)
      (Finset.univ.erase i) (omittedFace_nonempty i)).apply_symm_apply _)

theorem partialGenerator_coordinates (i a : Vertex) (ha : a ∈ Finset.univ.erase i) :
    twistCoordinates φ a h (Finset.univ.erase i) ha 1 (partialGenerator φ h i) =
      CycleQ2HodgeTwistCech.partialGenerator i (1 : R) := by
  apply Subtype.ext
  exact (read_face φ h 1 a (Finset.univ.erase i) ha (partialGenerator φ h i)).symm.trans
    (partialGenerator_read φ h i)

/-- The partial generator is the omitted coordinate times the original
top residue fraction when read on the common torus. -/
theorem partialGenerator_frame (i : Vertex) :
    chartFrame φ 1 0 (torus φ) (torus_le φ 0)
      (res (F φ 1) (torus_le_face φ (Finset.univ.erase i))
        (partialGenerator φ h i)) =
      CycleQ2HodgeTwistRatios.ratio φ 0 i (torus φ) (torus_le φ 0) *
        structureTopGenerator φ h 1 := by
  rw [frame_read_evaluate φ h 1, partialGenerator_read]
  rw [structureTopGenerator_fraction, map_one, one_mul]
  have he : evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      (CycleQ2HodgeTwistCech.partialGenerator i (1 : R)).val =
      CycleQ2HodgeTwistMonomials.monomial φ (torus φ) (torus_le φ) 0 2
        (CycleQ2HodgeTwistCech.partialExponent i) := by
    classical
    simp [evaluate, CycleQ2HodgeTwistCech.partialGenerator]
  rw [he]
  exact CycleQ2HodgeTwistMonomials.partial_monomial φ (torus φ) (torus_le φ) i 0

/-- Multiplication by a homogeneous quadric gives the actual cubic-twist
lift on an omitted-coordinate face. -/
def quadricLift (i : Vertex) (q : CycleQ2GeometricHodgeThreefold.cone φ)
    (hq : q ∈ CycleQ2GeometricHodgeThreefold.grade φ 2) :
    Γ(twist φ 3, (Finset.univ.erase i).inf (coordinateOpen φ)) :=
  (CycleQ2HodgeThreefoldTwist.multiply φ q hq 1 3 (by decide)).app _
    (partialGenerator φ h i)

theorem quadricLift_frame (i : Vertex) (q : CycleQ2GeometricHodgeThreefold.cone φ)
    (hq : q ∈ CycleQ2GeometricHodgeThreefold.grade φ 2) :
    chartFrame φ 3 0 (torus φ) (torus_le φ 0)
      (res (F φ 3) (torus_le_face φ (Finset.univ.erase i))
        (quadricLift φ h i q hq)) =
      CycleQ2HodgeTwistRatios.normalized φ 0 q hq (torus φ) (torus_le φ 0) *
        (CycleQ2HodgeTwistRatios.ratio φ 0 i (torus φ) (torus_le φ 0) *
          structureTopGenerator φ h 1) := by
  let m := CycleQ2HodgeThreefoldTwist.multiply φ q hq 1 3 (by decide)
  have hn := (CycleQ2SeedSectionSheafLocal.moduleRes_app m
    (torus_le_face φ (Finset.univ.erase i)) (partialGenerator φ h i)).symm
  change m.app (torus φ)
      (res (F φ 1) (torus_le_face φ (Finset.univ.erase i)) (partialGenerator φ h i)) =
    res (F φ 3) (torus_le_face φ (Finset.univ.erase i)) (quadricLift φ h i q hq) at hn
  rw [← hn, CycleQ2HodgeThreefoldTwist.multiply_frame, partialGenerator_frame]

/-- The same top fraction as a section of the original degree-zero twist. -/
def twistTopGenerator : Γ(twist φ 0, torus φ) :=
  (chartFrame φ 0 0 (torus φ) (torus_le φ 0)).symm (structureTopGenerator φ h 1)

@[simp] theorem twistTopGenerator_frame :
    chartFrame φ 0 0 (torus φ) (torus_le φ 0) (twistTopGenerator φ h) =
      structureTopGenerator φ h 1 := LinearEquiv.apply_symm_apply _ _

/-- The degree-zero twist trace reads the original structure coefficient
in its zeroth chart frame. -/
theorem twistTopSectionTrace_frame (s : Γ(twist φ 0, torus φ)) :
    CycleQ2HodgeTwistCoordinates.nativeTopSectionTrace (nativeLaurentSections φ h 0) s =
      structureTopSectionTrace φ h
        (chartFrame φ 0 0 (torus φ) (torus_le φ 0) s) := by
  change CycleQ2HodgeTwistCech.topCoefficient
      (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (nativeLaurentSections φ h 0) s) =
    CycleQ2HodgeTwistCech.topCoefficient
      (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h)
        (chartFrame φ 0 0 (torus φ) (torus_le φ 0) s))
  apply congrArg CycleQ2HodgeTwistCech.topCoefficient
  apply Subtype.ext
  change (chart φ h 0).coordinates (res (F φ 0) le_rfl s) =
    (chart φ h 0).coordinates ((chartFrame φ 0 0 (torus φ) (torus_le φ 0)).symm
      (res (structureAdditiveSheaf (threefold φ)) le_rfl
        (chartFrame φ 0 0 (torus φ) (torus_le φ 0) s)))
  rw [res_self, res_self, LinearEquiv.symm_apply_apply]

@[simp] theorem twistTopSectionTrace_generator :
    CycleQ2HodgeTwistCoordinates.nativeTopSectionTrace (nativeLaurentSections φ h 0)
      (twistTopGenerator φ h) = 1 := by
  rw [twistTopSectionTrace_frame, twistTopGenerator_frame, structureTopSectionTrace_generator]

def assembledCubic (q : Vertex → CycleQ2GeometricHodgeThreefold.cone φ) :
    CycleQ2GeometricHodgeThreefold.cone φ :=
  ∑ i, CycleQ2GeometricHodgeThreefold.coord φ i.castSucc * q i

theorem assembledCubic_homogeneous (q : Vertex → CycleQ2GeometricHodgeThreefold.cone φ)
    (hq : ∀ i, q i ∈ CycleQ2GeometricHodgeThreefold.grade φ 2) :
    assembledCubic φ q ∈ CycleQ2GeometricHodgeThreefold.grade φ 3 :=
  (CycleQ2GeometricHodgeThreefold.grade φ 3).sum_mem (fun i _ =>
    SetLike.mul_mem_graded (CycleQ2GeometricHodgeThreefold.weightOne_mem_grade φ i) (hq i))

/-- The four actual triple sections, indexed by the missing coordinate,
with the signs required to make their Čech boundary positive. -/
def quadricBoundaryLift (q : Vertex → CycleQ2GeometricHodgeThreefold.cone φ)
    (hq : ∀ i, q i ∈ CycleQ2GeometricHodgeThreefold.grade φ 2) :
    CycleQ2HodgeTwistCoordinates.NativeTopFaces (F := F φ 3) (U := coordinateOpen φ) :=
  fun i => if i = 1 ∨ i = 3 then -quadricLift φ h i (q i) (hq i)
    else quadricLift φ h i (q i) (hq i)

/-- The finite homogeneous identity `h=∑xᵢqᵢ` is the boundary identity of
genuine twist sections on the original projective cover. -/
theorem quadricBoundaryLift_boundary
    (q : Vertex → CycleQ2GeometricHodgeThreefold.cone φ)
    (hq : ∀ i, q i ∈ CycleQ2GeometricHodgeThreefold.grade φ 2) :
    CycleQ2HodgeTwistCoordinates.nativeTopBoundary (quadricBoundaryLift φ h q hq) =
      (CycleQ2HodgeThreefoldTwist.multiply φ (assembledCubic φ q)
        (assembledCubic_homogeneous φ q hq) 0 3 (by decide)).app (torus φ)
          (twistTopGenerator φ h) := by
  apply (chartFrame φ 3 0 (torus φ) (torus_le φ 0)).injective
  change chartFrame φ 3 0 (torus φ) (torus_le φ 0)
      (res (F φ 3) (torus_le_face φ (Finset.univ.erase 0)) (quadricLift φ h 0 (q 0) (hq 0)) -
        res (F φ 3) (torus_le_face φ (Finset.univ.erase 1)) (-quadricLift φ h 1 (q 1) (hq 1)) +
        res (F φ 3) (torus_le_face φ (Finset.univ.erase 2)) (quadricLift φ h 2 (q 2) (hq 2)) -
        res (F φ 3) (torus_le_face φ (Finset.univ.erase 3)) (-quadricLift φ h 3 (q 3) (hq 3))) = _
  simp only [map_neg, sub_neg_eq_add, map_add]
  rw [quadricLift_frame, quadricLift_frame, quadricLift_frame, quadricLift_frame,
    CycleQ2HodgeThreefoldTwist.multiply_frame, twistTopGenerator_frame]
  rw [CycleQ2HodgeTwistRatios.normalized_sum]
  simp_rw [CycleQ2HodgeTwistRatios.normalized_mul]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change _ =
    (CycleQ2HodgeTwistRatios.ratio φ 0 0 (torus φ) (torus_le φ 0) *
        CycleQ2HodgeTwistRatios.normalized φ 0 (q 0) (hq 0) (torus φ) (torus_le φ 0) +
      (CycleQ2HodgeTwistRatios.ratio φ 0 1 (torus φ) (torus_le φ 0) *
        CycleQ2HodgeTwistRatios.normalized φ 0 (q 1) (hq 1) (torus φ) (torus_le φ 0) +
      (CycleQ2HodgeTwistRatios.ratio φ 0 2 (torus φ) (torus_le φ 0) *
        CycleQ2HodgeTwistRatios.normalized φ 0 (q 2) (hq 2) (torus φ) (torus_le φ 0) +
       CycleQ2HodgeTwistRatios.ratio φ 0 3 (torus φ) (torus_le φ 0) *
        CycleQ2HodgeTwistRatios.normalized φ 0 (q 3) (hq 3) (torus φ) (torus_le φ 0)))) *
      structureTopGenerator φ h 1
  ring

/-- Restriction to the common torus is injective on the actual structure
sections of every nonempty original coordinate face. -/
theorem structure_restrict_torus_injective (B : Finset Vertex) (hB : B.Nonempty) :
    Function.Injective (res (structureAdditiveSheaf (threefold φ)) (torus_le_face φ B)) := by
  intro s t hst
  apply (structureLaurentSections φ h).injective B hB
  exact congrArg (structureChart φ h).coordinates hst

open CycleQ2GeometricHodgeThreefold (cone grade coord coord_mem_grade weightOne_mem_grade)
open CycleQ2HodgeTwistRatios (normalized normalized_mul normalized_restrict ratio)

private theorem coordinateProduct_homogeneous (B : Finset Vertex) :
    (∏ j ∈ B, coord φ j.castSucc) ∈ grade φ B.card := by
  simpa using (SetLike.prod_mem_graded (grade φ) (fun _ : Vertex => 1)
    (fun j => coord φ j.castSucc) (F := B) (fun j _ => weightOne_mem_grade φ j))

private theorem normalized_coordinateProduct (B : Finset Vertex) (a : Vertex)
    (W : (threefold φ).Opens) (hW : W ≤ coordinateOpen φ a) :
    normalized φ a (∏ j ∈ B, coord φ j.castSucc) (coordinateProduct_homogeneous φ B) W hW =
      ∏ j ∈ B, ratio φ a j W hW := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    apply Subtype.ext
    funext q
    apply HomogeneousLocalization.val_injective
    change Localization.mk (1 : cone φ)
      (1 : q.val.asHomogeneousIdeal.toIdeal.primeCompl) =
        (1 : HomogeneousLocalization (grade φ)
          q.val.asHomogeneousIdeal.toIdeal.primeCompl).val
    rw [HomogeneousLocalization.val_one]
    exact Localization.mk_self 1
  | insert j B hj ih =>
    have hc : (insert j B).card = 1 + B.card := by simp [hj, Nat.add_comm]
    calc
      _ = normalized φ a (coord φ j.castSucc * ∏ l ∈ B, coord φ l.castSucc)
          (SetLike.mul_mem_graded (weightOne_mem_grade φ j)
            (coordinateProduct_homogeneous φ B)) W hW := by
        simp only [hc, Finset.prod_insert hj]
      _ = ratio φ a j W hW * normalized φ a (∏ l ∈ B, coord φ l.castSucc)
          (coordinateProduct_homogeneous φ B) W hW :=
        normalized_mul φ a _ _ (weightOne_mem_grade φ j)
          (coordinateProduct_homogeneous φ B) W hW
      _ = _ := by rw [ih, Finset.prod_insert hj]

/-- The three original coordinates inverted on the omitted-coordinate face. -/
def partialDenominator (i : Vertex) : cone φ :=
  ∏ j ∈ Finset.univ.erase i, coord φ j.castSucc

theorem partialDenominator_homogeneous (i : Vertex) :
    partialDenominator φ i ∈ grade φ 3 := by
  simpa [partialDenominator] using
    coordinateProduct_homogeneous φ (Finset.univ.erase i)

theorem weightTwoSquare_homogeneous :
    (coord φ (Fin.last 4)) ^ 2 ∈ grade φ 4 := by
  simpa using SetLike.pow_mem_graded 2 (coord_mem_grade φ (Fin.last 4))

theorem partialDenominator_normalized (i a : Vertex)
    (W : (threefold φ).Opens) (hW : W ≤ coordinateOpen φ a) :
    normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i) W hW =
      ∏ j ∈ Finset.univ.erase i, ratio φ a j W hW := by
  simpa [partialDenominator] using
    normalized_coordinateProduct φ (Finset.univ.erase i) a W hW

/-- The denominator is a unit on the whole triple face; this does not
invert the omitted coordinate. -/
theorem partialDenominator_normalized_isUnit (i a : Vertex)
    (ha : a ∈ Finset.univ.erase i) :
    IsUnit (normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i)
      ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha)) := by
  rw [partialDenominator_normalized]
  exact IsUnit.prod_iff.mpr (fun j hj =>
    (transition φ a j ((Finset.univ.erase i).inf (coordinateOpen φ))
      (Finset.inf_le ha) (Finset.inf_le hj)).isUnit)

theorem partialGenerator_frame_at (i a : Vertex) (ha : a ∈ Finset.univ.erase i) :
    chartFrame φ 1 a (torus φ) (torus_le φ a)
      (res (F φ 1) (torus_le_face φ (Finset.univ.erase i)) (partialGenerator φ h i)) =
      CycleQ2HodgeTwistMonomials.monomial φ (torus φ) (torus_le φ) a 2
        (CycleQ2HodgeTwistCech.partialExponent i) := by
  have he := face_frame_evaluation φ a h (Finset.univ.erase i) ha 1 (partialGenerator φ h i)
  rw [partialGenerator_coordinates] at he
  simpa [evaluate, CycleQ2HodgeTwistCech.partialGenerator] using he

private theorem partial_units_cancel (i a : Vertex) :
    (∏ j ∈ Finset.univ.erase i, transition φ a j (torus φ) (torus_le φ a) (torus_le φ j)) *
      CycleQ2HodgeTwistMonomials.units φ (torus φ) (torus_le φ) a
        (CycleQ2HodgeTwistCech.partialExponent i) = 1 := by
  classical
  let u := fun j => transition φ a j (torus φ) (torus_le φ a) (torus_le φ j)
  have he : CycleQ2HodgeTwistMonomials.units φ (torus φ) (torus_le φ) a
      (CycleQ2HodgeTwistCech.partialExponent i) = ∏ j ∈ Finset.univ.erase i, (u j)⁻¹ := by
    symm
    calc
      _ = ∏ j ∈ Finset.univ.erase i, u j ^ CycleQ2HodgeTwistCech.partialExponent i j := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [CycleQ2HodgeTwistCech.partialExponent, (Finset.mem_erase.mp hj).1]
      _ = ∏ j : Vertex, u j ^ CycleQ2HodgeTwistCech.partialExponent i j := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro j _ hj
        have hji : j = i := by
          by_contra hji
          exact hj (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
        simp [hji, CycleQ2HodgeTwistCech.partialExponent]
      _ = _ := rfl
  rw [he]
  change (∏ j ∈ Finset.univ.erase i, u j) *
    (∏ j ∈ Finset.univ.erase i, (u j)⁻¹) = 1
  rw [← Finset.prod_mul_distrib]
  simp

/-- The native partial generator satisfies its literal fraction identity
on the entire original triple face, in every anchor belonging to that
face. No assumption about the omitted coordinate is used. -/
theorem partialGenerator_fraction (i a : Vertex) (ha : a ∈ Finset.univ.erase i) :
    normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i)
        ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha) *
      chartFrame φ 1 a ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha)
        (partialGenerator φ h i) =
    normalized φ a ((coord φ (Fin.last 4)) ^ 2) (weightTwoSquare_homogeneous φ)
      ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha) := by
  apply structure_restrict_torus_injective φ h (Finset.univ.erase i) (omittedFace_nonempty i)
  change CycleQ2GeometricProjectiveCurve.Twisted.res (threefold φ).sheaf
      (torus_le_face φ (Finset.univ.erase i))
      (normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i)
          ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha) *
        chartFrame φ 1 a ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha)
          (partialGenerator φ h i)) =
    CycleQ2GeometricProjectiveCurve.Twisted.res (threefold φ).sheaf
      (torus_le_face φ (Finset.univ.erase i))
      (normalized φ a ((coord φ (Fin.last 4)) ^ 2) (weightTwoSquare_homogeneous φ)
        ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha))
  rw [map_mul, normalized_restrict, normalized_restrict]
  have hf := CycleQ2HodgeAtlasLine.coordinate_restrict (CycleQ2HodgeThreefoldTwist.cocycle φ 1)
    a (Finset.inf_le ha) (torus_le_face φ (Finset.univ.erase i)) (partialGenerator φ h i)
  rw [← hf, partialGenerator_frame_at φ h i a ha, partialDenominator_normalized]
  have hu := congrArg Units.val (partial_units_cancel φ i a)
  have hv : (∏ j ∈ Finset.univ.erase i, ratio φ a j (torus φ) (torus_le φ a)) *
      (CycleQ2HodgeTwistMonomials.units φ (torus φ) (torus_le φ) a
        (CycleQ2HodgeTwistCech.partialExponent i)).val = 1 := by
    simpa [CycleQ2HodgeTwistRatios.transition] using hu
  rw [CycleQ2HodgeTwistMonomials.monomial, ← mul_assoc, hv, one_mul]
  simpa only [pow_two, CycleQ2HodgeTwistMonomials.weightTwo] using
    (normalized_mul φ a (coord φ (Fin.last 4)) (coord φ (Fin.last 4))
      (coord_mem_grade φ (Fin.last 4)) (coord_mem_grade φ (Fin.last 4))
      (torus φ) (torus_le φ a)).symm

/-- Clearing the same whole-face denominator after multiplication by a
quadric gives the original homogeneous numerator of degree six. -/
theorem quadricLift_fraction (i a : Vertex) (ha : a ∈ Finset.univ.erase i)
    (q : cone φ) (hq : q ∈ grade φ 2) :
    normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i)
        ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha) *
      chartFrame φ 3 a ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha)
        (quadricLift φ h i q hq) =
    normalized φ a (q * (coord φ (Fin.last 4)) ^ 2)
      (SetLike.mul_mem_graded hq (weightTwoSquare_homogeneous φ))
      ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le ha) := by
  rw [quadricLift, CycleQ2HodgeThreefoldTwist.multiply_frame]
  let W := (Finset.univ.erase i).inf (coordinateOpen φ)
  let d := normalized φ a (partialDenominator φ i) (partialDenominator_homogeneous φ i)
    W (Finset.inf_le ha)
  let r := normalized φ a q hq W (Finset.inf_le ha)
  let s := chartFrame φ 1 a W (Finset.inf_le ha) (partialGenerator φ h i)
  change d * (r * s) = _
  rw [show d * (r * s) = r * (d * s) by ring]
  rw [show d * s = normalized φ a ((coord φ (Fin.last 4)) ^ 2)
    (weightTwoSquare_homogeneous φ) W (Finset.inf_le ha) from
      partialGenerator_fraction φ h i a ha]
  exact (normalized_mul φ a q ((coord φ (Fin.last 4)) ^ 2)
    hq (weightTwoSquare_homogeneous φ) W (Finset.inf_le ha)).symm

/-- Positive twists have no top Čech obstruction on this actual projective cover. -/
theorem positive_twist_top_boundary_surjective (hk : 0 < k) :
    Function.Surjective (CycleQ2HodgeTwistCoordinates.nativeTopBoundary
      (F := F φ k) (U := coordinateOpen φ)) :=
  CycleQ2HodgeTwistCoordinates.nativeTopBoundary_surjective_of_positive
    (nativeLaurentSections φ h k) hk

end CycleQ2HodgeTwistTorusChart

#print axioms CycleQ2HodgeTwistTorusChart.nativeLaurentSections
#print axioms CycleQ2HodgeTwistTorusChart.globalSections

#print axioms CycleQ2HodgeTwistTorusChart.ordinary_vanishing

#print axioms CycleQ2HodgeTwistTorusChart.structureLaurentSections
#print axioms CycleQ2HodgeTwistTorusChart.structureTopTraceEquiv
#print axioms CycleQ2HodgeTwistTorusChart.structureTopSectionTrace_fraction
#print axioms CycleQ2HodgeTwistTorusChart.positive_twist_top_boundary_surjective
#print axioms CycleQ2HodgeTwistTorusChart.partialGenerator_fraction
#print axioms CycleQ2HodgeTwistTorusChart.partialDenominator_normalized_isUnit
#print axioms CycleQ2HodgeTwistTorusChart.quadricLift_fraction
