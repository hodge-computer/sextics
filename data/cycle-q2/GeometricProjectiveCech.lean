import Proposal.GeometricProjectiveFrames
import Proposal.GeometricTwistedSheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual projective Cech class in derived cohomology

The homogeneous local modules are identified with sections of the actual
twisted additive sheaf, including their restriction maps. Mayer-Vietoris
exactness gives an injection from the existing degree-one Cech quotient
into derived cohomology. No affine acyclicity or Serre comparison is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta

def degreeOneSheaf (r θ : ℂ) :
    Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0} :=
  Twisted.sheaf (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)

def firstSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, firstProjectivePatch r θ) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (firstProjectivePatch r θ) le_rfl

def secondSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, secondProjectivePatch r θ) :=
  Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (secondProjectivePatch r θ) le_rfl

def overlapSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, overlapProjectivePatch r θ) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)

def firstDegreeOneSectionsEquiv (r θ : ℂ) :
    FirstDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ)) :=
  (firstDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((firstProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (firstSheafFrame r θ).symm)

def secondDegreeOneSectionsEquiv (r θ : ℂ) :
    SecondDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ)) :=
  (secondDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((secondProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (secondSheafFrame r θ).symm)

def overlapDegreeOneSectionsEquiv (r θ : ℂ) :
    OverlapDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) :=
  (overlapFirstDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((overlapProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (overlapSheafFrame r θ).symm)

@[simp] theorem firstDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : FirstDegreeOne r θ) :
    firstSheafFrame r θ (firstDegreeOneSectionsEquiv r θ z) =
      (firstProjectiveSectionsIso r θ).hom ((firstDegreeOneEquiv r θ).symm z) :=
  (firstSheafFrame r θ).apply_symm_apply _

@[simp] theorem secondDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : SecondDegreeOne r θ) :
    secondSheafFrame r θ (secondDegreeOneSectionsEquiv r θ z) =
      (secondProjectiveSectionsIso r θ).hom ((secondDegreeOneEquiv r θ).symm z) :=
  (secondSheafFrame r θ).apply_symm_apply _

@[simp] theorem overlapDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : OverlapDegreeOne r θ) :
    overlapSheafFrame r θ (overlapDegreeOneSectionsEquiv r θ z) =
      (overlapProjectiveSectionsIso r θ).hom ((overlapFirstDegreeOneEquiv r θ).symm z) :=
  (overlapSheafFrame r θ).apply_symm_apply _

theorem firstSheafFrame_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ))) :
    overlapSheafFrame r θ
        ((degreeOneSheaf r θ).obj.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op s) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
          (firstSheafFrame r θ s) :=
  Twisted.firstLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    ((overlapProjectivePatch_eq r θ).le.trans inf_le_left) le_rfl s

theorem secondSheafFrame_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ))) :
    overlapSheafFrame r θ
        ((degreeOneSheaf r θ).obj.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s) =
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) *
        (projectiveCurve r θ).presheaf.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op
            (secondSheafFrame r θ s) := by
  have h := Twisted.localSections_transition (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) le_rfl
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s)
  exact h.trans (congrArg₂ (fun a b => a * b)
    (Twisted.res_self (projectiveCurve r θ).sheaf (overlapProjectivePatch r θ)
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)))
    (Twisted.secondLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      ((overlapProjectivePatch_eq r θ).le.trans inf_le_right) le_rfl s))

theorem firstDegreeOneSectionsEquiv_restriction (r θ : ℂ) (z : FirstDegreeOne r θ) :
    (degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
          (firstDegreeOneSectionsEquiv r θ z) =
      overlapDegreeOneSectionsEquiv r θ (firstDegreeOneRestriction r θ z) := by
  obtain ⟨a, rfl⟩ := (firstDegreeOneEquiv r θ).surjective z
  apply (overlapSheafFrame r θ).injective
  rw [firstSheafFrame_restriction, firstDegreeOneSectionsEquiv_coordinate,
    overlapDegreeOneSectionsEquiv_coordinate, firstDegreeOneEquiv_restriction]
  simpa only [LinearEquiv.symm_apply_apply, firstProjectivePatch,
    overlapProjectivePatch] using
    firstProjectiveRestriction_is_sheaf_restriction r θ a

theorem secondDegreeOneSectionsEquiv_restriction (r θ : ℂ) (z : SecondDegreeOne r θ) :
    (degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op
          (secondDegreeOneSectionsEquiv r θ z) =
      overlapDegreeOneSectionsEquiv r θ (secondDegreeOneRestriction r θ z) := by
  obtain ⟨b, rfl⟩ := (secondDegreeOneEquiv r θ).surjective z
  apply (overlapSheafFrame r θ).injective
  rw [secondSheafFrame_restriction, secondDegreeOneSectionsEquiv_coordinate,
    overlapDegreeOneSectionsEquiv_coordinate, secondDegreeOneEquiv_restriction,
    ← overlapTransition_frame]
  simp only [LinearEquiv.symm_apply_apply]
  exact (congrArg
      (fun a : Γ(projectiveCurve r θ, overlapProjectivePatch r θ) =>
        (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) * a)
      (secondProjectiveRestriction_is_sheaf_restriction r θ b)).trans
    ((overlapProjectiveSectionsIso r θ).hom.hom.map_mul
      (overlapTransition r θ) (secondProjectiveRestriction r θ b)).symm

theorem firstDegreeOneSectionsEquiv_symm_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ))) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op s) =
      firstDegreeOneRestriction r θ ((firstDegreeOneSectionsEquiv r θ).symm s) := by
  obtain ⟨z, rfl⟩ := (firstDegreeOneSectionsEquiv r θ).surjective s
  rw [firstDegreeOneSectionsEquiv_restriction, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

theorem secondDegreeOneSectionsEquiv_symm_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ))) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s) =
      secondDegreeOneRestriction r θ ((secondDegreeOneSectionsEquiv r θ).symm s) := by
  obtain ⟨z, rfl⟩ := (secondDegreeOneSectionsEquiv r θ).surjective s
  rw [secondDegreeOneSectionsEquiv_restriction, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-! ## Actual derived projective sheaf cohomology

Mayer-Vietoris exactness gives an injection from the degree-one Cech
quotient. It does not require affine acyclicity, and no surjectivity onto
derived cohomology is claimed.
-/

def projectiveMayerVietoris (r θ : ℂ) (hr : r ≠ 0) :
    (Opens.grothendieckTopology (projectiveCurve r θ)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := overlapProjectivePatch r θ
      X₂ := firstProjectivePatch r θ
      X₃ := secondProjectivePatch r θ
      X₄ := ⊤
      f₁₂ := homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)
      f₁₃ := homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    (projective_twoOpen_cover r θ hr).symm (overlapProjectivePatch_eq r θ)

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Derived cohomology of the constructed additive sheaf on the actual
projective scheme. The sheaf has the proved degree-one affine frames. -/
abbrev ProjectiveSheafH1 (r θ : ℂ) :=
  (degreeOneSheaf r θ).H' 1 ⊤

open CycleQ2GeometricConeCech.HZero

def degreeOneConnecting (r θ : ℂ) (hr : r ≠ 0) :
    OverlapDegreeOne r θ →+ ProjectiveSheafH1 r θ :=
  ((projectiveMayerVietoris r θ hr).δ (degreeOneSheaf r θ) 0 1 rfl).hom.comp
    ((sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)).symm.toAddMonoidHom.comp
      (overlapDegreeOneSectionsEquiv r θ).toAddMonoidHom)

private theorem firstHZero_degreeOne (r θ : ℂ)
    (a : (degreeOneSheaf r θ).H' 0 (firstProjectivePatch r θ)) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)
        (((degreeOneSheaf r θ).cohomologyPresheaf 0).map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op a)) =
      firstDegreeOneRestriction r θ ((firstDegreeOneSectionsEquiv r θ).symm
        (sectionsEquiv (degreeOneSheaf r θ) (firstProjectivePatch r θ) a)) :=
  (congrArg (overlapDegreeOneSectionsEquiv r θ).symm
    (sectionsEquiv_naturality (degreeOneSheaf r θ)
      (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)) a)).trans
    (firstDegreeOneSectionsEquiv_symm_restriction r θ
      (sectionsEquiv (degreeOneSheaf r θ) (firstProjectivePatch r θ) a))

private theorem secondHZero_degreeOne (r θ : ℂ)
    (b : (degreeOneSheaf r θ).H' 0 (secondProjectivePatch r θ)) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)
        (((degreeOneSheaf r θ).cohomologyPresheaf 0).map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op b)) =
      secondDegreeOneRestriction r θ ((secondDegreeOneSectionsEquiv r θ).symm
        (sectionsEquiv (degreeOneSheaf r θ) (secondProjectivePatch r θ) b)) :=
  (congrArg (overlapDegreeOneSectionsEquiv r θ).symm
    (sectionsEquiv_naturality (degreeOneSheaf r θ)
      (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)) b)).trans
    (secondDegreeOneSectionsEquiv_symm_restriction r θ
      (sectionsEquiv (degreeOneSheaf r θ) (secondProjectivePatch r θ) b))

private theorem fromBiprod_degreeOne (r θ : ℂ) (hr : r ≠ 0)
    (a : (degreeOneSheaf r θ).H' 0 (firstProjectivePatch r θ))
    (b : (degreeOneSheaf r θ).H' 0 (secondProjectivePatch r θ)) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)
        ((projectiveMayerVietoris r θ hr).fromBiprod (degreeOneSheaf r θ) 0
          ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b)))) =
      degreeOneCoboundary r θ
        ((firstDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv (degreeOneSheaf r θ) (firstProjectivePatch r θ) a),
        (secondDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv (degreeOneSheaf r θ) (secondProjectivePatch r θ) b)) := by
  let e : (degreeOneSheaf r θ).H' 0 (overlapProjectivePatch r θ) →+
      OverlapDegreeOne r θ :=
    (overlapDegreeOneSectionsEquiv r θ).symm.toAddMonoidHom.comp
      (sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)).toAddMonoidHom
  have hformula := (projectiveMayerVietoris r θ hr).fromBiprod_biprodIsoProd_inv_apply
    (degreeOneSheaf r θ) a b
  exact (congrArg e hformula).trans
    ((e.map_sub
      (((degreeOneSheaf r θ).cohomologyPresheaf 0).map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op a)
      (((degreeOneSheaf r θ).cohomologyPresheaf 0).map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op b)).trans
      (congrArg₂ (fun u v : OverlapDegreeOne r θ => u - v)
        (firstHZero_degreeOne r θ a) (secondHZero_degreeOne r θ b)))

theorem degreeOneConnecting_coboundary (r θ : ℂ) (hr : r ≠ 0)
    (x : FirstDegreeOne r θ) (y : SecondDegreeOne r θ) :
    degreeOneConnecting r θ hr (degreeOneCoboundary r θ (x, y)) = 0 := by
  let F := degreeOneSheaf r θ
  let S := projectiveMayerVietoris r θ hr
  let a := (sectionsEquiv F (firstProjectivePatch r θ)).symm
    (firstDegreeOneSectionsEquiv r θ x)
  let b := (sectionsEquiv F (secondProjectivePatch r θ)).symm
    (secondDegreeOneSectionsEquiv r θ y)
  let z := (AddCommGrpCat.biprodIsoProd _ _).inv (a, b)
  have hz : (sectionsEquiv F (overlapProjectivePatch r θ)).symm
      (overlapDegreeOneSectionsEquiv r θ (degreeOneCoboundary r θ (x, y))) =
        S.fromBiprod F 0 z := by
    apply (sectionsEquiv F (overlapProjectivePatch r θ)).injective
    apply (overlapDegreeOneSectionsEquiv r θ).symm.injective
    dsimp only [F, S, z]
    rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    have hcoords : degreeOneCoboundary r θ
        ((firstDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv F (firstProjectivePatch r θ) a),
        (secondDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv F (secondProjectivePatch r θ) b)) =
        degreeOneCoboundary r θ (x, y) := by
      simp only [a, b, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    exact hcoords.symm.trans (fromBiprod_degreeOne r θ hr a b).symm
  change S.δ F 0 1 rfl
    ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
      (overlapDegreeOneSectionsEquiv r θ (degreeOneCoboundary r θ (x, y)))) = 0
  rw [hz]
  have h := congrArg
    (fun f : (F.H' 0 (firstProjectivePatch r θ) ⊞ F.H' 0 (secondProjectivePatch r θ)) ⟶
      ProjectiveSheafH1 r θ => f z) (S.fromBiprod_δ F 0 1 rfl)
  exact h

/-- The exact kernel is the actual image of the two homogeneous chart
restrictions. No extra boundary or vanishing assumption is introduced. -/
theorem degreeOneConnecting_ker (r θ : ℂ) (hr : r ≠ 0) :
    (degreeOneConnecting r θ hr).ker = degreeOneBoundaries r θ := by
  ext z
  constructor
  · intro hz
    let F := degreeOneSheaf r θ
    let S := projectiveMayerVietoris r θ hr
    have hz' : S.δ F 0 1 rfl
        ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z)) = 0 := hz
    obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).mp
      ((S.sequence_exact F 0 1 rfl).exact 1)
        ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z)) hz'
    have hw' : S.fromBiprod F 0 w =
        (sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z) := hw
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective w
    refine ⟨((firstDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv F (firstProjectivePatch r θ) a),
      (secondDegreeOneSectionsEquiv r θ).symm
        (sectionsEquiv F (secondProjectivePatch r θ) b)), ?_⟩
    have hh := congrArg
      (fun v : F.H' 0 (overlapProjectivePatch r θ) =>
        (overlapDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv F (overlapProjectivePatch r θ) v)) hw'
    rw [Iso.addCommGroupIsoToAddEquiv_symm_apply,
      AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] at hh
    exact (fromBiprod_degreeOne r θ hr a b).symm.trans hh
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact degreeOneConnecting_coboundary r θ hr x y

/-- A proved injection from the concrete homogeneous Cech quotient into
actual derived cohomology of the constructed projective additive sheaf. -/
def degreeOneToProjectiveH1 (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ →+ ProjectiveSheafH1 r θ :=
  QuotientAddGroup.lift (degreeOneBoundaries r θ) (degreeOneConnecting r θ hr)
    (degreeOneConnecting_ker r θ hr).symm.le

theorem degreeOneToProjectiveH1_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (degreeOneToProjectiveH1 r θ hr) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (degreeOneConnecting_ker r θ hr).symm


end CycleQ2GeometricProjectiveCurve
end
