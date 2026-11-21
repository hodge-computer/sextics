import Proposal.GeometricProjectiveCharts

/-!
# Homogeneous frames on the actual projective curve

The degree-one localized modules have explicit frames and an invertible
transition section. Their maps agree with the actual structure-sheaf
restrictions on the projective affine charts.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped DirectSum
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta

def degreeOneFrame (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) : degreeOneModule r θ f d hf :=
  ⟨algebraMap (CurveRing r θ) (Localization.Away f) x,
    ⟨0, x, by simpa only [Nat.zero_mul, Nat.add_zero] using hx,
      by
        change Localization.mk x (⟨f ^ 0, 0, rfl⟩ : Submonoid.powers f) = _
        have hd : (⟨f ^ 0, 0, rfl⟩ : Submonoid.powers f) = 1 :=
          Subtype.ext (pow_zero f)
        exact (congrArg (Localization.mk x) hd).trans
          (Localization.mk_one_eq_algebraMap x)⟩⟩

@[simp] theorem degreeOneFrame_coe (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) :
    (degreeOneFrame r θ f d hf x hx : Localization.Away f) =
      algebraMap (CurveRing r θ) (Localization.Away f) x := rfl

def degreeOneFrameMap (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) :
    HomogeneousLocalization.Away (curveGrade r θ) f →ₗ[
        HomogeneousLocalization.Away (curveGrade r θ) f] degreeOneModule r θ f d hf :=
  LinearMap.toSpanSingleton _ _ (degreeOneFrame r θ f d hf x hx)

@[simp] theorem degreeOneFrameMap_coe (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1)
    (a : HomogeneousLocalization.Away (curveGrade r θ) f) :
    (degreeOneFrameMap r θ f d hf x hx a : Localization.Away f) =
      a.val * algebraMap (CurveRing r θ) (Localization.Away f) x := rfl

theorem frameCoordinate_isUnit (r θ : ℂ) (f x g : CurveRing r θ)
    (hfg : f = x * g) :
    IsUnit (algebraMap (CurveRing r θ) (Localization.Away f) x) :=
  isUnit_of_dvd_unit (map_dvd _ ⟨g, hfg⟩)
    (IsLocalization.Away.algebraMap_isUnit f)

/-- If a degree-one coordinate divides the inverted homogeneous function,
multiplication by that coordinate trivializes the degree-one local module. -/
def degreeOneFrameEquiv (r θ : ℂ) (f : CurveRing r θ) (e : ℕ)
    (hf : f ∈ curveGrade r θ (1 + e)) (x g : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) (hg : g ∈ curveGrade r θ e)
    (hfg : f = x * g) :
    HomogeneousLocalization.Away (curveGrade r θ) f ≃ₗ[
        HomogeneousLocalization.Away (curveGrade r θ) f]
      degreeOneModule r θ f (1 + e) hf :=
  LinearEquiv.ofBijective (degreeOneFrameMap r θ f (1 + e) hf x hx) (by
    constructor
    · intro a b hab
      apply HomogeneousLocalization.val_injective
      apply (frameCoordinate_isUnit r θ f x g hfg).mul_right_cancel
      exact congrArg (fun z : degreeOneModule r θ f (1 + e) hf =>
        (z : Localization.Away f)) hab
    · intro z
      obtain ⟨n, a, ha, haz⟩ := z.property
      have hag : a * g ∈ curveGrade r θ ((n + 1) • (1 + e)) := by
        have hd : 1 + n * (1 + e) + e = (n + 1) • (1 + e) := by
          simp only [nsmul_eq_mul, Nat.cast_id]
          ring
        rw [← hd]
        exact SetLike.mul_mem_graded ha hg
      refine ⟨HomogeneousLocalization.Away.mk (curveGrade r θ) hf (n + 1) (a * g) hag, ?_⟩
      apply Subtype.ext
      rw [degreeOneFrameMap_coe, HomogeneousLocalization.Away.val_mk, ← haz,
        ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, awayFraction,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Subtype.coe_mk, one_mul, mul_one]
      rw [pow_succ, hfg]
      ring)

@[simp] theorem degreeOneFrameEquiv_coe (r θ : ℂ) (f : CurveRing r θ) (e : ℕ)
    (hf : f ∈ curveGrade r θ (1 + e)) (x g : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) (hg : g ∈ curveGrade r θ e)
    (hfg : f = x * g) (a : HomogeneousLocalization.Away (curveGrade r θ) f) :
    (degreeOneFrameEquiv r θ f e hf x g hx hg hfg a : Localization.Away f) =
      a.val * algebraMap (CurveRing r θ) (Localization.Away f) x := rfl

def firstFrameComplement (r θ : ℂ) : CurveRing r θ :=
  curveMap r θ (C (3 * r ^ 2) * X 1 * X 3 ^ 2)

def secondFrameComplement (r θ : ℂ) : CurveRing r θ :=
  curveMap r θ (C 3 * X 2 ^ 3)

theorem firstFrameComplement_grade (r θ : ℂ) :
    firstFrameComplement r θ ∈ curveGrade r θ 3 := by
  apply curveMap_mem_grade
  simpa only [mul_assoc] using
    (((isHomogeneous_X ℂ (1 : Fin 4)).mul
      ((isHomogeneous_X ℂ (3 : Fin 4)).pow 2)).C_mul (3 * r ^ 2))

theorem secondFrameComplement_grade (r θ : ℂ) :
    secondFrameComplement r θ ∈ curveGrade r θ 3 :=
  curveMap_mem_grade r θ (((isHomogeneous_X ℂ (2 : Fin 4)).pow 3).C_mul 3)

theorem firstFrame_factorization (r θ : ℂ) :
    curveG1 r θ = curveMap r θ (X 1) * firstFrameComplement r θ := by
  change ambientCurveMap r θ (originalG1 r) = _
  rw [ambientCurveMap_g1]
  change curveMap r θ (C (3 * r ^ 2) * CycleQ2SeedCech.curveA ^ 2) =
    curveMap r θ (X 1) * curveMap r θ (C (3 * r ^ 2) * X 1 * X 3 ^ 2)
  rw [← map_mul]
  apply congrArg (curveMap r θ)
  dsimp [CycleQ2SeedCech.curveA]
  ring

theorem secondFrame_factorization (r θ : ℂ) :
    curveG2 r θ = curveMap r θ (X 2) * secondFrameComplement r θ := by
  change ambientCurveMap r θ originalG2 = _
  rw [ambientCurveMap_g2]
  change curveMap r θ (C 3 * X 2 ^ 4) =
    curveMap r θ (X 2) * curveMap r θ (C 3 * X 2 ^ 3)
  rw [← map_mul]
  apply congrArg (curveMap r θ)
  ring

def firstDegreeOneEquiv (r θ : ℂ) :
    FirstProjectiveRing r θ ≃ₗ[FirstProjectiveRing r θ] FirstDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ) 3 (curveG1_mem_grade r θ)
    (curveMap r θ (X 1)) (firstFrameComplement r θ)
    (coordinate_mem_grade r θ 1) (firstFrameComplement_grade r θ)
    (firstFrame_factorization r θ)

def secondDegreeOneEquiv (r θ : ℂ) :
    SecondProjectiveRing r θ ≃ₗ[SecondProjectiveRing r θ] SecondDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG2 r θ) 3 (curveG2_mem_grade r θ)
    (curveMap r θ (X 2)) (secondFrameComplement r θ)
    (coordinate_mem_grade r θ 2) (secondFrameComplement_grade r θ)
    (secondFrame_factorization r θ)

theorem overlapFirstFrame_factorization (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ = curveMap r θ (X 1) *
      (firstFrameComplement r θ * curveG2 r θ) := by
  rw [firstFrame_factorization, mul_assoc]

theorem overlapSecondFrame_factorization (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ = curveMap r θ (X 2) *
      (curveG1 r θ * secondFrameComplement r θ) := by
  rw [secondFrame_factorization]
  ring

def overlapFirstDegreeOneEquiv (r θ : ℂ) :
    OverlapProjectiveRing r θ ≃ₗ[OverlapProjectiveRing r θ] OverlapDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ * curveG2 r θ) 7 (curveG12_mem_grade r θ)
    (curveMap r θ (X 1)) (firstFrameComplement r θ * curveG2 r θ)
    (coordinate_mem_grade r θ 1)
    (SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (curveG2_mem_grade r θ))
    (overlapFirstFrame_factorization r θ)

def overlapSecondDegreeOneEquiv (r θ : ℂ) :
    OverlapProjectiveRing r θ ≃ₗ[OverlapProjectiveRing r θ] OverlapDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ * curveG2 r θ) 7 (curveG12_mem_grade r θ)
    (curveMap r θ (X 2)) (curveG1 r θ * secondFrameComplement r θ)
    (coordinate_mem_grade r θ 2)
    (SetLike.mul_mem_graded (curveG1_mem_grade r θ) (secondFrameComplement_grade r θ))
    (overlapSecondFrame_factorization r θ)

/-- In the first frame, the second frame is the genuine ratio `x2/x1`. -/
def overlapTransition (r θ : ℂ) : OverlapProjectiveRing r θ :=
  (overlapFirstDegreeOneEquiv r θ).symm (overlapSecondDegreeOneEquiv r θ 1)

def overlapReverseTransition (r θ : ℂ) : OverlapProjectiveRing r θ :=
  (overlapSecondDegreeOneEquiv r θ).symm (overlapFirstDegreeOneEquiv r θ 1)

theorem overlapTransition_coordinate (r θ : ℂ) :
    (overlapTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2)) := by
  have hh := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    ((overlapFirstDegreeOneEquiv r θ).apply_symm_apply
      (overlapSecondDegreeOneEquiv r θ 1))
  change (overlapTransition r θ).val * _ = (1 : OverlapProjectiveRing r θ).val * _ at hh
  simpa only [HomogeneousLocalization.val_one, one_mul, degreeOneFrame_coe] using hh

theorem overlapReverseTransition_coordinate (r θ : ℂ) :
    (overlapReverseTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2)) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) := by
  have hh := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    ((overlapSecondDegreeOneEquiv r θ).apply_symm_apply
      (overlapFirstDegreeOneEquiv r θ 1))
  change (overlapReverseTransition r θ).val * _ = (1 : OverlapProjectiveRing r θ).val * _ at hh
  simpa only [HomogeneousLocalization.val_one, one_mul, degreeOneFrame_coe] using hh

theorem overlapTransition_mul_reverse (r θ : ℂ) :
    overlapTransition r θ * overlapReverseTransition r θ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  apply (frameCoordinate_isUnit r θ _ _ _ (overlapSecondFrame_factorization r θ)).mul_right_cancel
  rw [mul_assoc, overlapReverseTransition_coordinate, overlapTransition_coordinate, one_mul]

def overlapTransitionUnit (r θ : ℂ) : (OverlapProjectiveRing r θ)ˣ where
  val := overlapTransition r θ
  inv := overlapReverseTransition r θ
  val_inv := overlapTransition_mul_reverse r θ
  inv_val := (mul_comm _ _).trans (overlapTransition_mul_reverse r θ)

/-- The transition is an invertible section of the actual projective
structure sheaf on the overlap of the two actual affine opens. -/
def projectiveTransitionUnit (r θ : ℂ) :
    Γ(projectiveCurve r θ, overlapProjectivePatch r θ)ˣ :=
  Units.map (overlapProjectiveSectionsIso r θ).hom.hom.toMonoidHom
    (overlapTransitionUnit r θ)

def firstProjectiveRestriction (r θ : ℂ) :
    FirstProjectiveRing r θ →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ) (curveG2_mem_grade r θ) rfl

def secondProjectiveRestriction (r θ : ℂ) :
    SecondProjectiveRing r θ →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ) (curveG1_mem_grade r θ) (mul_comm _ _)

theorem firstProjectiveRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : FirstProjectiveRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (Proj.basicOpen_mono (curveGrade r θ) (curveG1 r θ)
          (curveG1 r θ * curveG2 r θ) ⟨_, rfl⟩)).op
          ((firstProjectiveSectionsIso r θ).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (firstProjectiveRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ) (curveG2_mem_grade r θ) rfl).symm

theorem secondProjectiveRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : SecondProjectiveRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (Proj.basicOpen_mono (curveGrade r θ) (curveG2 r θ)
          (curveG1 r θ * curveG2 r θ) ⟨_, mul_comm _ _⟩)).op
          ((secondProjectiveSectionsIso r θ).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (secondProjectiveRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (curveG1_mem_grade r θ) (mul_comm _ _)).symm

theorem firstDegreeOneEquiv_restriction (r θ : ℂ) (a : FirstProjectiveRing r θ) :
    firstDegreeOneRestriction r θ (firstDegreeOneEquiv r θ a) =
      overlapFirstDegreeOneEquiv r θ (firstProjectiveRestriction r θ a) := by
  apply Subtype.ext
  rw [firstDegreeOneRestriction_coe]
  change awayRestriction r θ (curveG1 r θ) (curveG2 r θ) _ rfl
      (a.val * algebraMap _ (FirstOpen r θ) (curveMap r θ (X 1))) =
    (HomogeneousLocalization.awayMap (curveGrade r θ) (curveG2_mem_grade r θ) rfl a).val * _
  rw [map_mul, awayRestriction_base, awayRestriction_val]
  rw [degreeOneFrame_coe]

theorem secondDegreeOneEquiv_restriction (r θ : ℂ) (a : SecondProjectiveRing r θ) :
    secondDegreeOneRestriction r θ (secondDegreeOneEquiv r θ a) =
      overlapSecondDegreeOneEquiv r θ (secondProjectiveRestriction r θ a) := by
  apply Subtype.ext
  rw [secondDegreeOneRestriction_coe]
  change awayRestriction r θ (curveG2 r θ) (curveG1 r θ) _ (mul_comm _ _)
      (a.val * algebraMap _ (SecondOpen r θ) (curveMap r θ (X 2))) =
    (HomogeneousLocalization.awayMap (curveGrade r θ)
      (curveG1_mem_grade r θ) (mul_comm _ _) a).val * _
  rw [map_mul, awayRestriction_base, awayRestriction_val]
  rw [degreeOneFrame_coe]

theorem overlapTransition_frame (r θ : ℂ) (b : OverlapProjectiveRing r θ) :
    overlapFirstDegreeOneEquiv r θ (overlapTransition r θ * b) =
      overlapSecondDegreeOneEquiv r θ b := by
  apply Subtype.ext
  change (overlapTransition r θ * b).val *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
    b.val * algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2))
  rw [HomogeneousLocalization.val_mul]
  calc
    (overlapTransition r θ).val * b.val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
      b.val * ((overlapTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) := by ring
    _ = _ := by rw [overlapTransition_coordinate]

/-- In the actual projective affine frames, the homogeneous degree-one
coboundary is `a|₁₂ - (x2/x1)b|₁₂`, with the literal structure-sheaf
restrictions identified above. -/
theorem degreeOneCoboundary_in_frames (r θ : ℂ)
    (a : FirstProjectiveRing r θ) (b : SecondProjectiveRing r θ) :
    degreeOneCoboundary r θ (firstDegreeOneEquiv r θ a, secondDegreeOneEquiv r θ b) =
      overlapFirstDegreeOneEquiv r θ
        (firstProjectiveRestriction r θ a -
          overlapTransition r θ * secondProjectiveRestriction r θ b) := by
  change firstDegreeOneRestriction r θ (firstDegreeOneEquiv r θ a) -
    secondDegreeOneRestriction r θ (secondDegreeOneEquiv r θ b) = _
  rw [firstDegreeOneEquiv_restriction, secondDegreeOneEquiv_restriction,
    map_sub, overlapTransition_frame]


end CycleQ2GeometricProjectiveCurve
end
