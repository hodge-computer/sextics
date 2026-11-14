import Proposal.GeometricLiteralCanonicalClass
import Proposal.GeometricTwistedDifferential
import Proposal.GeometricCanonicalCechBoundary

/-!
# A genuine projective normal-frame class and cubic pairing

The inverse-square coordinate frames glue to an actual module sheaf on the
literal projective curve. Its overlap cocycle is specified by a homogeneous
fraction, and cubic multiplication is an actual module-sheaf morphism. The
Mayer--Vietoris image of the literal ambient cocycle pairs to the previously
verified nonzero canonical class. A second literal normal-frame class is
killed by the same seven actual cubic cohomology maps.

The frame interpretation below uses the actual relative conormal duals. This
does not identify the sheaf with the normal sheaf of a projective immersion,
nor identify a surface Cartier boundary in H².
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveNormalClass

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricConeCech.HZero CycleQ2GeometricCanonicalCechBoundary
  CycleQ2GeometricTwistedFrameMap CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricLiteralCanonicalClass CycleQ2GeometricLiteralDirection

private theorem fraction_mul_denominator (r θ : ℂ) (f : CurveRing r θ)
    (n : ℕ) (a : CurveRing r θ) :
    awayFraction r θ f n a * algebraMap (CurveRing r θ) (Localization.Away f) (f ^ n) =
      algebraMap (CurveRing r θ) (Localization.Away f) a := by
  rw [awayFraction, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec (Localization.Away f) a
    (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)

/-- The degree-one image of the normalized normal frame under multiplication
by a homogeneous cubic: its literal value is `σ/x²` when `f = x*g`. -/
def cubicLocalImage (r θ : ℂ) (f : CurveRing r θ)
    (hf : f ∈ curveGrade r θ 4) (g : CurveRing r θ)
    (hg : g ∈ curveGrade r θ 3) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    degreeOneModule r θ f 4 hf :=
  ⟨awayFraction r θ f 2 (curveMap r θ σ * g ^ 2),
    awayFraction_mem_degreeOne r θ f 4 hf 2 _ (by
      simpa only [nsmul_eq_mul, Nat.cast_id,
        show (3 + 2 * 3 : ℕ) = 1 + 2 * 4 by decide] using
        SetLike.mul_mem_graded (curveMap_mem_grade r θ hσ)
          (SetLike.pow_mem_graded 2 hg))⟩

theorem cubicLocalImage_mul_square (r θ : ℂ) (f : CurveRing r θ)
    (hf : f ∈ curveGrade r θ 4) (x g : CurveRing r θ)
    (hg : g ∈ curveGrade r θ 3) (hfg : f = x * g)
    (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (cubicLocalImage r θ f hf g hg σ hσ : Localization.Away f) *
        (algebraMap (CurveRing r θ) (Localization.Away f) x) ^ 2 =
      algebraMap (CurveRing r θ) (Localization.Away f) (curveMap r θ σ) := by
  change awayFraction r θ f 2 (curveMap r θ σ * g ^ 2) * _ = _
  rw [← map_pow, ← Localization.mk_one_eq_algebraMap, awayFraction,
    Localization.mk_mul, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Subtype.coe_mk, one_mul, mul_one]
  rw [hfg]
  ring

def firstCubicImage (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) : FirstDegreeOne r θ :=
  cubicLocalImage r θ (curveG1 r θ) (curveG1_mem_grade r θ)
    (firstFrameComplement r θ) (firstFrameComplement_grade r θ) σ hσ

def secondCubicImage (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) : SecondDegreeOne r θ :=
  cubicLocalImage r θ (curveG2 r θ) (curveG2_mem_grade r θ)
    (secondFrameComplement r θ) (secondFrameComplement_grade r θ) σ hσ

theorem firstCubicImage_overlap_square (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) : Overlap r θ) *
        (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) ^ 2 =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
  have h := congrArg (firstRestriction r θ)
    (cubicLocalImage_mul_square r θ (curveG1 r θ) (curveG1_mem_grade r θ)
      (curveMap r θ (X 1)) (firstFrameComplement r θ)
      (firstFrameComplement_grade r θ) (firstFrame_factorization r θ) σ hσ)
  simpa only [map_mul, map_pow, firstDegreeOneRestriction_coe, firstRestriction,
    IsLocalization.Away.awayToAwayRight_eq, firstCubicImage] using h

theorem secondCubicImage_overlap_square (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (secondDegreeOneRestriction r θ (secondCubicImage r θ σ hσ) : Overlap r θ) *
        (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2))) ^ 2 =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
  have h := congrArg (secondRestriction r θ)
    (cubicLocalImage_mul_square r θ (curveG2 r θ) (curveG2_mem_grade r θ)
      (curveMap r θ (X 2)) (secondFrameComplement r θ)
      (secondFrameComplement_grade r θ) (secondFrame_factorization r θ) σ hσ)
  simpa only [map_mul, map_pow, secondDegreeOneRestriction_coe, secondRestriction,
    IsLocalization.Away.awayToAwayLeft_eq, secondCubicImage] using h

private theorem inverse_square_transition {R : Type*} [CommRing R]
    (x y a b p v : R) (hx : IsUnit x) (hy : IsUnit y)
    (hv : v * y = x) (ha : a * x ^ 2 = p) (hb : b * y ^ 2 = p) :
    b = v ^ 2 * a := by
  apply (hx.pow 2).mul_right_cancel
  apply (hy.pow 2).mul_right_cancel
  calc
    b * x ^ 2 * y ^ 2 = (b * y ^ 2) * x ^ 2 := by ring
    _ = p * x ^ 2 := by rw [hb]
    _ = p * (v * y) ^ 2 := by rw [hv]
    _ = v ^ 2 * (a * x ^ 2) * y ^ 2 := by rw [ha]; ring
    _ = v ^ 2 * a * x ^ 2 * y ^ 2 := by ring

theorem cubicImage_transition (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    secondDegreeOneRestriction r θ (secondCubicImage r θ σ hσ) =
      (overlapReverseTransition r θ ^ 2) •
        firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) := by
  apply Subtype.ext
  change _ = (overlapReverseTransition r θ ^ 2).val * _
  rw [HomogeneousLocalization.val_pow]
  exact inverse_square_transition _ _ _ _ _ _
    (frameCoordinate_isUnit r θ _ _ _ (overlapFirstFrame_factorization r θ))
    (frameCoordinate_isUnit r θ _ _ _ (overlapSecondFrame_factorization r θ))
    (overlapReverseTransition_coordinate r θ)
    (firstCubicImage_overlap_square r θ σ hσ)
    (secondCubicImage_overlap_square r θ σ hσ)

/-- The actual inverse-square transition of the normal coordinate frames. -/
def normalTransitionUnit (r θ : ℂ) :
    Γ(projectiveCurve r θ, overlapProjectivePatch r θ)ˣ :=
  (projectiveTransitionUnit r θ)⁻¹ ^ 2

theorem normalTransitionUnit_value (r θ : ℂ) :
    (normalTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) =
      (overlapProjectiveSectionsIso r θ).hom (overlapReverseTransition r θ ^ 2) := by
  change ((overlapProjectiveSectionsIso r θ).hom (overlapReverseTransition r θ)) ^ 2 = _
  exact ((overlapProjectiveSectionsIso r θ).hom.hom.map_pow _ 2).symm

def normalModuleSheaf (r θ : ℂ) :
    SheafOfModules.{0} (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf) :=
  TwistedModule.moduleSheaf (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (normalTransitionUnit r θ)

def normalAdditiveSheaf (r θ : ℂ) :
    Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf)).obj
    (normalModuleSheaf r θ)

def normalOverlapFrame (r θ : ℂ) :
    (normalAdditiveSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, overlapProjectivePatch r θ) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (normalTransitionUnit r θ)
    (overlapProjectivePatch r θ) ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)

theorem overlapDegreeOneSections_smul (r θ : ℂ) (a : OverlapProjectiveRing r θ)
    (z : OverlapDegreeOne r θ) :
    overlapDegreeOneSectionsEquiv r θ (a • z) =
      (overlapProjectiveSectionsIso r θ).hom a • overlapDegreeOneSectionsEquiv r θ z := by
  apply (overlapSheafFrame r θ).injective
  have hs := TwistedModule.firstLocalSections_smul (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)
    ((overlapProjectiveSectionsIso r θ).hom a) (overlapDegreeOneSectionsEquiv r θ z)
  change overlapSheafFrame r θ
      ((overlapProjectiveSectionsIso r θ).hom a • overlapDegreeOneSectionsEquiv r θ z) =
    (overlapProjectiveSectionsIso r θ).hom a *
      overlapSheafFrame r θ (overlapDegreeOneSectionsEquiv r θ z) at hs
  rw [overlapDegreeOneSectionsEquiv_coordinate] at hs
  rw [overlapDegreeOneSectionsEquiv_coordinate]
  exact ((congrArg (fun b : OverlapProjectiveRing r θ => (overlapProjectiveSectionsIso r θ).hom b)
    ((overlapFirstDegreeOneEquiv r θ).symm.map_smul a z)).trans
      ((overlapProjectiveSectionsIso r θ).hom.hom.map_mul _ _)).trans hs.symm

def firstCubicSection (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ)) :=
  firstDegreeOneSectionsEquiv r θ (firstCubicImage r θ σ hσ)

def secondCubicSection (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ)) :=
  secondDegreeOneSectionsEquiv r θ (secondCubicImage r θ σ hσ)

theorem cubicSection_transition (r θ : ℂ) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op
        (secondCubicSection r θ σ hσ) =
      (normalTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) •
        (degreeOneSheaf r θ).obj.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
          (firstCubicSection r θ σ hσ) := by
  have hfirst := firstDegreeOneSectionsEquiv_restriction r θ (firstCubicImage r θ σ hσ)
  have hsecond := secondDegreeOneSectionsEquiv_restriction r θ (secondCubicImage r θ σ hσ)
  exact hsecond.trans ((congrArg (overlapDegreeOneSectionsEquiv r θ)
    (cubicImage_transition r θ σ hσ)).trans
      ((overlapDegreeOneSections_smul r θ (overlapReverseTransition r θ ^ 2)
        (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ))).trans
        ((congrArg
          (fun c : Γ(projectiveCurve r θ, overlapProjectivePatch r θ) =>
            c • overlapDegreeOneSectionsEquiv r θ
              (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ)))
          (normalTransitionUnit_value r θ).symm).trans
          (congrArg
            (fun z : (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) =>
              (normalTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) • z)
            hfirst.symm))))

/-- Multiplication by the cubic, constructed by actual sheaf gluing. -/
def cubicMorphism (r θ : ℂ) (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    normalModuleSheaf r θ ⟶ degreeOneModuleSheaf r θ :=
  frameMorphism (projectiveCurve r θ).sheaf (degreeOneModuleSheaf r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (normalTransitionUnit r θ)
    (projective_twoOpen_cover r θ hr)
    (firstCubicSection r θ σ hσ) (secondCubicSection r θ σ hσ)
    (cubicSection_transition r θ σ hσ)

def cubicAdditiveMorphism (r θ : ℂ) (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    normalAdditiveSheaf r θ ⟶ degreeOneSheaf r θ :=
  (SheafOfModules.toSheaf (TwistedModule.ringSheaf (projectiveCurve r θ).sheaf)).map
    (cubicMorphism r θ hr σ hσ)

theorem cubicMorphism_overlap (r θ : ℂ) (hr : r ≠ 0) (σ : Poly)
    (hσ : σ.IsHomogeneous 3)
    (s : (normalAdditiveSheaf r θ).obj.obj (op (overlapProjectivePatch r θ))) :
    (cubicAdditiveMorphism r θ hr σ hσ).hom.app (op (overlapProjectivePatch r θ)) s =
      normalOverlapFrame r θ s •
        overlapDegreeOneSectionsEquiv r θ
          (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ)) := by
  have h := frameMorphism_first_local (projectiveCurve r θ).sheaf
    (degreeOneModuleSheaf r θ) (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (normalTransitionUnit r θ) (projective_twoOpen_cover r θ hr)
    (firstCubicSection r θ σ hσ) (secondCubicSection r θ σ hσ)
    (cubicSection_transition r θ σ hσ) (overlapProjectivePatch r θ)
    ((overlapProjectivePatch_eq r θ).le.trans inf_le_left) s
  change _ = normalOverlapFrame r θ s •
    (degreeOneSheaf r θ).obj.map
      (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
      (firstCubicSection r θ σ hσ) at h
  exact h.trans (congrArg
    (fun z : (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) =>
      normalOverlapFrame r θ s • z)
    (firstDegreeOneSectionsEquiv_restriction r θ (firstCubicImage r θ σ hσ)))


/-- The first coordinate of a degree-minus-two overlap normal section.
The numerator has degree eight and the denominator has degree eight. -/
def normalOverlapCoordinate (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 6) :
    OverlapProjectiveRing r θ :=
  HomogeneousLocalization.Away.mk (curveGrade r θ) (curveG12_mem_grade r θ) 1
    (curveMap r θ (p * X 1 ^ 2)) (by
      simpa only [one_smul] using curveMap_mem_grade r θ
        (hp.mul ((isHomogeneous_X ℂ (1 : Fin 4)).pow 2)))

theorem normalOverlapCoordinate_mul_denominator (r θ : ℂ)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    (normalOverlapCoordinate r θ p hp).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (p * X 1 ^ 2)) := by
  simpa only [normalOverlapCoordinate, HomogeneousLocalization.Away.val_mk, awayFraction, pow_one] using
    fraction_mul_denominator r θ (curveG1 r θ * curveG2 r θ) 1
      (curveMap r θ (p * X 1 ^ 2))

/-- An actual section of the actual twisted sheaf on the projective overlap. -/
def normalOverlapSection (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 6) :
    (normalAdditiveSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) :=
  (normalOverlapFrame r θ).symm
    ((overlapProjectiveSectionsIso r θ).hom (normalOverlapCoordinate r θ p hp))

theorem cubicMorphism_normalOverlapSection (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    (cubicAdditiveMorphism r θ hr σ hσ).hom.app (op (overlapProjectivePatch r θ))
        (normalOverlapSection r θ p hp) =
      overlapDegreeOneSectionsEquiv r θ
        (degreeNineRepresentative r θ (p * σ) (hp.mul hσ)) := by
  rw [cubicMorphism_overlap, normalOverlapSection, AddEquiv.apply_symm_apply,
    ← overlapDegreeOneSections_smul]
  apply congrArg (overlapDegreeOneSectionsEquiv r θ)
  apply Subtype.ext
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Overlap r θ) (curveG1 r θ * curveG2 r θ)).mul_right_cancel
  change ((normalOverlapCoordinate r θ p hp).val *
    (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) : Overlap r θ)) * _ = _
  have hrep : (degreeNineRepresentative r θ (p * σ) (hp.mul hσ) : Overlap r θ) *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ) =
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (p * σ)) := by
    simpa only [degreeNineRepresentative, pow_one] using
      fraction_mul_denominator r θ (curveG1 r θ * curveG2 r θ) 1
        (curveMap r θ (p * σ))
  calc
    _ = ((normalOverlapCoordinate r θ p hp).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ)) *
          (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) : Overlap r θ) := by ring
    _ = algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (p * X 1 ^ 2)) *
          (firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) : Overlap r θ) := by
      rw [normalOverlapCoordinate_mul_denominator]
    _ = algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) *
        ((firstDegreeOneRestriction r θ (firstCubicImage r θ σ hσ) : Overlap r θ) *
          (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) ^ 2) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      ring
    _ = algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
      rw [firstCubicImage_overlap_square]
    _ = algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (p * σ)) := by
      rw [map_mul, map_mul]
    _ = _ := hrep.symm

local instance projectiveNormalHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Genuine derived cohomology of the constructed normal-frame sheaf. -/
abbrev NormalSheafH1 (r θ : ℂ) := (normalAdditiveSheaf r θ).H' 1 ⊤

def normalClass (r θ : ℂ) (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6) :
    NormalSheafH1 r θ :=
  (projectiveMayerVietoris r θ hr).δ (normalAdditiveSheaf r θ) 0 1 rfl
    ((sectionsEquiv (normalAdditiveSheaf r θ) (overlapProjectivePatch r θ)).symm
      (normalOverlapSection r θ p hp))

/-- The actual cohomology map induced by cubic multiplication. -/
def cubicH1Map (r θ : ℂ) (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    NormalSheafH1 r θ →+ ProjectiveSheafH1 r θ :=
  (((Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology (projectiveCurve r θ)) 1).map
      (cubicAdditiveMorphism r θ hr σ hσ)).app (op ⊤)).hom

/-- The actual derived connecting class retains the literal product numerator. -/
theorem cubicH1Map_normalClass (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    cubicH1Map r θ hr σ hσ (normalClass r θ hr p hp) =
      degreeOneConnecting r θ hr (degreeNineRepresentative r θ (p * σ) (hp.mul hσ)) := by
  have hnat := mayerVietoris_delta_naturality (cubicAdditiveMorphism r θ hr σ hσ)
    (projectiveMayerVietoris r θ hr) 0 1 rfl
    ((sectionsEquiv (normalAdditiveSheaf r θ) (overlapProjectivePatch r θ)).symm
      (normalOverlapSection r θ p hp))
  have hzero := sectionsEquiv_symm_map (cubicAdditiveMorphism r θ hr σ hσ)
    (overlapProjectivePatch r θ) (normalOverlapSection r θ p hp)
  rw [cubicMorphism_normalOverlapSection] at hzero
  exact hnat.trans (congrArg
    (fun x : (degreeOneSheaf r θ).H' 0 (overlapProjectivePatch r θ) =>
      (projectiveMayerVietoris r θ hr).δ (degreeOneSheaf r θ) 0 1 rfl x) hzero)

def ambientNormalNumerator : Poly := X 2 ^ 3 * X 3 ^ 3

theorem ambientNormalNumerator_homogeneous : ambientNormalNumerator.IsHomogeneous 6 :=
  ((isHomogeneous_X ℂ (2 : Fin 4)).pow 3).mul ((isHomogeneous_X ℂ (3 : Fin 4)).pow 3)

def literalNormalClass : NormalSheafH1 57 1 :=
  normalClass 57 1 (by norm_num) ambientNormalNumerator ambientNormalNumerator_homogeneous

/-- Cubic multiplication followed by the proved literal canonical-sheaf
isomorphism, both acting on actual derived cohomology. -/
def selectedCubicPairing : NormalSheafH1 57 1 →+ DifferentialSheafH1 57 1 :=
  literalCanonicalH1Equiv.toAddMonoidHom.comp
    (cubicH1Map 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous)

theorem selectedCubicPairing_literalNormalClass :
    selectedCubicPairing literalNormalClass = selectedAmbientClass := by
  change literalCanonicalH1Equiv
    (cubicH1Map 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous
      (normalClass 57 1 (by norm_num) ambientNormalNumerator ambientNormalNumerator_homogeneous)) = _
  rw [cubicH1Map_normalClass]
  change literalCanonicalH1Equiv (degreeOneConnecting 57 1 (by norm_num)
      (degreeNineRepresentative 57 1 (ambientNormalNumerator * selectedCubic) _)) =
    literalCanonicalH1Equiv (degreeOneConnecting 57 1 (by norm_num)
      (degreeNineRepresentative 57 1 ambientNumerator _))
  congr 3
  exact ambientNumerator_eq.symm

/-- The genuine projective H¹ class is nonzero because its actual cubic
image is the already verified nonzero differential-sheaf class. -/
theorem literalNormalClass_ne_zero : literalNormalClass ≠ 0 := by
  intro hz
  apply selectedAmbientClass_ne_zero
  rw [← selectedCubicPairing_literalNormalClass, hz, map_zero]

#print axioms cubicMorphism
#print axioms cubicH1Map_normalClass
#print axioms selectedCubicPairing_literalNormalClass
#print axioms literalNormalClass_ne_zero


/-! ## Intrinsic relative-normal frames -/

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2GenuineNormalConnecting
  CycleQ2NormalRestriction CycleQ2ActualNormalCech CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricRelativeNormalConnecting

def coordinateUnit (r θ : ℂ) (f x g : CurveRing r θ) (hfg : f = x * g) :
    (Localization.Away f)ˣ :=
  (frameCoordinate_isUnit r θ f x g hfg).unit

theorem coordinateUnit_value (r θ : ℂ) (f x g : CurveRing r θ) (hfg : f = x * g) :
    (coordinateUnit r θ f x g hfg : Localization.Away f) =
      algebraMap (CurveRing r θ) (Localization.Away f) x := IsUnit.unit_spec _

def firstCoordinateUnit (r θ : ℂ) : (FirstOpen r θ)ˣ :=
  coordinateUnit r θ (curveG1 r θ) (curveMap r θ (X 1))
    (firstFrameComplement r θ) (firstFrame_factorization r θ)

def secondCoordinateUnit (r θ : ℂ) : (SecondOpen r θ)ˣ :=
  coordinateUnit r θ (curveG2 r θ) (curveMap r θ (X 2))
    (secondFrameComplement r θ) (secondFrame_factorization r θ)

def overlapFirstCoordinateUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  coordinateUnit r θ (curveG1 r θ * curveG2 r θ) (curveMap r θ (X 1))
    (firstFrameComplement r θ * curveG2 r θ) (overlapFirstFrame_factorization r θ)

def overlapSecondCoordinateUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  coordinateUnit r θ (curveG1 r θ * curveG2 r θ) (curveMap r θ (X 2))
    (curveG1 r θ * secondFrameComplement r θ) (overlapSecondFrame_factorization r θ)

/-- Full scalar trivializations of the actual relative conormal duals.
The coordinate normalization is by the explicit inverse square. -/
def firstRelativeFrameEquiv (r θ : ℂ) :
    FirstOpen r θ ≃ₗ[FirstOpen r θ] RelativeNormal r θ (FirstOpen r θ) :=
  (((firstCoordinateUnit r θ)⁻¹ ^ 2).mulRightLinearEquiv (FirstOpen r θ)).trans
    ((firstKernelEquiv r θ (firstBasis r θ) (firstBasis_apply r θ)
      (firstOpenUnit r θ) (firstUnit_value r θ)).trans (firstNormalModuleEquiv r θ).symm)

def secondRelativeFrameEquiv (r θ : ℂ) :
    SecondOpen r θ ≃ₗ[SecondOpen r θ] RelativeNormal r θ (SecondOpen r θ) :=
  (((secondCoordinateUnit r θ)⁻¹ ^ 2).mulRightLinearEquiv (SecondOpen r θ)).trans
    ((secondKernelEquiv r θ (secondBasis r θ) (secondBasis_apply r θ)
      (secondOpenUnit r θ) (secondUnit_value r θ)).trans (secondNormalModuleEquiv r θ).symm)

def overlapFirstRelativeFrameEquiv (r θ : ℂ) :
    Overlap r θ ≃ₗ[Overlap r θ] RelativeNormal r θ (Overlap r θ) :=
  (((overlapFirstCoordinateUnit r θ)⁻¹ ^ 2).mulRightLinearEquiv (Overlap r θ)).trans
    ((firstKernelEquiv r θ (overlapBasis r θ) (overlapBasis_apply r θ)
      (firstOverlapUnit r θ) (firstOverlapUnit_value r θ)).trans (overlapNormalModuleEquiv r θ).symm)

def overlapSecondRelativeFrameEquiv (r θ : ℂ) :
    Overlap r θ ≃ₗ[Overlap r θ] RelativeNormal r θ (Overlap r θ) :=
  (((overlapSecondCoordinateUnit r θ)⁻¹ ^ 2).mulRightLinearEquiv (Overlap r θ)).trans
    ((firstKernelEquiv r θ (overlapBasis r θ) (overlapBasis_apply r θ)
      (firstOverlapUnit r θ) (firstOverlapUnit_value r θ)).trans (overlapNormalModuleEquiv r θ).symm)

theorem firstRelativeFrameEquiv_comparison (r θ : ℂ) (a : FirstOpen r θ) :
    firstNormalModuleEquiv r θ (firstRelativeFrameEquiv r θ a) =
      firstKernelEquivalence r θ (a * (↑((firstCoordinateUnit r θ)⁻¹) : FirstOpen r θ) ^ 2) :=
  (firstNormalModuleEquiv r θ).apply_symm_apply _

theorem secondRelativeFrameEquiv_comparison (r θ : ℂ) (a : SecondOpen r θ) :
    secondNormalModuleEquiv r θ (secondRelativeFrameEquiv r θ a) =
      secondKernelEquivalence r θ (a * (↑((secondCoordinateUnit r θ)⁻¹) : SecondOpen r θ) ^ 2) :=
  (secondNormalModuleEquiv r θ).apply_symm_apply _

theorem overlapFirstRelativeFrameEquiv_comparison (r θ : ℂ) (a : Overlap r θ) :
    overlapNormalModuleEquiv r θ (overlapFirstRelativeFrameEquiv r θ a) =
      overlapKernelEquivalence r θ (a * (↑((overlapFirstCoordinateUnit r θ)⁻¹) : Overlap r θ) ^ 2) :=
  (overlapNormalModuleEquiv r θ).apply_symm_apply _

theorem overlapSecondRelativeFrameEquiv_comparison (r θ : ℂ) (a : Overlap r θ) :
    overlapNormalModuleEquiv r θ (overlapSecondRelativeFrameEquiv r θ a) =
      overlapKernelEquivalence r θ (a * (↑((overlapSecondCoordinateUnit r θ)⁻¹) : Overlap r θ) ^ 2) :=
  (overlapNormalModuleEquiv r θ).apply_symm_apply _

theorem firstRelativeFrameEquiv_equation (r θ : ℂ) (a : FirstOpen r θ) (i : Fin 3) :
    firstRelativeFrameEquiv r θ a (relativeEquationClass r θ (FirstOpen r θ) i) =
      (a * (↑((firstCoordinateUnit r θ)⁻¹) : FirstOpen r θ) ^ 2) *
        kernelVector (algebraMap P (FirstOpen r θ) (originalG1 r))
          (algebraMap P (FirstOpen r θ) originalG2) i := by
  change (normalModuleEquiv r θ (FirstOpen r θ)).symm
    (kernelParam r θ (firstBasis r θ) (firstBasis_apply r θ) _) _ = _
  rw [normalModuleEquiv_symm_equation]
  change (_ • genuineKernelGenerator r θ (firstBasis r θ)) (curveClass r θ i) = _
  rw [LinearMap.smul_apply, genuineKernelGenerator,
    fromCoordinates_class r θ (firstBasis r θ) (firstBasis_apply r θ)]
  rfl

theorem secondRelativeFrameEquiv_equation (r θ : ℂ) (a : SecondOpen r θ) (i : Fin 3) :
    secondRelativeFrameEquiv r θ a (relativeEquationClass r θ (SecondOpen r θ) i) =
      (a * (↑((secondCoordinateUnit r θ)⁻¹) : SecondOpen r θ) ^ 2) *
        kernelVector (algebraMap P (SecondOpen r θ) (originalG1 r))
          (algebraMap P (SecondOpen r θ) originalG2) i := by
  change (normalModuleEquiv r θ (SecondOpen r θ)).symm
    (kernelParam r θ (secondBasis r θ) (secondBasis_apply r θ) _) _ = _
  rw [normalModuleEquiv_symm_equation]
  change (_ • genuineKernelGenerator r θ (secondBasis r θ)) (curveClass r θ i) = _
  rw [LinearMap.smul_apply, genuineKernelGenerator,
    fromCoordinates_class r θ (secondBasis r θ) (secondBasis_apply r θ)]
  rfl

theorem overlapFirstRelativeFrameEquiv_equation (r θ : ℂ) (a : Overlap r θ) (i : Fin 3) :
    overlapFirstRelativeFrameEquiv r θ a (relativeEquationClass r θ (Overlap r θ) i) =
      (a * (↑((overlapFirstCoordinateUnit r θ)⁻¹) : Overlap r θ) ^ 2) *
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) i := by
  change (normalModuleEquiv r θ (Overlap r θ)).symm
    (kernelParam r θ (overlapBasis r θ) (overlapBasis_apply r θ) _) _ = _
  rw [normalModuleEquiv_symm_equation]
  change (_ • genuineKernelGenerator r θ (overlapBasis r θ)) (curveClass r θ i) = _
  rw [LinearMap.smul_apply, genuineKernelGenerator,
    fromCoordinates_class r θ (overlapBasis r θ) (overlapBasis_apply r θ)]
  rfl

/-- The normalized intrinsic normal frames have the very inverse-square
transition used to define the actual module sheaf. -/
theorem relativeNormalFrame_transition (r θ : ℂ) (a : Overlap r θ) :
    overlapSecondRelativeFrameEquiv r θ a =
      overlapFirstRelativeFrameEquiv r θ ((overlapReverseTransition r θ ^ 2).val * a) := by
  apply (overlapNormalModuleEquiv r θ).injective
  rw [overlapSecondRelativeFrameEquiv_comparison, overlapFirstRelativeFrameEquiv_comparison]
  apply congrArg (overlapKernelEquivalence r θ)
  have hi (u : (Overlap r θ)ˣ) : (↑u⁻¹ : Overlap r θ) ^ 2 * (u : Overlap r θ) ^ 2 = 1 := by
    rw [← mul_pow, u.inv_mul, one_pow]
  have hx := coordinateUnit_value r θ _ _ _ (overlapFirstFrame_factorization r θ)
  have hy := coordinateUnit_value r θ _ _ _ (overlapSecondFrame_factorization r θ)
  change (overlapFirstCoordinateUnit r θ : Overlap r θ) = _ at hx
  change (overlapSecondCoordinateUnit r θ : Overlap r θ) = _ at hy
  have hxy : (overlapReverseTransition r θ).val *
      (overlapSecondCoordinateUnit r θ : Overlap r θ) =
        (overlapFirstCoordinateUnit r θ : Overlap r θ) := by
    rw [hx, hy]
    exact overlapReverseTransition_coordinate r θ
  have h := inverse_square_transition _ _ _ _ 1 _
    (overlapFirstCoordinateUnit r θ).isUnit (overlapSecondCoordinateUnit r θ).isUnit
    hxy (hi (overlapFirstCoordinateUnit r θ)) (hi (overlapSecondCoordinateUnit r θ))
  rw [HomogeneousLocalization.val_pow, h]
  ring

def firstProjectiveNormalSection (r θ : ℂ) (a : FirstProjectiveRing r θ) :
    RelativeNormal r θ (FirstOpen r θ) := firstRelativeFrameEquiv r θ a.val

def secondProjectiveNormalSection (r θ : ℂ) (a : SecondProjectiveRing r θ) :
    RelativeNormal r θ (SecondOpen r θ) := secondRelativeFrameEquiv r θ a.val

theorem firstProjectiveNormalSection_injective (r θ : ℂ) :
    Function.Injective (firstProjectiveNormalSection r θ) := by
  intro a b h
  apply HomogeneousLocalization.val_injective
  exact (firstRelativeFrameEquiv r θ).injective h

theorem secondProjectiveNormalSection_injective (r θ : ℂ) :
    Function.Injective (secondProjectiveNormalSection r θ) := by
  intro a b h
  apply HomogeneousLocalization.val_injective
  exact (secondRelativeFrameEquiv r θ).injective h

/-- The actual overlap section interpreted as a genuine surface-relative
normal homomorphism, through its first normalized intrinsic frame. -/
def overlapRelativeNormal (r θ : ℂ)
    (s : (normalAdditiveSheaf r θ).obj.obj (op (overlapProjectivePatch r θ))) :
    RelativeNormal r θ (Overlap r θ) :=
  overlapFirstRelativeFrameEquiv r θ
    ((overlapProjectiveSectionsIso r θ).inv (normalOverlapFrame r θ s)).val

theorem normalOverlapCoordinate_coefficient (r θ : ℂ) (A L : WeightedPoly)
    (p : Poly) (hp : p.IsHomogeneous 6) (hnum : substitute (thetaK θ * L - A) = p) :
    (normalOverlapCoordinate r θ p hp).val =
      normalOverlapCoefficient r θ A L *
        (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) ^ 2 := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Overlap r θ) (curveG1 r θ * curveG2 r θ)).mul_right_cancel
  rw [normalOverlapCoordinate_mul_denominator]
  calc
    _ = algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) *
        (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) ^ 2 := by
      rw [map_mul, map_mul, map_pow, map_pow]
    _ = overlapAmbient r θ (thetaK θ * L - A) *
        (algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) ^ 2 := by
      change _ = algebraMap (CurveRing r θ) (Overlap r θ)
        (curveMap r θ (substitute (thetaK θ * L - A))) * _
      rw [hnum]
    _ = _ := by rw [← normalOverlapCoefficient_mul_denominator]; ring

/-- The homogeneous overlap cocycle is the actual previously constructed
normal lift difference, without a cochain-comparison hypothesis. -/
theorem normalOverlapSection_relative (r θ : ℂ) (A L : WeightedPoly)
    (p : Poly) (hp : p.IsHomogeneous 6) (hnum : substitute (thetaK θ * L - A) = p) :
    overlapRelativeNormal r θ (normalOverlapSection r θ p hp) =
      relativeConnectingRepresentative r θ A L := by
  unfold overlapRelativeNormal normalOverlapSection
  rw [AddEquiv.apply_symm_apply, Iso.hom_inv_id_apply]
  apply (overlapNormalModuleEquiv r θ).injective
  rw [relativeConnectingRepresentative_comparison, connectingRepresentative_eq,
    overlapFirstRelativeFrameEquiv_comparison]
  apply congrArg (overlapKernelEquivalence r θ)
  rw [normalOverlapCoordinate_coefficient r θ A L p hp hnum]
  have hx := coordinateUnit_value r θ _ _ _ (overlapFirstFrame_factorization r θ)
  change (overlapFirstCoordinateUnit r θ : Overlap r θ) = _ at hx
  rw [← hx, mul_assoc, ← mul_pow, (overlapFirstCoordinateUnit r θ).mul_inv,
    one_pow, mul_one]

theorem literal_overlapRelativeNormal :
    overlapRelativeNormal 57 1
      (normalOverlapSection 57 1 ambientNormalNumerator ambientNormalNumerator_homogeneous) =
        relativeConnectingRepresentative 57 1 derivativeA 0 := by
  apply normalOverlapSection_relative
  simp only [mul_zero, zero_sub, map_neg]
  change -substitute ambientTest = ambientNormalNumerator
  rw [substitute_ambientTest, neg_neg]
  rfl

#print axioms firstRelativeFrameEquiv_equation
#print axioms relativeNormalFrame_transition
#print axioms normalOverlapSection_relative
#print axioms literal_overlapRelativeNormal


/-- Canonical tensor-Hom restrictions, transported through the proved
relative-conormal comparisons. -/
def firstRelativeRestriction (r θ : ℂ) (ν : RelativeNormal r θ (FirstOpen r θ)) :
    RelativeNormal r θ (Overlap r θ) :=
  (overlapNormalModuleEquiv r θ).symm
    (firstKernelRestriction r θ (firstNormalModuleEquiv r θ ν))

def secondRelativeRestriction (r θ : ℂ) (ν : RelativeNormal r θ (SecondOpen r θ)) :
    RelativeNormal r θ (Overlap r θ) :=
  (overlapNormalModuleEquiv r θ).symm
    (secondKernelRestriction r θ (secondNormalModuleEquiv r θ ν))

theorem firstRelativeRestriction_equation (r θ : ℂ)
    (ν : RelativeNormal r θ (FirstOpen r θ)) (i : Fin 3) :
    firstRelativeRestriction r θ ν (relativeEquationClass r θ (Overlap r θ) i) =
      firstRestriction r θ (ν (relativeEquationClass r θ (FirstOpen r θ) i)) := by
  have he := normalModuleEquiv_symm_equation r θ (FirstOpen r θ)
    (firstNormalModuleEquiv r θ ν) i
  change (firstNormalModuleEquiv r θ).symm (firstNormalModuleEquiv r θ ν)
      (relativeEquationClass r θ (FirstOpen r θ) i) =
    (firstNormalModuleEquiv r θ ν).val (curveClass r θ i) at he
  rw [LinearEquiv.symm_apply_apply] at he
  change (normalModuleEquiv r θ (Overlap r θ)).symm
    (firstKernelRestriction r θ (firstNormalModuleEquiv r θ ν)) _ = _
  rw [normalModuleEquiv_symm_equation]
  change curveRestriction r θ (firstRestrictionAlg r θ)
    (firstNormalModuleEquiv r θ ν).val (curveClass r θ i) = _
  rw [curveRestriction_class]
  exact congrArg (firstRestriction r θ) he.symm

theorem secondRelativeRestriction_equation (r θ : ℂ)
    (ν : RelativeNormal r θ (SecondOpen r θ)) (i : Fin 3) :
    secondRelativeRestriction r θ ν (relativeEquationClass r θ (Overlap r θ) i) =
      secondRestriction r θ (ν (relativeEquationClass r θ (SecondOpen r θ) i)) := by
  have he := normalModuleEquiv_symm_equation r θ (SecondOpen r θ)
    (secondNormalModuleEquiv r θ ν) i
  change (secondNormalModuleEquiv r θ).symm (secondNormalModuleEquiv r θ ν)
      (relativeEquationClass r θ (SecondOpen r θ) i) =
    (secondNormalModuleEquiv r θ ν).val (curveClass r θ i) at he
  rw [LinearEquiv.symm_apply_apply] at he
  change (normalModuleEquiv r θ (Overlap r θ)).symm
    (secondKernelRestriction r θ (secondNormalModuleEquiv r θ ν)) _ = _
  rw [normalModuleEquiv_symm_equation]
  change curveRestriction r θ (secondRestrictionAlg r θ)
    (secondNormalModuleEquiv r θ ν).val (curveClass r θ i) = _
  rw [curveRestriction_class]
  exact congrArg (secondRestriction r θ) he.symm

private theorem firstProjectiveRestriction_value (r θ : ℂ) (a : FirstProjectiveRing r θ) :
    (firstProjectiveRestriction r θ a).val = firstRestriction r θ a.val := by
  have h := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    (firstDegreeOneEquiv_restriction r θ a)
  rw [firstDegreeOneRestriction_coe] at h
  change firstRestriction r θ
    (a.val * algebraMap (CurveRing r θ) (FirstOpen r θ) (curveMap r θ (X 1))) =
      (firstProjectiveRestriction r θ a).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) at h
  rw [map_mul] at h
  have hx := IsLocalization.Away.awayToAwayRight_eq (R := CurveRing r θ)
    (S := FirstOpen r θ) (P := Overlap r θ) (curveG1 r θ) (curveG2 r θ)
    (curveMap r θ (X 1))
  change firstRestriction r θ _ = _ at hx
  rw [hx] at h
  exact ((frameCoordinate_isUnit r θ _ _ _ (overlapFirstFrame_factorization r θ)).mul_right_cancel h).symm

private theorem secondProjectiveRestriction_value (r θ : ℂ) (a : SecondProjectiveRing r θ) :
    (secondProjectiveRestriction r θ a).val = secondRestriction r θ a.val := by
  have h := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    (secondDegreeOneEquiv_restriction r θ a)
  rw [secondDegreeOneRestriction_coe] at h
  change secondRestriction r θ
    (a.val * algebraMap (CurveRing r θ) (SecondOpen r θ) (curveMap r θ (X 2))) =
      (secondProjectiveRestriction r θ a).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2)) at h
  rw [map_mul] at h
  have hx := IsLocalization.Away.awayToAwayLeft_eq (R := CurveRing r θ)
    (S := SecondOpen r θ) (P := Overlap r θ) (curveG2 r θ) (curveG1 r θ)
    (curveMap r θ (X 2))
  change secondRestriction r θ _ = _ at hx
  rw [hx] at h
  exact ((frameCoordinate_isUnit r θ _ _ _ (overlapSecondFrame_factorization r θ)).mul_right_cancel h).symm

private theorem firstCoordinateUnit_map (r θ : ℂ) :
    Units.map (firstRestriction r θ).toMonoidHom (firstCoordinateUnit r θ) =
      overlapFirstCoordinateUnit r θ := by
  apply Units.ext
  change firstRestriction r θ (firstCoordinateUnit r θ : FirstOpen r θ) =
    (overlapFirstCoordinateUnit r θ : Overlap r θ)
  simp only [firstCoordinateUnit, overlapFirstCoordinateUnit, coordinateUnit_value,
    firstRestriction, IsLocalization.Away.awayToAwayRight_eq]

private theorem secondCoordinateUnit_map (r θ : ℂ) :
    Units.map (secondRestriction r θ).toMonoidHom (secondCoordinateUnit r θ) =
      overlapSecondCoordinateUnit r θ := by
  apply Units.ext
  change secondRestriction r θ (secondCoordinateUnit r θ : SecondOpen r θ) =
    (overlapSecondCoordinateUnit r θ : Overlap r θ)
  simp only [secondCoordinateUnit, overlapSecondCoordinateUnit, coordinateUnit_value,
    secondRestriction, IsLocalization.Away.awayToAwayLeft_eq]

private theorem firstInverseCoordinate_restriction (r θ : ℂ) :
    firstRestriction r θ (↑((firstCoordinateUnit r θ)⁻¹) : FirstOpen r θ) =
      (↑((overlapFirstCoordinateUnit r θ)⁻¹) : Overlap r θ) := by
  change (Units.map (firstRestriction r θ).toMonoidHom ((firstCoordinateUnit r θ)⁻¹) : Overlap r θ) = _
  rw [map_inv, firstCoordinateUnit_map]

private theorem secondInverseCoordinate_restriction (r θ : ℂ) :
    secondRestriction r θ (↑((secondCoordinateUnit r θ)⁻¹) : SecondOpen r θ) =
      (↑((overlapSecondCoordinateUnit r θ)⁻¹) : Overlap r θ) := by
  change (Units.map (secondRestriction r θ).toMonoidHom ((secondCoordinateUnit r θ)⁻¹) : Overlap r θ) = _
  rw [map_inv, secondCoordinateUnit_map]

theorem firstRelativeFrame_restriction (r θ : ℂ) (a : FirstProjectiveRing r θ) :
    firstRelativeRestriction r θ (firstProjectiveNormalSection r θ a) =
      overlapFirstRelativeFrameEquiv r θ (firstProjectiveRestriction r θ a).val := by
  apply (overlapNormalModuleEquiv r θ).injective
  rw [firstRelativeRestriction, LinearEquiv.apply_symm_apply]
  change firstKernelRestriction r θ (firstNormalModuleEquiv r θ (firstRelativeFrameEquiv r θ a.val)) = _
  rw [firstRelativeFrameEquiv_comparison, firstKernelRestriction_trivialization,
    overlapFirstRelativeFrameEquiv_comparison]
  apply congrArg (overlapKernelEquivalence r θ)
  rw [map_mul, map_pow, firstInverseCoordinate_restriction, firstProjectiveRestriction_value]

theorem secondRelativeFrame_restriction (r θ : ℂ) (a : SecondProjectiveRing r θ) :
    secondRelativeRestriction r θ (secondProjectiveNormalSection r θ a) =
      overlapSecondRelativeFrameEquiv r θ (secondProjectiveRestriction r θ a).val := by
  apply (overlapNormalModuleEquiv r θ).injective
  rw [secondRelativeRestriction, LinearEquiv.apply_symm_apply]
  change secondKernelRestriction r θ (secondNormalModuleEquiv r θ (secondRelativeFrameEquiv r θ a.val)) = _
  rw [secondRelativeFrameEquiv_comparison, secondKernelRestriction_trivialization,
    overlapSecondRelativeFrameEquiv_comparison]
  apply congrArg (overlapKernelEquivalence r θ)
  rw [map_mul, map_pow, secondInverseCoordinate_restriction, secondProjectiveRestriction_value]

#print axioms firstRelativeRestriction_equation
#print axioms secondRelativeRestriction_equation
#print axioms firstRelativeFrame_restriction
#print axioms secondRelativeFrame_restriction


/-! ## The same seven cubic tests on a genuine normal-frame H¹ class -/

def incidenceNormalNumerator : Poly := obstructionCubic * selectedCubic

theorem incidenceNormalNumerator_homogeneous : incidenceNormalNumerator.IsHomogeneous 6 :=
  obstructionCubic_homogeneous.mul selectedCubic_homogeneous

def selectedIncidenceNormalClass : NormalSheafH1 57 1 :=
  normalClass 57 1 (by norm_num) incidenceNormalNumerator incidenceNormalNumerator_homogeneous

def testCubicPairing (j : Fin 7) : NormalSheafH1 57 1 →+ DifferentialSheafH1 57 1 :=
  literalCanonicalH1Equiv.toAddMonoidHom.comp
    (cubicH1Map 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j))

theorem testCubicPairing_selectedIncidenceNormalClass (j : Fin 7) :
    testCubicPairing j selectedIncidenceNormalClass = selectedTestClass j := by
  change literalCanonicalH1Equiv
    (cubicH1Map 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j)
      (normalClass 57 1 (by norm_num) incidenceNormalNumerator incidenceNormalNumerator_homogeneous)) = _
  rw [cubicH1Map_normalClass]
  rfl

theorem selectedIncidenceNormalClass_in_seven_kernels (j : Fin 7) :
    testCubicPairing j selectedIncidenceNormalClass = 0 :=
  (testCubicPairing_selectedIncidenceNormalClass j).trans (selectedTestClass_zero j)

theorem selectedIncidenceNormalSection_relative :
    overlapRelativeNormal 57 1
      (normalOverlapSection 57 1 incidenceNormalNumerator incidenceNormalNumerator_homogeneous) =
        relativeConnectingRepresentative 57 1 0 weightedSelectedCubic := by
  apply normalOverlapSection_relative
  simp only [sub_zero, map_mul, thetaK, substitute_literalK,
    substitute_weightedSelectedCubic, incidenceNormalNumerator]

theorem firstProjectiveNormalSection_mul (r θ : ℂ) (a b : FirstProjectiveRing r θ) :
    firstProjectiveNormalSection r θ (a * b) = a.val • firstProjectiveNormalSection r θ b := by
  change firstRelativeFrameEquiv r θ (a * b).val = a.val • firstRelativeFrameEquiv r θ b.val
  rw [HomogeneousLocalization.val_mul]
  exact (firstRelativeFrameEquiv r θ).map_smul a.val b.val

theorem secondProjectiveNormalSection_mul (r θ : ℂ) (a b : SecondProjectiveRing r θ) :
    secondProjectiveNormalSection r θ (a * b) = a.val • secondProjectiveNormalSection r θ b := by
  change secondRelativeFrameEquiv r θ (a * b).val = a.val • secondRelativeFrameEquiv r θ b.val
  rw [HomogeneousLocalization.val_mul]
  exact (secondRelativeFrameEquiv r θ).map_smul a.val b.val

#print axioms testCubicPairing_selectedIncidenceNormalClass
#print axioms selectedIncidenceNormalClass_in_seven_kernels
#print axioms selectedIncidenceNormalSection_relative
#print axioms firstProjectiveNormalSection_mul
#print axioms secondProjectiveNormalSection_mul

end CycleQ2GeometricProjectiveNormalClass
end
