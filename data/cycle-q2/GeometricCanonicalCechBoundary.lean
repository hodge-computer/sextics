import Proposal.GeometricProjectiveCanonicalH1
import Proposal.GeometricNormalConnecting

/-!
# The explicit residue section and its genuine cohomology boundary

Naturality of the actual Mayer--Vietoris connecting map identifies the
degree-nine canonical class with the boundary of its actual differential
section on the overlap. The section is expressed in the inverse canonical
frame, so its coefficient and projective orientation are retained.

The final normal-cochain comparison concerns the already constructed
surface-relative normal homomorphism. It does not replace the further
Cartier boundary to surface cohomology or a geometric Serre trace.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCanonicalCechBoundary

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricConeCech.HZero

section Naturality

universe v w
variable {C : Type v} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)

/-- The actual functorial cohomology map is postcomposition in Ext. -/
theorem cohomologyMap_apply (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U) x =
      x.comp (Ext.mk₀ f) (add_zero n) := rfl

/-- The actual H⁰-to-sections comparison is natural in the sheaf. -/
theorem sectionsEquiv_map (U : C) (x : F.H' 0 U) :
    sectionsEquiv G U (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (sectionsEquiv F U x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  rw [cohomologyMap_apply, Ext.mk₀_comp_mk₀, sectionsEquiv_mk₀, sectionsEquiv_mk₀,
    (sheafificationAdjunction J AddCommGrpCat).homEquiv_naturality_right]
  rfl

theorem sectionsEquiv_symm_map (U : C) (x : F.obj.obj (op U)) :
    ((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U)
        ((sectionsEquiv F U).symm x) =
      (sectionsEquiv G U).symm (f.hom.app (op U) x) := by
  apply (sectionsEquiv G U).injective
  rw [sectionsEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

variable [HasWeakSheafify J (Type v)]

/-- Functoriality of the genuine Mayer--Vietoris connecting homomorphism,
proved from associativity of Ext composition. -/
theorem mayerVietoris_delta_naturality (S : J.MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : F.H' n₀ S.X₁) :
    ((Sheaf.cohomologyPresheafFunctor J n₁).map f).app (op S.X₄)
        (S.δ F n₀ n₁ h x) =
      S.δ G n₀ n₁ h
        (((Sheaf.cohomologyPresheafFunctor J n₀).map f).app (op S.X₁) x) := by
  let h' : 1 + n₀ = n₁ := (Nat.add_comm 1 n₀).trans h
  change (S.shortComplex_shortExact.extClass.comp x h').comp (Ext.mk₀ f) (add_zero n₁) =
    S.shortComplex_shortExact.extClass.comp (x.comp (Ext.mk₀ f) (add_zero n₀)) h'
  exact Ext.comp_assoc_of_third_deg_zero S.shortComplex_shortExact.extClass x (Ext.mk₀ f) h'

end Naturality

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricProjectiveCanonical
  CycleQ2GeometricProjectiveCanonicalH1 CycleQ2GeometricProjectiveNonzero
  CycleQ2GeometricCanonicalGluing CycleQ2GeometricProjectiveDifferentialForms

private theorem root_ne_zero (r : ℂ) (hr : r ^ 3 = 2) : r ≠ 0 := by
  intro hz
  simp [hz] at hr

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The literal coefficient in the original first degree-one frame. -/
def degreeOneSectionCoefficient (r θ : ℂ) (z : OverlapDegreeOne r θ) :
    Γ(projectiveCurve r θ, overlapProjectivePatch r θ) :=
  (overlapProjectiveSectionsIso r θ).hom ((overlapFirstDegreeOneEquiv r θ).symm z)

/-- This coefficient is fixed by the original homogeneous localization:
multiplication by X₁ recovers the degree-one section. -/
theorem degreeOneSectionCoefficient_coordinate (r θ : ℂ) (z : OverlapDegreeOne r θ) :
    ((overlapProjectiveSectionsIso r θ).inv (degreeOneSectionCoefficient r θ z)).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
      (z : Overlap r θ) := by
  rw [degreeOneSectionCoefficient, Iso.hom_inv_id_apply]
  have h := congrArg (fun a : OverlapDegreeOne r θ => (a : Overlap r θ))
    ((overlapFirstDegreeOneEquiv r θ).apply_symm_apply z)
  change ((overlapFirstDegreeOneEquiv r θ).symm z).val *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
    (z : Overlap r θ) at h
  exact h

/-- The inverse first canonical frame on the original denominator overlap. -/
def canonicalOverlapGenerator (r : ℂ) (hr : r ^ 3 = 2) :
    (projectiveDifferentialSheaf r 0).val.obj (op (overlapProjectivePatch r 0)) :=
  frameGenerator (firstDenominatorFrame r hr) (overlapProjectivePatch r 0)
    ((overlapProjectivePatch_eq r 0).le.trans inf_le_left)

/-- Its orientation is the actual restriction of the first, negatively
oriented affine cofactor form used in the canonical isomorphism. -/
theorem canonicalOverlapGenerator_restriction (r : ℂ) (hr : r ^ 3 = 2) :
    canonicalOverlapGenerator r hr =
      (projectiveDifferentialSheaf r 0).val.map
        (homOfLE ((overlapProjectivePatch_eq r 0).le.trans inf_le_left)).op
        (firstDenominatorForm r hr (projectiveDifferentialSheaf r 0)
          (projectiveUniversalDifferential r 0)) := by
  change frameGenerator (firstDenominatorFrame r hr) (overlapProjectivePatch r 0) _ = _
  rw [← frameGenerator_naturality (firstDenominatorFrame r hr)
    ((overlapProjectivePatch_eq r 0).le.trans inf_le_left) le_rfl,
    firstDenominatorFrame_generator]
  rfl

/-- The actual homogeneous section transported to the differential sheaf. -/
def canonicalOverlapSection (r : ℂ) (hr : r ^ 3 = 2) (z : OverlapDegreeOne r 0) :
    (projectiveDifferentialSheaf r 0).val.obj (op (overlapProjectivePatch r 0)) :=
  (projectiveCanonicalIso r hr).inv.val.app (op (overlapProjectivePatch r 0))
    (overlapDegreeOneSectionsEquiv r 0 z)

theorem canonicalInverse_overlap_frame (r : ℂ) (hr : r ^ 3 = 2)
    (s : (degreeOneSheaf r 0).obj.obj (op (overlapProjectivePatch r 0))) :
    (projectiveCanonicalIso r hr).inv.val.app (op (overlapProjectivePatch r 0)) s =
      overlapSheafFrame r 0 s • canonicalOverlapGenerator r hr := by
  have hs := canonicalIso_inv_first (projectiveCurve r 0).sheaf
    (firstProjectivePatch r 0) (secondProjectivePatch r 0) (overlapProjectivePatch r 0)
    (overlapProjectivePatch_eq r 0) (projectiveTransitionUnit r 0)
    (projectiveDifferentialSheaf r 0) (firstDenominatorFrame r hr) (secondDenominatorFrame r hr)
    (projective_twoOpen_cover r 0 (root_ne_zero r hr))
    (generatorTransition_of_overlap (projectiveCurve r 0).sheaf
      (firstProjectivePatch r 0) (secondProjectivePatch r 0) (overlapProjectivePatch r 0)
      (overlapProjectivePatch_eq r 0) (projectiveTransitionUnit r 0)
      (projectiveDifferentialSheaf r 0) (firstDenominatorFrame r hr) (secondDenominatorFrame r hr)
      (denominatorFrame_transition r hr))
    (overlapProjectivePatch r 0) ((overlapProjectivePatch_eq r 0).le.trans inf_le_left) s
  change (projectiveCanonicalIso r hr).inv.val.app (op (overlapProjectivePatch r 0)) s =
    ((firstDenominatorFrame r hr).app (overlapProjectivePatch r 0)
      ((overlapProjectivePatch_eq r 0).le.trans inf_le_left)).symm
      (overlapSheafFrame r 0 s) at hs
  rw [hs]
  have h := ((firstDenominatorFrame r hr).app (overlapProjectivePatch r 0)
      ((overlapProjectivePatch_eq r 0).le.trans inf_le_left)).symm.map_smul
      (overlapSheafFrame r 0 s) (1 : Γ(projectiveCurve r 0, overlapProjectivePatch r 0))
  simpa only [smul_eq_mul, mul_one, canonicalOverlapGenerator, frameGenerator] using h

/-- The comparison retains the exact coefficient, rather than merely
identifying one-dimensional spaces up to a nonzero scalar. -/
theorem canonicalOverlapSection_eq (r : ℂ) (hr : r ^ 3 = 2) (z : OverlapDegreeOne r 0) :
    canonicalOverlapSection r hr z =
      degreeOneSectionCoefficient r 0 z • canonicalOverlapGenerator r hr := by
  rw [canonicalOverlapSection, canonicalInverse_overlap_frame,
    overlapDegreeOneSectionsEquiv_coordinate]
  rfl

/-- The actual connecting homomorphism for the actual differential sheaf. -/
def canonicalMayerVietorisBoundary (r : ℂ) (hr : r ^ 3 = 2) :
    (projectiveDifferentialSheaf r 0).val.obj (op (overlapProjectivePatch r 0)) →+
      DifferentialSheafH1 r 0 :=
  ((projectiveMayerVietoris r 0 (root_ne_zero r hr)).δ
    (differentialAdditiveSheaf r 0) 0 1 rfl).hom.comp
      (sectionsEquiv (differentialAdditiveSheaf r 0) (overlapProjectivePatch r 0)).symm.toAddMonoidHom

theorem canonicalH1Equiv_apply (r : ℂ) (hr : r ^ 3 = 2) (x : ProjectiveSheafH1 r 0) :
    canonicalH1Equiv r hr x =
      ((Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (projectiveCurve r 0)) 1).map
          (canonicalAdditiveIso r hr).inv).app (op ⊤) x := rfl

/-- Transport through the canonical sheaf isomorphism commutes with the
genuine connecting homomorphism, including its actual overlap input. -/
theorem canonicalH1Equiv_connecting (r : ℂ) (hr : r ^ 3 = 2)
    (z : OverlapDegreeOne r 0) :
    canonicalH1Equiv r hr (degreeOneConnecting r 0 (root_ne_zero r hr) z) =
      canonicalMayerVietorisBoundary r hr (canonicalOverlapSection r hr z) := by
  rw [canonicalH1Equiv_apply]
  change ((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve r 0)) 1).map
        (canonicalAdditiveIso r hr).inv).app (op ⊤)
      ((projectiveMayerVietoris r 0 (root_ne_zero r hr)).δ (degreeOneSheaf r 0) 0 1 rfl
        ((sectionsEquiv (degreeOneSheaf r 0) (overlapProjectivePatch r 0)).symm
          (overlapDegreeOneSectionsEquiv r 0 z))) = _
  have hnat := mayerVietoris_delta_naturality (canonicalAdditiveIso r hr).inv
    (projectiveMayerVietoris r 0 (root_ne_zero r hr)) 0 1 rfl
    ((sectionsEquiv (degreeOneSheaf r 0) (overlapProjectivePatch r 0)).symm
      (overlapDegreeOneSectionsEquiv r 0 z))
  have hzero := sectionsEquiv_symm_map (canonicalAdditiveIso r hr).inv
    (overlapProjectivePatch r 0) (overlapDegreeOneSectionsEquiv r 0 z)
  exact hnat.trans (congrArg
    (fun x : (differentialAdditiveSheaf r 0).H' 0 (overlapProjectivePatch r 0) =>
      (projectiveMayerVietoris r 0 (root_ne_zero r hr)).δ
        (differentialAdditiveSheaf r 0) 0 1 rfl x) hzero)

/-- The degree-nine class is the Mayer--Vietoris boundary of the exact
coefficient times the oriented actual canonical generator. -/
theorem degreeNineCanonicalClass_eq_boundary (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCanonicalClass r hr p hp =
      canonicalMayerVietorisBoundary r hr
        (degreeOneSectionCoefficient r 0 (degreeNineRepresentative r 0 p hp) •
          canonicalOverlapGenerator r hr) := by
  change canonicalH1Equiv r hr
      (degreeOneConnecting r 0 (root_ne_zero r hr) (degreeNineRepresentative r 0 p hp)) = _
  rw [canonicalH1Equiv_connecting, canonicalOverlapSection_eq]

/-! ## The actual surface-relative normal cochain -/

open CycleQ2ConormalJacobian CycleQ2ActualNormalCech
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricRelativeNormalConnecting

/-- The numerator fixed by the actual two local normal lifts, paired with
the polynomial test section. No trace-based scalar is chosen. -/
def pairedNormalNumerator (θ : ℂ) (A L : WeightedPoly) (σ : Poly) : Poly :=
  substitute (thetaK θ * L - A) * σ

/-- The scalar is extracted from the actual surface-relative normal
homomorphism, through its proved natural conormal comparison. -/
def pairedRelativeNormalCoefficient (r θ : ℂ) (A L : WeightedPoly) (σ : Poly) :
    Overlap r θ :=
  (overlapKernelEquivalence r θ).symm
      (overlapNormalModuleEquiv r θ (relativeConnectingRepresentative r θ A L)) *
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ)

theorem pairedRelativeNormalCoefficient_eq (r θ : ℂ) (A L : WeightedPoly) (σ : Poly) :
    pairedRelativeNormalCoefficient r θ A L σ =
      normalOverlapCoefficient r θ A L *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
  rw [pairedRelativeNormalCoefficient, relativeConnectingRepresentative_comparison,
    connectingRepresentative_eq, LinearEquiv.symm_apply_apply]

/-- The same coefficient is determined by evaluation on the actual first
curve equation, divided by its actual cofactor unit. -/
theorem pairedRelativeNormalCoefficient_equation (r θ : ℂ) (A L : WeightedPoly) (σ : Poly) :
    pairedRelativeNormalCoefficient r θ A L σ =
      relativeConnectingRepresentative r θ A L
          (relativeEquationClass r θ (Overlap r θ) 0) *
        (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) *
          algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
  rw [pairedRelativeNormalCoefficient_eq, relativeConnectingRepresentative_equation]
  change normalOverlapCoefficient r θ A L *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) =
    (normalOverlapCoefficient r θ A L * overlapAmbient r θ originalG2) *
      (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ)
  have hu := coe_secondOverlapUnit r θ
  change (secondOverlapUnit r θ : Overlap r θ) = overlapAmbient r θ originalG2 at hu
  rw [← hu, mul_assoc (normalOverlapCoefficient r θ A L),
    (secondOverlapUnit r θ).mul_inv, mul_one]

/-- Multiplication by the actual product of denominator equations clears
the two specified localization inverses in the normal lift difference. -/
theorem normalOverlapCoefficient_mul_denominator (r θ : ℂ) (A L : WeightedPoly) :
    normalOverlapCoefficient r θ A L *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ) =
      overlapAmbient r θ (thetaK θ * L - A) := by
  rw [map_mul, ← coe_firstOverlapUnit, ← coe_secondOverlapUnit]
  calc
    _ = (overlapAmbient r θ (thetaK θ) * overlapAmbient r θ L - overlapAmbient r θ A) *
        ((↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) * (firstOverlapUnit r θ : Overlap r θ)) *
        ((↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) *
          (secondOverlapUnit r θ : Overlap r θ)) := by
      unfold normalOverlapCoefficient overlapCoefficient
      ring
    _ = _ := by
      rw [(firstOverlapUnit r θ).inv_mul, (secondOverlapUnit r θ).inv_mul,
        mul_one, mul_one, map_sub, map_mul]

/-- The homogeneous degree-one representative has exactly the paired
actual normal coefficient, including the `k L - A` sign. -/
theorem degreeNineRepresentative_relativeNormal (r θ : ℂ) (A L : WeightedPoly)
    (σ : Poly) (hp : (pairedNormalNumerator θ A L σ).IsHomogeneous 9) :
    (degreeNineRepresentative r θ (pairedNormalNumerator θ A L σ) hp : Overlap r θ) =
      pairedRelativeNormalCoefficient r θ A L σ := by
  rw [pairedRelativeNormalCoefficient_eq]
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Overlap r θ) (curveG1 r θ * curveG2 r θ)).mul_right_cancel
  have hfrac :
      (degreeNineRepresentative r θ (pairedNormalNumerator θ A L σ) hp : Overlap r θ) *
          algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ) =
        algebraMap (CurveRing r θ) (Overlap r θ)
          (curveMap r θ (pairedNormalNumerator θ A L σ)) := by
    change Localization.mk _ _ * _ = _
    rw [Localization.mk_eq_mk']
    simpa only [pow_one] using
      IsLocalization.mk'_spec (Overlap r θ)
        (curveMap r θ (pairedNormalNumerator θ A L σ))
        (⟨(curveG1 r θ * curveG2 r θ) ^ 1, 1, rfl⟩ :
          Submonoid.powers (curveG1 r θ * curveG2 r θ))
  calc
    _ = algebraMap (CurveRing r θ) (Overlap r θ)
        (curveMap r θ (pairedNormalNumerator θ A L σ)) := hfrac
    _ = overlapAmbient r θ (thetaK θ * L - A) *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
      simp only [pairedNormalNumerator, map_mul, overlapAmbient,
        ambientCurveMap, RingHom.comp_apply]
      rfl
    _ = (normalOverlapCoefficient r θ A L *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ * curveG2 r θ)) *
          algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ σ) := by
      rw [normalOverlapCoefficient_mul_denominator]
    _ = _ := by ring

/-- The paired genuine relative-normal homomorphism defines an actual
homogeneous projective section. Its degree is proved by the exact fraction
comparison, not supplied as a freeness or cohomology comparison hypothesis. -/
def pairedRelativeNormalSection (r θ : ℂ) (A L : WeightedPoly) (σ : Poly)
    (hp : (pairedNormalNumerator θ A L σ).IsHomogeneous 9) : OverlapDegreeOne r θ :=
  ⟨pairedRelativeNormalCoefficient r θ A L σ, by
    rw [← degreeNineRepresentative_relativeNormal r θ A L σ hp]
    exact (degreeNineRepresentative r θ (pairedNormalNumerator θ A L σ) hp).property⟩

theorem pairedRelativeNormalSection_eq (r θ : ℂ) (A L : WeightedPoly) (σ : Poly)
    (hp : (pairedNormalNumerator θ A L σ).IsHomogeneous 9) :
    pairedRelativeNormalSection r θ A L σ hp =
      degreeNineRepresentative r θ (pairedNormalNumerator θ A L σ) hp :=
  Subtype.ext (degreeNineRepresentative_relativeNormal r θ A L σ hp).symm

/-- A class in the actual differential-sheaf cohomology, obtained from
the paired relative-normal cochain and the genuine connecting map. -/
def relativeNormalCanonicalBoundary (r : ℂ) (hr : r ^ 3 = 2)
    (A L : WeightedPoly) (σ : Poly)
    (hp : (pairedNormalNumerator 0 A L σ).IsHomogeneous 9) : DifferentialSheafH1 r 0 :=
  canonicalMayerVietorisBoundary r hr
    (canonicalOverlapSection r hr (pairedRelativeNormalSection r 0 A L σ hp))

/-- The normal-cochain boundary is the particular degree-nine canonical
class, with its exact normalization and no comparison premise. -/
theorem relativeNormalCanonicalBoundary_eq (r : ℂ) (hr : r ^ 3 = 2)
    (A L : WeightedPoly) (σ : Poly)
    (hp : (pairedNormalNumerator 0 A L σ).IsHomogeneous 9) :
    relativeNormalCanonicalBoundary r hr A L σ hp =
      degreeNineCanonicalClass r hr (pairedNormalNumerator 0 A L σ) hp := by
  rw [relativeNormalCanonicalBoundary, pairedRelativeNormalSection_eq,
    canonicalOverlapSection_eq, degreeNineCanonicalClass_eq_boundary]

/-- The checked finite trace now detects the genuine derived boundary of
the paired actual normal cochain. This is not a claim of Serre duality. -/
theorem relativeNormalCanonicalBoundary_eq_zero_iff (r : ℂ) (hr : r ^ 3 = 2)
    (A L : WeightedPoly) (σ : Poly)
    (hp : (pairedNormalNumerator 0 A L σ).IsHomogeneous 9) :
    relativeNormalCanonicalBoundary r hr A L σ hp = 0 ↔
      traceLinear r (pairedNormalNumerator 0 A L σ) = 0 := by
  rw [relativeNormalCanonicalBoundary_eq,
    degreeNineCanonicalClass_eq_zero_iff_trace_zero]

/-- At fixed cubic equation the same comparison retains the minus sign. -/
theorem pairedNormalNumerator_fixed_h (A : WeightedPoly) (σ : Poly) :
    pairedNormalNumerator 0 A 0 σ = -(substitute A) * σ := by
  simp only [pairedNormalNumerator, mul_zero, zero_sub, map_neg]

/-! ## A fixed nonzero actual normal-cochain boundary -/

/-- For the literal ambient variation and the test cubic X₀³, the paired
numerator is this specific homogeneous monomial. -/
theorem ambientPairedNumerator_eq :
    pairedNormalNumerator 0 derivativeA 0 (X 0 ^ 3) = mon 3 0 3 3 := by
  rw [pairedNormalNumerator_fixed_h]
  simp [derivativeA, substitute, mon] <;> ring

theorem ambientPairedNumerator_homogeneous :
    (pairedNormalNumerator 0 derivativeA 0 (X 0 ^ 3)).IsHomogeneous 9 := by
  rw [ambientPairedNumerator_eq]
  exact CycleQ2SeedTrace.mon_homogeneous 3 0 3 3

/-- Direct evaluation of the already fixed finite trace, requiring no
choice of a trace-matched class or supplied nonvanishing assertion. -/
theorem trace_ambientPairedNumerator (r : ℂ) :
    traceLinear r (mon 3 0 3 3) = (1 + Complex.I) / 6 := by
  rw [traceLinear_apply]
  simp only [traceNumerator, add_mul, mul_assoc, mon_mul, coeff_add, coeff_C_mul,
    coeff_top_mon]
  norm_num <;> ring

/-- The genuine derived boundary of the paired actual ambient normal
lift difference, on the literal sparse parameter choice. -/
def ambientNormalCanonicalBoundary (r : ℂ) (hr : r ^ 3 = 2) : DifferentialSheafH1 r 0 :=
  relativeNormalCanonicalBoundary r hr derivativeA 0 (X 0 ^ 3)
    ambientPairedNumerator_homogeneous

theorem ambientNormalCanonicalBoundary_ne_zero (r : ℂ) (hr : r ^ 3 = 2) :
    ambientNormalCanonicalBoundary r hr ≠ 0 := by
  intro hz
  have htrace := (relativeNormalCanonicalBoundary_eq_zero_iff r hr derivativeA 0
    (X 0 ^ 3) ambientPairedNumerator_homogeneous).mp hz
  rw [ambientPairedNumerator_eq, trace_ambientPairedNumerator] at htrace
  have hc : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  exact (div_ne_zero hc (by norm_num : (6 : ℂ) ≠ 0)) htrace

end CycleQ2GeometricCanonicalCechBoundary

end
