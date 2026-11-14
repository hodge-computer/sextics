import Proposal.GeometricCanonicalResidueScalar
import Proposal.GeometricLiteralHOne
import Proposal.GeometricSurfaceDifferentialCharts
import Proposal.GeometricCanonicalResidueNonzero

/-!
# The actual curve H¹ image inside the pushed canonical sheaf

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

The original two-quartic Mayer--Vietoris boundary on the curve and the
actual closed-pushforward boundary have the same kernel. Their scalar
actions agree by the proved complex-coefficient square of the original
immersion. The already fixed one-dimensional coordinate on curve H¹
therefore gives a linear injection into pushed H¹ which agrees with the
actual pushforward boundary on every overlap section.

Every cubic image of the original normal class lies in this concrete
image. The construction does not assert surjectivity onto all pushed H¹,
and uses neither a general direct-image cohomology comparison nor a
chosen replacement for the residue connecting morphism.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalCurveImage

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2CanonicalResidueSheaf CycleQ2CanonicalResidueDiagram
  CycleQ2CanonicalResidueScalar CycleQ2ClosedSupportCohomology
  CycleQ2ClosedSupportBoundary CycleQ2SurfaceNormalCohomology
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricProjectiveCohomologyLinear CycleQ2GeometricLiteralCanonicalClass
  CycleQ2GeometricLiteralHOne CycleQ2GeometricIncidenceCechSurjectivity
  CycleQ2GeometricProjectiveNormalClass CycleQ2SurfaceCechTwoScalar
  CycleQ2SeedTrace CycleQ2SurfaceCubicGluing

local instance curveHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Curve) AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev CurveAdditive := differentialAdditiveSheaf (57 : ℂ) 1
abbrev CurveHOne := DifferentialSheafH1 (57 : ℂ) 1
abbrev PushedHOne := canonicalResidueAdditiveComplex.X₃.H' 1 ⊤
abbrev Overlap := overlapProjectivePatch (57 : ℂ) 1
abbrev OverlapForms := CurveAdditive.obj.obj (op Overlap)

local instance overlapModule : Module Γ(Curve, Overlap) OverlapForms :=
  (CurveForms.val.obj (op Overlap)).isModule

/-- The original two-quartic square, with its original boundary sign. -/
def sourceSquare : (Opens.grothendieckTopology Curve).MayerVietorisSquare :=
  coverSquare (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num))

def sourceBoundary : OverlapForms →+ CurveHOne :=
  sectionBoundary CurveAdditive sourceSquare

/-- The unchanged target-space boundary of the closed immersion. -/
def targetBoundary : OverlapForms →+ PushedHOne :=
  pushforwardBoundary immersion.base (curveClosedEmbedding 57 1) CurveAdditive
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num))

theorem targetBoundary_zero_iff (z : OverlapForms) :
    targetBoundary z = 0 ↔ sourceBoundary z = 0 :=
  pushforwardBoundary_zero_iff immersion.base (curveClosedEmbedding 57 1) CurveAdditive
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num)) z

/-- Actual module pushforward carries the original surface scalar to
the original curve scalar. This is a sectionwise equality of sheaf maps. -/
theorem pushed_scalarEnd (c : ℂ) :
    scalarEnd Surface.sheaf (surfaceGlobalCoefficient 57 1) ResidueTarget c =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} immersion.base).map
        (scalarEnd Curve.sheaf (projectiveGlobalCoefficient 57 1) CurveForms c) := by
  ext O x
  change immersion.app O.unop
      (coefficientOn Surface.sheaf (surfaceGlobalCoefficient 57 1) O.unop c) • x =
    coefficientOn Curve.sheaf (projectiveGlobalCoefficient 57 1)
      (immersion ⁻¹ᵁ O.unop) c • x
  rw [CycleQ2GeometricSurfaceComplexRestriction.curveToSurface_coefficient_app]

theorem sourceBoundary_scalar (c : ℂ) (z : OverlapForms) :
    sourceBoundary
        (coefficientOn Curve.sheaf (projectiveGlobalCoefficient 57 1) Overlap c • z) =
      c • sourceBoundary z := by
  exact (sectionBoundary_map
    (scalarEnd Curve.sheaf (projectiveGlobalCoefficient 57 1) CurveForms c)
    sourceSquare z).symm

theorem targetBoundary_scalar (c : ℂ) (z : OverlapForms) :
    targetBoundary
        (coefficientOn Curve.sheaf (projectiveGlobalCoefficient 57 1) Overlap c • z) =
      c • targetBoundary z := by
  have h := pushforwardBoundary_map immersion.base (curveClosedEmbedding 57 1)
    (scalarEnd Curve.sheaf (projectiveGlobalCoefficient 57 1) CurveForms c)
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num)) z
  rw [← pushed_scalarEnd] at h
  exact h.symm

/-- The original fixed canonical coordinate is represented by this actual
overlap differential. The older canonical isomorphism is used exactly as
in the definition of `literalCanonicalNormalization`. -/
def normalizationSection : OverlapForms :=
  literalCanonicalAdditiveIso.inv.hom.app (op Overlap)
    (overlapDegreeOneSectionsEquiv 57 1
      (degreeNineRepresentative 57 1 (mon 0 0 0 9) (mon_homogeneous 0 0 0 9)))

theorem sourceBoundary_normalization :
    sourceBoundary normalizationSection = literalCanonicalNormalization := by
  have h := sectionBoundary_map literalCanonicalAdditiveIso.inv sourceSquare
    (overlapDegreeOneSectionsEquiv 57 1
      (degreeNineRepresentative 57 1 (mon 0 0 0 9) (mon_homogeneous 0 0 0 9)))
  exact h.symm

def pushedNormalization : PushedHOne := targetBoundary normalizationSection

theorem pushedNormalization_ne_zero : pushedNormalization ≠ 0 := by
  intro h
  apply literalCanonicalNormalization_ne_zero
  rw [← sourceBoundary_normalization]
  exact (targetBoundary_zero_iff normalizationSection).mp h

/-- This map uses the already fixed curve coordinate. The following
factorization proves that it is the genuine closed-pushforward map on
every class presented by the original Mayer--Vietoris boundary. -/
def pushforwardFromCurve : CurveHOne →ₗ[ℂ] PushedHOne :=
  (LinearMap.toSpanSingleton ℂ PushedHOne pushedNormalization).comp
    literalCanonicalCoordinate

@[simp] theorem pushforwardFromCurve_apply (x : CurveHOne) :
    pushforwardFromCurve x = literalCanonicalCoordinate x • pushedNormalization := rfl

@[simp] theorem pushforwardFromCurve_normalization :
    pushforwardFromCurve literalCanonicalNormalization = pushedNormalization := by
  rw [pushforwardFromCurve_apply, literalCanonicalCoordinate_normalization, one_smul]

/-- Equal boundary kernels and the actual scalar square determine the
pushforward of every overlap section, without a target surjectivity premise. -/
theorem targetBoundary_factor (z : OverlapForms) :
    targetBoundary z = pushforwardFromCurve (sourceBoundary z) := by
  let c := literalCanonicalCoordinate (sourceBoundary z)
  let a := coefficientOn Curve.sheaf (projectiveGlobalCoefficient 57 1) Overlap c
  have hs : sourceBoundary (z - a • normalizationSection) = 0 := by
    apply (literalCanonicalCoordinate_eq_zero_iff _).mp
    rw [map_sub, sourceBoundary_scalar, sourceBoundary_normalization,
      map_sub, map_smul, literalCanonicalCoordinate_normalization, smul_eq_mul,
      mul_one]
    exact sub_self c
  have ht := (targetBoundary_zero_iff (z - a • normalizationSection)).mpr hs
  rw [map_sub, targetBoundary_scalar, sub_eq_zero] at ht
  exact ht

theorem pushforwardFromCurve_injective : Function.Injective pushforwardFromCurve := by
  intro x y h
  apply literalCanonicalNormalizationEquiv.symm.injective
  exact (smul_left_injective ℂ pushedNormalization_ne_zero) h

/-- The actual connecting homomorphism restricted to the concrete image
of curve H¹, with its intrinsic complex module structures. -/
def canonicalConnectingOnCurve :
    CurveHOne →ₗ[ℂ] canonicalResidueAdditiveComplex.X₁.H' 2 ⊤ :=
  (canonicalOpenConnectingLinear ⊤).comp pushforwardFromCurve

@[simp] theorem canonicalConnectingOnCurve_apply (x : CurveHOne) :
    canonicalConnectingOnCurve x =
      canonicalOpenConnecting ⊤ (pushforwardFromCurve x) := rfl

section ActualCubicImages

open CycleQ2GlobalCubicAdjunctionCohomology
  CycleQ2GeometricIntrinsicCartierCohomology

/-- Forget only the module structure of the actual cubic adjunction's
canonical isomorphism, retaining its own prescribed orientation. -/
def cubicCanonicalMap : degreeOneSheaf 57 1 ⟶ CurveAdditive :=
  (SheafOfModules.toSheaf (ringSheaf Curve.sheaf)).map literalCanonicalModuleIso.hom

def cubicOverlapSection (p : WeightedCubic) : OverlapForms :=
  cubicCanonicalMap.hom.app (op Overlap)
    ((cubicAdditiveMorphism 57 1 (by norm_num) (substitute p.val)
      (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)).hom.app
        (op Overlap)
      (normalOverlapSection 57 1 ambientNormalNumerator ambientNormalNumerator_homogeneous))

theorem surfaceCanonicalH1Equiv_boundary
    (z : (degreeOneSheaf 57 1).obj.obj (op Overlap)) :
    surfaceCanonicalH1Equiv
        (pushforwardBoundary immersion.base (curveClosedEmbedding 57 1)
          (degreeOneSheaf 57 1) (firstProjectivePatch 57 1)
          (secondProjectivePatch 57 1) Overlap (overlapProjectivePatch_eq 57 1)
          (projective_twoOpen_cover 57 1 (by norm_num)) z) =
      targetBoundary (cubicCanonicalMap.hom.app (op Overlap) z) :=
  pushforwardBoundary_map immersion.base (curveClosedEmbedding 57 1) cubicCanonicalMap
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num)) z

theorem cubicH1_boundary (p : WeightedCubic) :
    surfaceCanonicalH1Equiv
        (cubicH1OnSurface 57 1 (by norm_num) (substitute p.val)
          (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property)
          literalNormalClassOnSurface) =
      targetBoundary (cubicOverlapSection p) := by
  have h := pushforwardBoundary_map immersion.base (curveClosedEmbedding 57 1)
    (cubicAdditiveMorphism 57 1 (by norm_num) (substitute p.val)
      (CycleQ2GeometricLiteralSurface.substitute_homogeneous p.property))
    (firstProjectivePatch 57 1) (secondProjectivePatch 57 1) Overlap
    (overlapProjectivePatch_eq 57 1) (projective_twoOpen_cover 57 1 (by norm_num))
    (normalOverlapSection 57 1 ambientNormalNumerator ambientNormalNumerator_homogeneous)
  exact (congrArg surfaceCanonicalH1Equiv h).trans (surfaceCanonicalH1Equiv_boundary _)

/-- The source class includes the unchanged negative normalization of
the original reduced inverse-ideal class. -/
def originalCubicCurveClass (p : WeightedCubic) : CurveHOne :=
  -(sourceBoundary (cubicOverlapSection p))

/-- Every original cubic image lies in the concrete actual curve image.
No claim about arbitrary classes of pushed H¹ is needed. -/
theorem originalNormalClass_adjunction_factor (p : WeightedCubic) :
    surfaceAdjunctionH1 p literalNormalClassAtTop =
      pushforwardFromCurve (originalCubicCurveClass p) := by
  rw [originalNormalClass_adjunction_image, cubicH1_boundary, targetBoundary_factor]
  exact (map_neg pushforwardFromCurve _).symm

theorem canonicalConnectingOnCurve_cubic (p : WeightedCubic) :
    canonicalConnectingOnCurve (originalCubicCurveClass p) =
      canonicalOpenConnecting ⊤ (surfaceAdjunctionH1 p literalNormalClassAtTop) := by
  rw [canonicalConnectingOnCurve_apply, originalNormalClass_adjunction_factor]

end ActualCubicImages

/-- The old curve coordinate reconstructs every actual curve H¹ class. -/
theorem curveClass_eq_coordinate_smul (x : CurveHOne) :
    x = literalCanonicalCoordinate x • literalCanonicalNormalization :=
  (literalCanonicalNormalizationEquiv.apply_symm_apply x).symm

theorem canonicalConnectingOnCurve_formula (x : CurveHOne) :
    canonicalConnectingOnCurve x = literalCanonicalCoordinate x •
      canonicalConnectingOnCurve literalCanonicalNormalization := by
  conv_lhs => rw [curveClass_eq_coordinate_smul x]
  exact map_smul canonicalConnectingOnCurve _ _

/-- The fixed detector is in the same actual curve image, so the proved
nonzero connecting value gives nonzero on that image itself. -/
theorem canonicalConnectingOnCurve_ne_zero : canonicalConnectingOnCurve ≠ 0 := by
  intro h
  have hd := CycleQ2CanonicalResidueNonzero.canonicalResidueConnecting_value_ne_zero
  apply hd
  rw [← canonicalConnectingOnCurve_cubic, h, LinearMap.zero_apply]

theorem canonicalConnectingOnCurve_normalization_ne_zero :
    canonicalConnectingOnCurve literalCanonicalNormalization ≠ 0 := by
  intro h
  apply canonicalConnectingOnCurve_ne_zero
  ext x
  rw [canonicalConnectingOnCurve_formula, h, smul_zero, LinearMap.zero_apply]

/-- The connecting operation is injective on the actual one-dimensional
curve image. This does not claim injectivity on arbitrary pushed H¹. -/
theorem canonicalConnectingOnCurve_injective :
    Function.Injective canonicalConnectingOnCurve := by
  intro x y h
  apply literalCanonicalNormalizationEquiv.symm.injective
  apply smul_left_injective ℂ canonicalConnectingOnCurve_normalization_ne_zero
  exact (canonicalConnectingOnCurve_formula x).symm.trans
    (h.trans (canonicalConnectingOnCurve_formula y))

open CycleQ2GlobalCubicAdjunctionCohomology
  CycleQ2GeometricIntrinsicCartierCohomology

/-- The actual canonical residue boundary has exactly the expected
vanishing criterion on every original cubic image. -/
theorem canonicalOpenConnecting_original_cubic_zero_iff (p : WeightedCubic) :
    canonicalOpenConnecting ⊤ (surfaceAdjunctionH1 p literalNormalClassAtTop) = 0 ↔
      surfaceAdjunctionH1 p literalNormalClassAtTop = 0 := by
  rw [originalNormalClass_adjunction_factor]
  constructor
  · intro h
    have hx : originalCubicCurveClass p = 0 :=
      canonicalConnectingOnCurve_injective
        (h.trans canonicalConnectingOnCurve.map_zero.symm)
    rw [hx, map_zero]
  · intro h
    rw [h, map_zero]

/-- The fixed curve coordinate gives the same zero criterion, retaining
the explicit original cubic class and its negative boundary sign. -/
theorem canonicalOpenConnecting_original_cubic_coordinate_zero_iff (p : WeightedCubic) :
    canonicalOpenConnecting ⊤ (surfaceAdjunctionH1 p literalNormalClassAtTop) = 0 ↔
      literalCanonicalCoordinate (originalCubicCurveClass p) = 0 := by
  rw [canonicalOpenConnecting_original_cubic_zero_iff,
    originalNormalClass_adjunction_factor, literalCanonicalCoordinate_eq_zero_iff]
  constructor
  · intro h
    exact pushforwardFromCurve_injective (h.trans pushforwardFromCurve.map_zero.symm)
  · intro h
    rw [h, map_zero]

/-- The selected cubic and the detector are distinct. Injectivity on the
proved curve image transports the detector result to the original
selected cubic without identifying those polynomials. -/
theorem original_selected_cubic_connecting_ne_zero :
    canonicalOpenConnecting ⊤
      (surfaceAdjunctionH1 CycleQ2GluedCubicAdjunction.originalSelectedCubic
        literalNormalClassAtTop) ≠ 0 := by
  intro h
  exact originalNormalClass_selected_adjunction_ne_zero
    ((canonicalOpenConnecting_original_cubic_zero_iff _).mp h)

#print axioms pushed_scalarEnd
#print axioms targetBoundary_factor
#print axioms pushforwardFromCurve_injective
#print axioms originalNormalClass_adjunction_factor
#print axioms canonicalConnectingOnCurve_injective
#print axioms original_selected_cubic_connecting_ne_zero

end CycleQ2CanonicalCurveImage

end
