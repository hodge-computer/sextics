import Proposal.GeometricIncidenceFirstOrderCohomology
import Proposal.GeometricProjectiveNormalClass
import Proposal.GeometricCartierNormalBinding

/-!
# The retained incidence tangent pairs with the existing normal-frame class

For every cubic coefficient vector, the existing paired projective class
is the image of the literal class in the constructed normal-frame sheaf
under the actual cubic cohomology map. The proof uses the already proved
Mayer--Vietoris naturality formula and the unchanged degree-nine numerator.
The original ambient test restricts with a minus sign, so its negative
is exactly the positive numerator of the retained normal-frame class.

Specialization uses the same firstOrderCubicDirection as the retained
seed/time-derivation path. Transport through the existing canonical-sheaf
isomorphism identifies its cubic image with firstOrderDifferentialClass
and transfers the existing nonvanishing result. The existing intrinsic
normal-sheaf comparison then proves nonvanishing of the same cubic image
of the original intrinsic class and its oppositely normalized Cartier
lift. The surface-side target remains the original pushed degree-one
sheaf cohomology, with the existing comparison to curve cohomology.
The comparison with the moving section curve's Abel--Jacobi class, and
the protected residue-exactness conclusion, remain separate obligations.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFirstOrderNormalPairing

open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricLiteralCanonicalClass CycleQ2GeometricLiteralDirection
  CycleQ2IncidenceFirstOrderTrace CycleQ2IncidenceFirstOrderCohomology
  CycleQ2SurfaceNormalTransport CycleQ2IntrinsicNormalModel
  CycleQ2IntrinsicSurfaceNormalCohomology

/-- The original weighted test is restricted by w = -x2^2. Its negative,
not its positive restriction, is the retained normal-frame numerator. -/
theorem ambientNormalNumerator_eq_neg_derivativeRestriction :
    ambientNormalNumerator = -(substitute CycleQ2NormalConnecting.derivativeA) := by
  change ambientNormalNumerator = -(substitute ambientTest)
  simp only [ambientNormalNumerator, substitute_ambientTest, neg_neg]

/-- The paired numerator is literally multiplication of the retained
normal-frame numerator by the supplied cubic. -/
theorem pairedNumerator_eq_normalProduct (v : Fin 9 → ℂ) :
    -derivativeNumerator (cubicDeformation v) =
      ambientNormalNumerator * cubicDeformation v := by
  simp only [derivativeNumerator, ambientNormalNumerator, neg_mul, neg_neg]

/-- This is equality in the existing actual projective H1 group, for
every cubic coefficient vector; no nonvanishing premise is used. -/
theorem pairedProjectiveClass_eq_cubicNormal (v : Fin 9 → ℂ) :
    degreeOneToProjectiveH1 57 1 (by norm_num)
      (pairedDegreeOneClass 57 1 v) =
    cubicH1Map 57 1 (by norm_num)
      (cubicDeformation v) (cubicDeformation_homogeneous v)
      CycleQ2GeometricProjectiveNormalClass.literalNormalClass := by
  rw [CycleQ2GeometricProjectiveNormalClass.literalNormalClass,
    cubicH1Map_normalClass]
  change
    degreeOneConnecting 57 1 (by norm_num)
      (degreeNineRepresentative 57 1
        (-derivativeNumerator (cubicDeformation v)) _) =
    degreeOneConnecting 57 1 (by norm_num)
      (degreeNineRepresentative 57 1
        (ambientNormalNumerator * cubicDeformation v) _)
  congr 2
  exact pairedNumerator_eq_normalProduct v

/-- Specialization to the original pointed incidence tangent. -/
theorem firstOrderProjectiveClass_eq_cubicNormal :
    firstOrderProjectiveClass =
    cubicH1Map 57 1 (by norm_num)
      (cubicDeformation firstOrderCubicDirection)
      (cubicDeformation_homogeneous firstOrderCubicDirection)
      CycleQ2GeometricProjectiveNormalClass.literalNormalClass := by
  simpa only [firstOrderProjectiveClass] using
    pairedProjectiveClass_eq_cubicNormal firstOrderCubicDirection

/-- The existing canonical-sheaf comparison sends this same cubic
image to the original first-order differential-cohomology class. -/
theorem firstOrderDifferentialClass_eq_cubicNormal :
    firstOrderDifferentialClass =
    literalCanonicalH1Equiv
      (cubicH1Map 57 1 (by norm_num)
        (cubicDeformation firstOrderCubicDirection)
        (cubicDeformation_homogeneous firstOrderCubicDirection)
        CycleQ2GeometricProjectiveNormalClass.literalNormalClass) := by
  simpa only [firstOrderDifferentialClass] using
    congrArg literalCanonicalH1Equiv firstOrderProjectiveClass_eq_cubicNormal

theorem firstOrder_cubicNormal_ne_zero :
    cubicH1Map 57 1 (by norm_num)
      (cubicDeformation firstOrderCubicDirection)
      (cubicDeformation_homogeneous firstOrderCubicDirection)
      CycleQ2GeometricProjectiveNormalClass.literalNormalClass ≠ 0 := by
  rw [← firstOrderProjectiveClass_eq_cubicNormal]
  exact firstOrderProjectiveClass_ne_zero

theorem firstOrder_canonicalCubicNormal_ne_zero :
    literalCanonicalH1Equiv
      (cubicH1Map 57 1 (by norm_num)
        (cubicDeformation firstOrderCubicDirection)
        (cubicDeformation_homogeneous firstOrderCubicDirection)
        CycleQ2GeometricProjectiveNormalClass.literalNormalClass) ≠ 0 := by
  rw [← firstOrderDifferentialClass_eq_cubicNormal]
  exact firstOrderDifferentialClass_ne_zero

/-- The proved intrinsic normal-sheaf comparison and curve-to-surface
cohomology comparison preserve nonvanishing for this same actual cubic. -/
theorem firstOrder_intrinsicCubic_ne_zero :
    literalIntrinsicCubicH1Map
      (cubicDeformation firstOrderCubicDirection)
      (cubicDeformation_homogeneous firstOrderCubicDirection)
      literalIntrinsicNormalClass ≠ 0 := by
  intro h
  apply firstOrder_cubicNormal_ne_zero
  exact (intrinsicCubicH1Map_class_zero_iff
    57 1 intrinsicNormalIso (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous
    (cubicDeformation firstOrderCubicDirection)
    (cubicDeformation_homogeneous firstOrderCubicDirection)).mp h

/-- The original Cartier lift uses the opposite fixed Cech sign; its
cubic image is nonzero for the retained incidence tangent as well. -/
theorem firstOrder_CartierNormal_cubic_ne_zero :
    literalIntrinsicCubicH1Map
      (cubicDeformation firstOrderCubicDirection)
      (cubicDeformation_homogeneous firstOrderCubicDirection)
      CycleQ2GeometricIntrinsicCartierCohomology.literalNormalClassAtTop ≠ 0 := by
  rw [CycleQ2GeometricIntrinsicCartierCohomology.literalNormalClassAtTop_eq_negative_original,
    map_neg]
  exact neg_ne_zero.mpr firstOrder_intrinsicCubic_ne_zero

#print axioms pairedProjectiveClass_eq_cubicNormal
#print axioms firstOrderDifferentialClass_eq_cubicNormal
#print axioms firstOrder_cubicNormal_ne_zero
#print axioms firstOrder_canonicalCubicNormal_ne_zero
#print axioms firstOrder_intrinsicCubic_ne_zero
#print axioms firstOrder_CartierNormal_cubic_ne_zero

end CycleQ2IncidenceFirstOrderNormalPairing
end
