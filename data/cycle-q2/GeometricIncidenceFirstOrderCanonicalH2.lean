import Proposal.GeometricIncidenceFirstOrderNormalPairing
import Proposal.GeometricCanonicalCurveImage

/-!
# The retained original incidence tangent has nonzero canonical H² image

The cubic below is the cubic component of the existing firstOrderDirection,
with its original full invariant coefficient indexing. Restriction to the
literal curve gives exactly the previously retained nine-column cubic.
The existing intrinsic cubic nonvanishing and the proved injectivity of
the actual canonical residue boundary on the curve image therefore give
nonvanishing in the canonical H² of the same literal surface (57, 1).

The public endpoint keeps literalDerivedClassAtTop, the original Cartier
boundary of the original ambient-test normal class, with its existing sign.
No Serre trace, new tangent, or geometric comparison hypothesis is supplied.
This is the original tangent's canonical boundary. It does not identify
that class with the moving section curve's Chern or Abel--Jacobi class,
construct a supported correspondence, or prove protected residue exactness.

Source-only proof draft: no Lean elaboration, compilation, or kernel replay
has been run. Prepared for fqlx with OpenAI ChatGPT assistance; the geometric
strategy and attribution are recorded in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceFirstOrderCanonicalH2

open CategoryTheory TopologicalSpace MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj
  CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2IncidenceFirstOrderTrace CycleQ2IncidenceFirstOrderNormalPairing
  CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2GlobalCubicAdjunctionCohomology CycleQ2CanonicalResidueDiagram
  CycleQ2CanonicalCubicDiagram CycleQ2CanonicalCurveImage

local instance surfaceHasExt :
    HasExt.{1} (Sheaf
      (Opens.grothendieckTopology CycleQ2CanonicalResidueSheaf.Surface)
      AddCommGrpCat.{0}) := HasExt.standard _

/-- The unchanged cubic component of the actual retained incidence tangent.
Its degree is proved from its existing full invariant grading. -/
def firstOrderWeightedCubic : CycleQ2SurfaceCubicGluing.WeightedCubic :=
  ⟨fullInvariantPolynomial 3 (fun j => firstOrderDirection (Sum.inl j)),
    homogeneous_of_character
      (fullInvariantPolynomial_homogeneous 3
        (fun j => firstOrderDirection (Sum.inl j)))⟩

/-- Restriction uses the original checked cubic-column order and exactly
the same firstOrderDirection, with no scalar renormalization. -/
theorem firstOrderWeightedCubic_substitute :
    substitute firstOrderWeightedCubic.val =
      cubicDeformation firstOrderCubicDirection := by
  simpa only [firstOrderWeightedCubic, firstOrderCubicDirection] using
    CycleQ2IncidenceCubicCechTrace.substitute_cubic
      (fun j => firstOrderDirection (Sum.inl j))

/-- The actual surface adjunction preserves the already proved nonzero
intrinsic cubic image of the original Cartier-normal class. -/
theorem firstOrder_surfaceAdjunction_ne_zero :
    surfaceAdjunctionH1 firstOrderWeightedCubic literalNormalClassAtTop ≠ 0 := by
  rw [surfaceAdjunctionH1_factor]
  intro hzero
  have h := surfaceCanonicalH1Equiv.injective
    (hzero.trans surfaceCanonicalH1Equiv.map_zero.symm)
  apply firstOrder_CartierNormal_cubic_ne_zero
  simpa only [firstOrderWeightedCubic_substitute] using h

/-- Injectivity on the actual curve image, already proved using the
fixed canonical residue diagram, gives nonzero surface canonical boundary.
There is no additional trace or nonvanishing premise. -/
theorem firstOrder_canonicalConnecting_ne_zero :
    canonicalOpenConnecting ⊤
      (surfaceAdjunctionH1 firstOrderWeightedCubic literalNormalClassAtTop) ≠ 0 := by
  intro hzero
  exact firstOrder_surfaceAdjunction_ne_zero
    ((canonicalOpenConnecting_original_cubic_zero_iff firstOrderWeightedCubic).mp hzero)

/-- CLOSED SOURCE-LEVEL ENDPOINT: the original retained tangent's actual
global cubic form has nonzero product with the original literal Cartier
H² class on the unchanged surface (57, 1), with the original boundary sign.
This is not an Abel--Jacobi comparison for the moving section curve. -/
theorem firstOrder_canonicalH2_ne_zero :
    cubicH2 firstOrderWeightedCubic
      CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop ≠ 0 := by
  rw [← originalClass_cubic_connecting]
  exact firstOrder_canonicalConnecting_ne_zero

end CycleQ2IncidenceFirstOrderCanonicalH2

end

#print axioms CycleQ2IncidenceFirstOrderCanonicalH2.firstOrderWeightedCubic_substitute
#print axioms CycleQ2IncidenceFirstOrderCanonicalH2.firstOrder_surfaceAdjunction_ne_zero
#print axioms CycleQ2IncidenceFirstOrderCanonicalH2.firstOrder_canonicalConnecting_ne_zero
#print axioms CycleQ2IncidenceFirstOrderCanonicalH2.firstOrder_canonicalH2_ne_zero
