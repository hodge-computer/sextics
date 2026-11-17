import Proposal.GeometricThreeOpenH2Naturality
import Proposal.GeometricGlobalSurfaceCubics
import Proposal.GeometricCanonicalResidueDiagram

/-!
# The canonical residue diagram for the actual global cubic forms

The global forms are constructed over the full surface cover,
and their unchanged normal-neighborhood restrictions discharge the local
identification hypothesis in the general residue diagram. The statements
below therefore have no global-cubic extension premise.

Nonvanishing of the image under the canonical connecting map is not
asserted here; the coordinate/cohomology trace comparison is a further
requirement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalCubicDiagram

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricIntrinsicCartierSequence CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2CanonicalResidueSheaf CycleQ2CanonicalResidueDiagram
  CycleQ2GlobalCubicAdjunctionCohomology

abbrev WeightedCubic := CycleQ2SurfaceCubicGluing.WeightedCubic

local instance sheafHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology
      (show TopCat from CycleQ2CanonicalResidueSheaf.Surface)) AddCommGrpCat.{0}) :=
  CycleQ2CoordinateTopDescent.coordinateSurfaceHasExt 57 1

theorem globalCubic_restrict (p : WeightedCubic) (a : PatchIndex)
    (O : CycleQ2CanonicalResidueSheaf.Surface.Opens) (hO : O ≤ refinedPatch a) :
    formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p) O =
      CycleQ2SurfaceCubicGluing.localSectionOn 57 1 p.val a O
        (hO.trans (refinedPatch_le a)) :=
  CycleQ2GlobalSurfaceCubics.globalCubicSection_restrict_original p a O
    (hO.trans (refinedPatch_le a))

/-- The global-form construction gives exactly the original cubic contraction. -/
theorem globalCubic_normalContraction (p : WeightedCubic) :
    normalContractionOfGlobal (CycleQ2GlobalSurfaceCubics.globalCubicSection p) =
      normalContraction p :=
  normalContractionOfGlobal_eq_cubic
    (CycleQ2GlobalSurfaceCubics.globalCubicSection p) p (globalCubic_restrict p)

def cubicDiagram (p : WeightedCubic) :
    literalInverseIdealComplex (57 : ℂ) 1 ⟶ canonicalResidueComplex :=
  globalFormDiagram (CycleQ2GlobalSurfaceCubics.globalCubicSection p)

theorem cubicDiagram_right (p : WeightedCubic) :
    (cubicDiagram p).τ₃ = normalContraction p := globalCubic_normalContraction p

def cubicH2 (p : WeightedCubic) :
    (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf
      CycleQ2CanonicalResidueSheaf.Surface).H' 2 ⊤ →+
      canonicalResidueAdditiveComplex.X₁.H' 2 ⊤ :=
  CycleQ2ThreeOpenH2Naturality.cohomologyMap
    (globalFormAdditiveDiagram (CycleQ2GlobalSurfaceCubics.globalCubicSection p)).τ₁ 2 ⊤

/-- The actual cubic connecting identity for the original reduced normal
class and its original Cartier boundary, with the established sign. -/
theorem originalClass_cubic_connecting (p : WeightedCubic) :
    canonicalOpenConnecting ⊤ (surfaceAdjunctionH1 p literalNormalClassAtTop) =
      cubicH2 p CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop :=
  cubic_originalClass_connecting
    (CycleQ2GlobalSurfaceCubics.globalCubicSection p) p (globalCubic_restrict p)

/-- The fixed detector cubic has nonzero normal-class image when viewed
through the actual global two-form, with no extension premise. -/
theorem selected_globalForm_contraction_ne_zero :
    formContractionH1
        (CycleQ2GlobalSurfaceCubics.globalCubicSection
          CycleQ2GluedCubicAdjunction.originalSelectedCubic)
        ⊤ literalNormalClassAtTop ≠ 0 := by
  rw [formContractionH1_eq_cubic
    (CycleQ2GlobalSurfaceCubics.globalCubicSection
      CycleQ2GluedCubicAdjunction.originalSelectedCubic)
    CycleQ2GluedCubicAdjunction.originalSelectedCubic
    (globalCubic_restrict CycleQ2GluedCubicAdjunction.originalSelectedCubic)]
  exact originalNormalClass_selected_adjunction_ne_zero

#print axioms globalCubic_normalContraction
#print axioms cubicDiagram
#print axioms originalClass_cubic_connecting
#print axioms selected_globalForm_contraction_ne_zero

end CycleQ2CanonicalCubicDiagram

end
