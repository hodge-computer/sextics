import Proposal.GeometricHodgeThreefoldIncidence
import Proposal.GeometricLiteralAmbientCylinder
import Proposal.GeometricLiteralAmbientCharts

/-!
# The four moving-family charts at the fixed incidence fiber

The specialization at the original incidence point has invertible cubic
leading coefficient. Composing the homogeneous-ideal identification and
the native projective fiber isomorphism identifies its four degree-one
opens with those used in the fixed-fiber residue calculations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefoldIncidence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2LiteralAmbientCylinder
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2SeedCubicFamily
  CycleQ2SeedProjectiveFamily CycleQ2IncidenceFamilyContainment CycleQ2IncidenceEquations
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceNormalForm

abbrev literalEval := sexticEval point

theorem literal_vertex_unit : IsUnit (literalEval vertexCoefficient) := by
  change IsUnit (aeval (pointSextic point) (X fullSexticLeadingIndex))
  rw [aeval_X]
  exact seedSexticCoefficients_unit 57 Complex.I

def literalIso : threefold literalEval ≅ IncidenceFiber 57 := nativeIso point ≪≫ nativeToIncidence

theorem literalIso_overComplex :
    literalIso.hom ≫ incidenceFiberToComplex 57 = toBase literalEval := by
  rw [literalIso, Iso.trans_hom, Category.assoc, nativeToIncidence_overComplex, nativeIso_overBase]

theorem literal_smoothDimension : SmoothOfRelativeDimension 3 (toBase literalEval) := by
  rw [← literalIso_overComplex]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 3)
    literalIso.hom (incidenceFiberToComplex 57)).mpr literal_fiber_smooth

theorem nativeToIncidence_preimage (i : Fin 4) :
    nativeToIncidence.hom ⁻¹ᵁ fixedOpen i = nativeOpen point i := by
  change (nativeToIncidence.hom ≫ pullback.snd incidenceParameter (familyToParameters 57))
    ⁻¹ᵁ CycleQ2SeedFamilyChart.coordinateOpen 57 i = _
  rw [nativeToIncidence_snd]
  unfold CycleQ2SeedFamilyChart.coordinateOpen CycleQ2LiteralAmbientProjFiber.projective
  rw [Proj.map_preimage_basicOpen]
  change Proj.basicOpen (sexticGrade point) (Ideal.Quotient.mk (sexticIdeal point)
    (MvPolynomial.map cubicEval (X i.castSucc))) = _
  rw [MvPolynomial.map_X] <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem literalIso_preimage (i : Fin 4) :
    literalIso.hom ⁻¹ᵁ fixedOpen i = coordinateOpen literalEval i := by
  rw [literalIso, Iso.trans_hom, Scheme.Hom.comp_preimage, nativeToIncidence_preimage, nativeIso_preimage]

end CycleQ2GeometricHodgeThreefoldIncidence
end

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.literalIso_preimage
#print axioms CycleQ2GeometricHodgeThreefoldIncidence.literal_vertex_unit
