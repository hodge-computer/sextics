import Proposal.GeometricLiteralCanonicalProjectionFrame
import Proposal.GeometricLiteralResidueMonomial
import Proposal.GeometricLiteralCanonicalTraceLinearity
import Proposal.GeometricCanonicalResidueNonzero

/-!
# The normalized canonical residue generator

The fraction `x₀² w² / (x₁ x₂ x₃)` has degree three on the triple
intersection. Its actual canonical section has Laurent residue one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalResidueGenerator

open CategoryTheory Opposite MvPolynomial AlgebraicGeometry
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCoordinateCharacter CycleQ2CartierSurfaceGrading
  CycleQ2GradedLocalizationProjection CycleQ2LiteralCanonicalDegreeProjection
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2CanonicalCoordinateCoefficients CycleQ2CanonicalResidueNonzero

/-- The standard Laurent monomial on the literal surface. -/
def residueFraction : CoordinateLocal 57 1 Finset.univ :=
  polynomialFraction 57 1 ((X 0)^2 * (X 4)^2)

private theorem residueFraction_degreeThree :
    degreeThree Finset.univ (by simp) residueFraction = residueFraction := by
  let p : MvPolynomial (Fin 5) ℂ := (X 0)^2 * (X 4)^2
  have h0 : (X (0 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 :=
    isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 0
  have h4 : (X (4 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 2 :=
    isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 4
  have hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 6 :=
    (h0.pow 2).mul (h4.pow 2)
  let f := coordinateProduct 57 1 Finset.univ
  change degreePlus _ _ _ (fraction f 1 (quotientMap 57 1 p)) = _
  rw [degreePlus_fraction]
  change fraction f 1 (GradedRing.proj (surfaceGrade 57 1) 6 (quotientMap 57 1 p)) =
    fraction f 1 (quotientMap 57 1 p)
  congr 1
  exact DirectSum.decompose_of_mem_same _ (surfaceQuotient_mem_grade 57 1 hp)

theorem residueFraction_mem_range : residueFraction ∈ canonicalCoefficient.range := by
  have hr := degreeThree_mem_range Finset.univ (by simp) residueFraction
  rw [residueFraction_degreeThree] at hr
  suffices ∀ (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 Finset.univ),
    residueFraction ∈ (canonicalCoefficientAt Finset.univ (by simp) O hO).range from
    this TripleOpen (coordinateIntersection_univ 57 1).symm
  rintro O rfl
  exact hr

/-- A canonical section with the prescribed explicit Laurent coefficient. -/
def canonicalResidueGenerator : CanonicalSheaf.obj.obj (op TripleOpen) :=
  Classical.choose residueFraction_mem_range

theorem canonicalCoefficient_residueGenerator :
    canonicalCoefficient canonicalResidueGenerator = residueFraction :=
  Classical.choose_spec residueFraction_mem_range

theorem eq_residueGenerator_of_coefficient (s : CanonicalSheaf.obj.obj (op TripleOpen))
    (hs : canonicalCoefficient s = residueFraction) : s = canonicalResidueGenerator :=
  CycleQ2LiteralCanonicalCoefficientRange.canonicalCoefficientAt_injective Finset.univ (by simp)
    TripleOpen (coordinateIntersection_univ 57 1).symm
    (hs.trans canonicalCoefficient_residueGenerator.symm)

/-- The distinguished Laurent residue of the canonical generator is exactly one. -/
theorem canonicalSectionTrace_residueGenerator :
    canonicalSectionTrace canonicalResidueGenerator = 1 := by
  change CycleQ2CoordinateCechTrace.localCoefficient 57 Finset.univ (2,2) (fun _ => -1)
    (canonicalCoefficient canonicalResidueGenerator) = 1
  rw [canonicalCoefficient_residueGenerator]
  exact CycleQ2LiteralResidueMonomial.residueFraction_trace

theorem canonicalConnecting_residueGenerator_ne_zero :
    CycleQ2CanonicalCoordinateH2.canonicalConnecting canonicalResidueGenerator ≠ 0 := by
  intro hz
  have h := canonicalSectionTrace_zero_of_connecting_zero canonicalResidueGenerator hz
  rw [canonicalSectionTrace_residueGenerator] at h
  exact one_ne_zero h

/-- Multiples of the normalized generator realize every complex residue. -/
theorem canonicalCechTrace_surjective : Function.Surjective canonicalCechTrace := by
  intro c
  let s := CycleQ2LiteralCanonicalTraceLinearity.sectionScalar c canonicalResidueGenerator
  refine ⟨QuotientAddGroup.mk s, ?_⟩
  change canonicalSectionTrace
    (CycleQ2LiteralCanonicalTraceLinearity.sectionScalar c canonicalResidueGenerator) = c
  rw [CycleQ2LiteralCanonicalTraceLinearity.canonicalSectionTrace_smul,
    canonicalSectionTrace_residueGenerator, smul_eq_mul, mul_one]

end CycleQ2LiteralCanonicalResidueGenerator

end

#print axioms CycleQ2LiteralCanonicalResidueGenerator.canonicalCoefficient_residueGenerator
#print axioms CycleQ2LiteralCanonicalResidueGenerator.eq_residueGenerator_of_coefficient
#print axioms CycleQ2LiteralCanonicalResidueGenerator.canonicalSectionTrace_residueGenerator
#print axioms CycleQ2LiteralCanonicalResidueGenerator.canonicalConnecting_residueGenerator_ne_zero
#print axioms CycleQ2LiteralCanonicalResidueGenerator.canonicalCechTrace_surjective
