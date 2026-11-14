/-
SOURCE-ONLY DRAFT: unverified.
Compilation and independent kernel replay were deferred at the user's request.
The proof terms below have not been accepted as a checked certificate.
-/

import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricSurfaceResidueOverlap

/-!
# The original cubic sections in the actual local exterior frames

The frame coordinates below are the literal dehomogeneous polynomial
coefficients, with the fixed negative orientation on the second chart.
In particular X1³ and −X2³ give the actual first and second residue frame
generators. The already proved gluing of these original cubic sections
then determines the generator on every overlap without a new transition
choice.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceExteriorFrameBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
  CycleQ2GeometricAffineCurveCharts CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricAffineChartSections CycleQ2GeometricExteriorSheaf
  CycleQ2SurfaceResidueSheafOverlap CycleQ2SurfaceCubicGluing
  CycleQ2GeometricCanonicalGluing CycleQ2GeometricExteriorLocalFrames

variable (r θ : ℂ)

def firstExteriorFrame (i : Fin 2) (j : Fin 3) :
    LocalFrame (projectiveSurface r θ).sheaf (surfaceExteriorSheaf r θ)
      (firstNormalOpen r θ i j) :=
  chartResidueLocalFrame (projectiveToComplex r θ) (firstEquations r θ)
    (normalPolynomial (firstQuadric r) i) (includeCurve (X j))
    (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)

def secondExteriorFrame (i : Fin 2) (j : Fin 3) :
    LocalFrame (projectiveSurface r θ).sheaf (surfaceExteriorSheaf r θ)
      (secondNormalOpen r θ i j) :=
  chartResidueLocalFrame (projectiveToComplex r θ) (secondEquations r θ)
    (normalPolynomial (secondQuadric r) i) (includeCurve (X j))
    (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)

def exteriorFrame : (k : PatchIndex) →
    LocalFrame (projectiveSurface r θ).sheaf (surfaceExteriorSheaf r θ) (patchOpen r θ k)
  | .inl (i,j) => firstExteriorFrame r θ i j
  | .inr (i,j) => secondExteriorFrame r θ i j

theorem first_localSection_coordinate (p : CubicPolynomial) (i : Fin 2) (j : Fin 3)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ firstNormalOpen r θ i j) :
    frameCoordinate (firstExteriorFrame r θ i j) O hO
      (localSectionOn r θ p (.inl (i,j)) O hO) =
      chartSection (firstNormalChart r θ i j) (Over.mk (homOfLE hO))
        (algebraMap SurfacePoly (FirstNormalRing r θ i j) (firstSurfaceDehomogenize p)) := by
  change (firstExteriorFrame r θ i j).app O hO
    (chartSection (firstNormalChart r θ i j) (Over.mk (homOfLE hO))
      (algebraMap SurfacePoly (FirstNormalRing r θ i j) (firstSurfaceDehomogenize p)) •
      chartResidueSheafSection (projectiveToComplex r θ) (firstEquations r θ)
        (normalPolynomial (firstQuadric r) i) (includeCurve (X j))
        (firstNormalChart r θ i j) (firstNormalChart_overComplex r θ i j)
        (Over.mk (homOfLE hO))) = _
  rw [← chartResidueLocalFrame_generator]
  change (firstExteriorFrame r θ i j).app O hO
    (_ • ((firstExteriorFrame r θ i j).app O hO).symm 1) = _
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

theorem second_localSection_coordinate (p : CubicPolynomial) (i : Fin 2) (j : Fin 3)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ secondNormalOpen r θ i j) :
    frameCoordinate (secondExteriorFrame r θ i j) O hO
      (localSectionOn r θ p (.inr (i,j)) O hO) =
      -(chartSection (secondNormalChart r θ i j) (Over.mk (homOfLE hO))
        (algebraMap SurfacePoly (SecondNormalRing r θ i j) (secondSurfaceDehomogenize p))) := by
  change (secondExteriorFrame r θ i j).app O hO
    (-(chartSection (secondNormalChart r θ i j) (Over.mk (homOfLE hO))
      (algebraMap SurfacePoly (SecondNormalRing r θ i j) (secondSurfaceDehomogenize p)) •
      chartResidueSheafSection (projectiveToComplex r θ) (secondEquations r θ)
        (normalPolynomial (secondQuadric r) i) (includeCurve (X j))
        (secondNormalChart r θ i j) (secondNormalChart_overComplex r θ i j)
        (Over.mk (homOfLE hO)))) = _
  rw [map_neg, ← chartResidueLocalFrame_generator]
  change -((secondExteriorFrame r θ i j).app O hO
    (_ • ((secondExteriorFrame r θ i j).app O hO).symm 1)) = _
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

def firstFrameCubic : WeightedCubic :=
  ⟨X 1 ^ 3,
    (show (X (1 : Fin 5) : CubicPolynomial).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 from
        isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 1).pow 3⟩

def secondFrameCubic : WeightedCubic :=
  ⟨-(X 2 ^ 3),
    ((show (X (2 : Fin 5) : CubicPolynomial).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 from
        isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 2).pow 3).neg⟩

def frameCubic : PatchIndex → WeightedCubic
  | .inl _ => firstFrameCubic
  | .inr _ => secondFrameCubic

theorem first_frameCubic_generator (i : Fin 2) (j : Fin 3)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ firstNormalOpen r θ i j) :
    localSectionOn r θ firstFrameCubic.val (.inl (i,j)) O hO =
      frameGenerator (firstExteriorFrame r θ i j) O hO := by
  apply ((firstExteriorFrame r θ i j).app O hO).injective
  change frameCoordinate (firstExteriorFrame r θ i j) O hO
      (localSectionOn r θ firstFrameCubic.val (.inl (i,j)) O hO) =
    (firstExteriorFrame r θ i j).app O hO (((firstExteriorFrame r θ i j).app O hO).symm 1)
  rw [first_localSection_coordinate, LinearEquiv.apply_symm_apply]
  simp [firstFrameCubic, firstSurfaceDehomogenize]

theorem second_frameCubic_generator (i : Fin 2) (j : Fin 3)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ secondNormalOpen r θ i j) :
    localSectionOn r θ secondFrameCubic.val (.inr (i,j)) O hO =
      frameGenerator (secondExteriorFrame r θ i j) O hO := by
  apply ((secondExteriorFrame r θ i j).app O hO).injective
  change frameCoordinate (secondExteriorFrame r θ i j) O hO
      (localSectionOn r θ secondFrameCubic.val (.inr (i,j)) O hO) =
    (secondExteriorFrame r θ i j).app O hO (((secondExteriorFrame r θ i j).app O hO).symm 1)
  rw [second_localSection_coordinate, LinearEquiv.apply_symm_apply]
  simp [secondFrameCubic, secondSurfaceDehomogenize]

theorem frameCubic_generator (k : PatchIndex)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ patchOpen r θ k) :
    localSectionOn r θ (frameCubic k).val k O hO =
      frameGenerator (exteriorFrame r θ k) O hO := by
  rcases k with ⟨i,j⟩ | ⟨i,j⟩
  · exact first_frameCubic_generator r θ i j O hO
  · exact second_frameCubic_generator r θ i j O hO

/-- On any overlap, the second frame's genuine generator is the local
section of its original cubic computed in the first chart. -/
theorem generator_eq_original_cubic_on_overlap (k l : PatchIndex)
    (O : (projectiveSurface r θ).Opens)
    (hk : O ≤ patchOpen r θ k) (hl : O ≤ patchOpen r θ l) :
    frameGenerator (exteriorFrame r θ l) O hl =
      localSectionOn r θ (frameCubic l).val k O hk :=
  (frameCubic_generator r θ l O hl).symm.trans
    (localSectionOn_pairwise r θ (frameCubic l).val (frameCubic l).property l k O hl hk)

#print axioms first_localSection_coordinate
#print axioms second_localSection_coordinate
#print axioms frameCubic_generator
#print axioms generator_eq_original_cubic_on_overlap

end CycleQ2SurfaceExteriorFrameBinding

end
