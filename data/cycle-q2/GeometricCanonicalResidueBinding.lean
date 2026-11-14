import Proposal.GeometricCanonicalResidue
import Proposal.GeometricGradedCechDescent
import Proposal.GeometricSurfaceDifferentialCharts

/-!
# The chart residue uses the original Cartier reduction map

Status: source-only proof draft; compilation and independent kernel replay
are deferred at the user's request. Its raw-residue prerequisite was
corrected after an earlier failed elaboration and remains unverified.
No new axioms or admissions are used.

The affine comparison below identifies the existing sheaf morphism
`inverseIdealReduction` with reduction of the original coordinate-algebra
functional.  The resulting square uses actual inverse-ideal sheaf sections,
the original surface-to-curve morphism, and the exterior restriction of an
arbitrary two-form.  The two final definitions specialize it to the first
and second literal normal-chart families at `(r, θ) = (57, 1)`.

The nonconstructive geometric strategy is due to Ben Diamond and the cited
work of Claire Voisin.  Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalRawResidueBinding

open CategoryTheory Opposite AlgebraicGeometry Module
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2ProjectiveInverseIdeal CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricAffineCurveCharts CycleQ2CanonicalRawResidue
open scoped TensorProduct

section AffineReduction

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The actual Cartier sheaf reduction has the original coordinate-algebra
map as its affine expression, on every inverse-ideal section. -/
theorem affine_reduction
    (s : (inverseIdealSheaf (Spec.map φ)).val.obj (op ⊤)) :
    letI : Algebra A B := φ.hom.toAlgebra
    affineNormalAlgebraEquiv φ
        ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤) s) =
      (Algebra.linearMap A B).comp (affineInverseIdealAlgebraEquiv φ s) := by
  letI : Algebra A B := φ.hom.toAlgebra
  apply LinearMap.ext
  intro a
  change specTopRingEquiv B
      (normalSectionEvaluate (Spec.map φ) ⊤
        ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤) s)
        ((affineKernelSectionSemilinearEquiv φ).symm a)) =
    φ (specTopRingEquiv A
      (inverseIdealSectionEvaluate (Spec.map φ) ⊤ s
        ((affineKernelSectionSemilinearEquiv φ).symm a)))
  rw [inverseIdealReduction_evaluate, affineSectionMap_normalization]

/-- The same comparison retains the actual conormal quotient and scalar
extension, exactly the normalization used by the raw residue map. -/
theorem affine_conormal_reduction
    (s : (inverseIdealSheaf (Spec.map φ)).val.obj (op ⊤)) :
    letI : Algebra A B := φ.hom.toAlgebra
    affineNormalAlgebraConormalEquiv φ
        ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤) s) =
      normalFunctionalEquiv (RingHom.ker φ.hom) (fun _ ha => ha)
        ((Algebra.linearMap A B).comp (affineInverseIdealAlgebraEquiv φ s)) := by
  letI : Algebra A B := φ.hom.toAlgebra
  change normalFunctionalEquiv (RingHom.ker φ.hom) (fun _ ha => ha)
    (affineNormalAlgebraEquiv φ
      ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤) s)) = _
  rw [affine_reduction]

end AffineReduction

section NormalChart

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

/-- The ring map of the existing surface/curve Jacobian chart. -/
abbrev chartMap : CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j) ⟶
    CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j) :=
  CommRingCat.ofHom (normalChartMap q h g₁ g₂ k i j).toRingHom

/-- The second square of the canonical residue diagram on the actual
affine chart, with the original Cartier sheaf reduction as its upper map. -/
theorem chart_residue_sequence_square
    (s : (inverseIdealSheaf (Spec.map (chartMap q h g₁ g₂ k i j))).val.obj (op ⊤))
    (ω : SurfaceForms q h g₁ g₂ k i j) :
    residue q h g₁ g₂ k i j
        ((affineInverseIdealAlgebraEquiv (chartMap q h g₁ g₂ k i j) s).smulRight ω) =
      normalAdjunction q h g₁ g₂ k i j
        (affineNormalAlgebraConormalEquiv (chartMap q h g₁ g₂ k i j)
          ((inverseIdealReduction (Spec.map (chartMap q h g₁ g₂ k i j))).val.app
            (op ⊤) s))
        (restrictForm q h g₁ g₂ k i j ω) := by
  rw [residue_smulRight, affine_conormal_reduction]
  rfl

end NormalChart

section LiteralCharts

open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricSurfacePrincipalCurveCharts
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSeedNormalIdeals
  CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting

/-- The actual residue on the first literal normal-chart family. -/
def firstResidue (i : Fin 2) (j : Fin 3) :
    (RingHom.ker (firstNormalCurveMap 57 1 i j).toRingHom →ₗ[FirstNormalRing 57 1 i j]
      (⋀[FirstNormalRing 57 1 i j]^2
        (KaehlerDifferential ℂ (FirstNormalRing 57 1 i j)))) →ₛₗ[
      (firstNormalCurveMap 57 1 i j).toRingHom]
        KaehlerDifferential ℂ (FirstNormalCurveRing 57 1 i j) :=
  residue (firstQuadric 57) (firstCubic 1)
    (firstSurfaceDehomogenize (originalG1 57)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK 1)) i j

/-- The actual residue on the second literal normal-chart family. -/
def secondResidue (i : Fin 2) (j : Fin 3) :
    (RingHom.ker (secondNormalCurveMap 57 1 i j).toRingHom →ₗ[SecondNormalRing 57 1 i j]
      (⋀[SecondNormalRing 57 1 i j]^2
        (KaehlerDifferential ℂ (SecondNormalRing 57 1 i j)))) →ₛₗ[
      (secondNormalCurveMap 57 1 i j).toRingHom]
        KaehlerDifferential ℂ (SecondNormalCurveRing 57 1 i j) :=
  residue (secondQuadric 57) (secondCubic 1)
    (secondSurfaceDehomogenize (originalG1 57)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK 1)) i j

theorem first_residue_sequence_square (i : Fin 2) (j : Fin 3)
    (s : (inverseIdealSheaf
      (Spec.map (CommRingCat.ofHom (firstNormalCurveMap 57 1 i j).toRingHom))).val.obj
        (op ⊤))
    (ω : ⋀[FirstNormalRing 57 1 i j]^2
      (KaehlerDifferential ℂ (FirstNormalRing 57 1 i j))) :
    firstResidue i j
        ((affineInverseIdealAlgebraEquiv
          (CommRingCat.ofHom (firstNormalCurveMap 57 1 i j).toRingHom) s).smulRight ω) =
      normalAdjunction (firstQuadric 57) (firstCubic 1)
        (firstSurfaceDehomogenize (originalG1 57)) (firstSurfaceDehomogenize originalG2)
        (firstSurfaceDehomogenize (thetaK 1)) i j
        (affineNormalAlgebraConormalEquiv
          (CommRingCat.ofHom (firstNormalCurveMap 57 1 i j).toRingHom)
          ((inverseIdealReduction
            (Spec.map (CommRingCat.ofHom (firstNormalCurveMap 57 1 i j).toRingHom))).val.app
              (op ⊤) s))
        (restrictForm (firstQuadric 57) (firstCubic 1)
          (firstSurfaceDehomogenize (originalG1 57)) (firstSurfaceDehomogenize originalG2)
          (firstSurfaceDehomogenize (thetaK 1)) i j ω) :=
  chart_residue_sequence_square (firstQuadric 57) (firstCubic 1)
    (firstSurfaceDehomogenize (originalG1 57)) (firstSurfaceDehomogenize originalG2)
    (firstSurfaceDehomogenize (thetaK 1)) i j s ω

theorem second_residue_sequence_square (i : Fin 2) (j : Fin 3)
    (s : (inverseIdealSheaf
      (Spec.map (CommRingCat.ofHom (secondNormalCurveMap 57 1 i j).toRingHom))).val.obj
        (op ⊤))
    (ω : ⋀[SecondNormalRing 57 1 i j]^2
      (KaehlerDifferential ℂ (SecondNormalRing 57 1 i j))) :
    secondResidue i j
        ((affineInverseIdealAlgebraEquiv
          (CommRingCat.ofHom (secondNormalCurveMap 57 1 i j).toRingHom) s).smulRight ω) =
      normalAdjunction (secondQuadric 57) (secondCubic 1)
        (secondSurfaceDehomogenize (originalG1 57)) (secondSurfaceDehomogenize originalG2)
        (secondSurfaceDehomogenize (thetaK 1)) i j
        (affineNormalAlgebraConormalEquiv
          (CommRingCat.ofHom (secondNormalCurveMap 57 1 i j).toRingHom)
          ((inverseIdealReduction
            (Spec.map (CommRingCat.ofHom (secondNormalCurveMap 57 1 i j).toRingHom))).val.app
              (op ⊤) s))
        (restrictForm (secondQuadric 57) (secondCubic 1)
          (secondSurfaceDehomogenize (originalG1 57)) (secondSurfaceDehomogenize originalG2)
          (secondSurfaceDehomogenize (thetaK 1)) i j ω) :=
  chart_residue_sequence_square (secondQuadric 57) (secondCubic 1)
    (secondSurfaceDehomogenize (originalG1 57)) (secondSurfaceDehomogenize originalG2)
    (secondSurfaceDehomogenize (thetaK 1)) i j s ω

end LiteralCharts

#print axioms affine_conormal_reduction
#print axioms chart_residue_sequence_square
#print axioms first_residue_sequence_square
#print axioms second_residue_sequence_square

end CycleQ2CanonicalRawResidueBinding

end
