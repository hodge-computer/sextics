import Proposal.GeometricLiteralNativeCotangent
import Proposal.GeometricLiteralProjectiveDualFamily
import Proposal.GeometricSurfaceNormalCharts

/-!
# The canonical restricted cotangent sheaf of the original deformation

The total differential sheaf is formed from the actual complex structure
of the original Proj deformation. Its genuine scheme-module pullback to
the original closed surface is the restricted cotangent sheaf. The
canonical differential morphism and the actual pullback/pushforward
adjunction construct its reduction map to the original differential
sheaf. No global cotangent exactness or comparison is assumed here.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveCotangent

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2CartierProjectiveCover CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveComplexSplittings CycleQ2LiteralProjectiveDeformationCover
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSchemeDifferentialMap

abbrev ClosedSurface := projectiveSurface 57 1

def totalGlobalCoefficient : ℂ →+* Γ(projectiveDeformation,⊤) :=
  schemeCoefficient deformationToComplex

def totalDifferentialSheaf : projectiveDeformation.Modules :=
  differentialSheaf projectiveDeformation.sheaf totalGlobalCoefficient

def restrictedCotangentSheaf : ClosedSurface.Modules :=
  (Scheme.Modules.pullback closedFiber).obj totalDifferentialSheaf

abbrev originalDifferentialSheaf : ClosedSurface.Modules :=
  CycleQ2GeometricSurfaceCoefficients.projectiveDifferentialSheaf 57 1

theorem closedFiber_coefficient (U : projectiveDeformation.Opens) (c : ℂ) :
    closedFiber.app U (coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient U c) =
      coefficientOn ClosedSurface.sheaf
        (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1) (closedFiber ⁻¹ᵁ U) c := by
  have he : schemeCoefficient (closedFiber ≫ deformationToComplex) =
      CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1 :=
    congrArg (fun f : ClosedSurface ⟶ Spec (CommRingCat.of ℂ) => schemeCoefficient f)
      closedFiber_overComplex
  exact (coefficientOn_app closedFiber deformationToComplex U c).trans
    (congrArg (fun cX : ℂ →+* Γ(ClosedSurface,⊤) =>
      coefficientOn ClosedSurface.sheaf cX (closedFiber ⁻¹ᵁ U) c) he)

def pushedCotangentReduction :
    totalDifferentialSheaf ⟶ (Scheme.Modules.pushforward closedFiber).obj originalDifferentialSheaf :=
  schemeDifferentialMap closedFiber
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
    totalGlobalCoefficient closedFiber_coefficient

def cotangentReduction : restrictedCotangentSheaf ⟶ originalDifferentialSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction closedFiber).homEquiv
    totalDifferentialSheaf originalDifferentialSheaf).symm pushedCotangentReduction

theorem cotangentReduction_adjunct :
    (Scheme.Modules.pullbackPushforwardAdjunction closedFiber).homEquiv
        totalDifferentialSheaf originalDifferentialSheaf cotangentReduction =
      pushedCotangentReduction :=
  ((Scheme.Modules.pullbackPushforwardAdjunction closedFiber).homEquiv
    totalDifferentialSheaf originalDifferentialSheaf).apply_symm_apply _

theorem pushedCotangentReduction_D (U : projectiveDeformation.Opens)
    (a : Γ(projectiveDeformation,U)) :
    pushedCotangentReduction.val.app (op U)
        ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d a) =
      (universalDifferential ClosedSurface.sheaf
        (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)).d (closedFiber.app U a) :=
  schemeDifferentialMap_D closedFiber
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
    totalGlobalCoefficient closedFiber_coefficient U a

theorem pushedCotangentReduction_ideal (U : projectiveDeformation.Opens)
    (a : RingHom.ker (closedFiber.app U).hom) :
    pushedCotangentReduction.val.app (op U)
      ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d (a : Γ(projectiveDeformation,U))) = 0 :=
  schemeDifferentialMap_ideal closedFiber
    (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
    totalGlobalCoefficient closedFiber_coefficient U a

end CycleQ2LiteralProjectiveCotangent

end

#print axioms CycleQ2LiteralProjectiveCotangent.restrictedCotangentSheaf
#print axioms CycleQ2LiteralProjectiveCotangent.cotangentReduction_adjunct
#print axioms CycleQ2LiteralProjectiveCotangent.pushedCotangentReduction_D
#print axioms CycleQ2LiteralProjectiveCotangent.pushedCotangentReduction_ideal
