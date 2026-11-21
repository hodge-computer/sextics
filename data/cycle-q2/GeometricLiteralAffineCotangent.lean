import Proposal.GeometricAffineKahlerSheaf
import Proposal.GeometricAffineModulePullback
import Proposal.GeometricOpenDifferentialSheaf
import Proposal.GeometricLiteralProjectiveCotangent

/-!
# The canonical restricted cotangent sheaf on the original native charts

The actual affine Proj maps and original reduction square identify the
canonical scheme-module pullback with the tilde of the literal tensor
module ClosedRing tensor_ThickRing Omega(ThickRing/C). Both differential
sheaf comparisons are universal and use the original complex coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAffineCotangent

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2CartierSurfaceGrading CycleQ2LiteralGradedDeformation
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveComplexSplittings
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralProjectiveCotangent CycleQ2LiteralNativeCotangent
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
  CycleQ2GeometricAffineModulePullback CycleQ2GeometricOpenDifferentialSheaf

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

abbrev thickAffineMap (s : Finset Vertex) (hs : s.Nonempty) :
    Spec (CommRingCat.of (ThickRing s)) ⟶ projectiveDeformation :=
  Proj.awayι deformationGrade (thickProduct s) (thickProduct_homogeneous s) (productDegree_pos hs)

abbrev closedAffineMap (s : Finset Vertex) (hs : s.Nonempty) :
    Spec (CommRingCat.of (ClosedRing s)) ⟶ ClosedSurface :=
  Proj.awayι (surfaceGrade 57 1) (closedProduct s)
    (closedProduct_homogeneous s) (productDegree_pos hs)

theorem affineCoefficient_square {Y : Scheme.{0}} {A : Type} [CommRing A] [Algebra ℂ A]
    (j : Spec (CommRingCat.of A) ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of ℂ))
    (h : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
    (U : Y.Opens) (c : ℂ) :
    j.app U (coefficientOn Y.sheaf (schemeCoefficient f) U c) =
      coefficientOn (Spec.structureSheaf A) (affineCoefficient A) (j ⁻¹ᵁ U) c := by
  have he : schemeCoefficient (j ≫ f) = affineCoefficient A :=
    (congrArg (fun g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℂ) =>
      schemeCoefficient g) h).trans
      (congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism A).symm)
  exact (coefficientOn_app j f U c).trans
    (congrArg (fun cX : ℂ →+* Γ(Spec (CommRingCat.of A), ⊤) =>
      coefficientOn (Spec.structureSheaf A) cX (j ⁻¹ᵁ U) c) he)

theorem thickAffine_coefficient (s : Finset Vertex) (hs : s.Nonempty)
    (U : projectiveDeformation.Opens) (c : ℂ) :
    (thickAffineMap s hs).app U (coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient U c) =
      coefficientOn (Spec.structureSheaf (ThickRing s)) (affineCoefficient (ThickRing s))
        (thickAffineMap s hs ⁻¹ᵁ U) c :=
  affineCoefficient_square (thickAffineMap s hs) deformationToComplex (thickCoefficient_scheme s hs) U c

theorem closedAffine_coefficient (s : Finset Vertex) (hs : s.Nonempty)
    (U : ClosedSurface.Opens) (c : ℂ) :
    (closedAffineMap s hs).app U
        (coefficientOn ClosedSurface.sheaf
          (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1) U c) =
      coefficientOn (Spec.structureSheaf (ClosedRing s)) (affineCoefficient (ClosedRing s))
        (closedAffineMap s hs ⁻¹ᵁ U) c :=
  affineCoefficient_square (closedAffineMap s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)
    (closedCoefficient_scheme s hs) U c

def thickDifferentialIso (s : Finset Vertex) (hs : s.Nonempty) :
    (Scheme.Modules.pullback (thickAffineMap s hs)).obj totalDifferentialSheaf ≅
      kahlerTilde (A := ThickRing s) :=
  pullbackOpenDifferentialIso (thickAffineMap s hs)
      (affineCoefficient (ThickRing s)) totalGlobalCoefficient (thickAffine_coefficient s hs) ≪≫
    affineKahlerIso

def closedDifferentialIso (s : Finset Vertex) (hs : s.Nonempty) :
    (Scheme.Modules.pullback (closedAffineMap s hs)).obj originalDifferentialSheaf ≅
      kahlerTilde (A := ClosedRing s) :=
  pullbackOpenDifferentialIso (closedAffineMap s hs)
      (affineCoefficient (ClosedRing s))
      (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
      (closedAffine_coefficient s hs) ≪≫ affineKahlerIso

def nativeTensorModuleIso (s : Finset Vertex) :
    (ModuleCat.extendScalars (nativeReduction s)).obj
        (ModuleCat.of (ThickRing s) (KaehlerDifferential ℂ (ThickRing s))) ≅
      ModuleCat.of (ClosedRing s) (NativeCotangent s) := Iso.refl _

abbrev nativeCotangentTilde (s : Finset Vertex) :=
  tilde (R := CommRingCat.of (ClosedRing s)) (ModuleCat.of (ClosedRing s) (NativeCotangent s))

/-- This identifies the original canonical global sheaf with the original
native tensor module on every actual nonempty finite intersection chart. -/
def nativeCotangentIso (s : Finset Vertex) (hs : s.Nonempty) :
    (Scheme.Modules.pullback (closedAffineMap s hs)).obj restrictedCotangentSheaf ≅
      nativeCotangentTilde s :=
  (Scheme.Modules.pullbackComp (closedAffineMap s hs) closedFiber).app totalDifferentialSheaf ≪≫
    (Scheme.Modules.pullbackCongr (nativeReduction_scheme_square s hs)).app totalDifferentialSheaf ≪≫
    ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (nativeReduction s)))
      (thickAffineMap s hs)).app totalDifferentialSheaf).symm ≪≫
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (nativeReduction s)))).mapIso
      (thickDifferentialIso s hs) ≪≫
    (pullbackTildeIso (CommRingCat.ofHom (nativeReduction s))).app
      (ModuleCat.of (ThickRing s) (KaehlerDifferential ℂ (ThickRing s))) ≪≫
    (tilde.functor (CommRingCat.of (ClosedRing s))).mapIso (nativeTensorModuleIso s)

end CycleQ2LiteralAffineCotangent

end

#print axioms CycleQ2LiteralAffineCotangent.thickDifferentialIso
#print axioms CycleQ2LiteralAffineCotangent.closedDifferentialIso
#print axioms CycleQ2LiteralAffineCotangent.nativeCotangentIso
