import Proposal.GeometricOpenCoverAdditiveExactness
import Proposal.GeometricLiteralCotangentEpi
import Proposal.GeometricLiteralCotangentEpsilonKernel
import Proposal.GeometricLiteralCotangentEpsilonMap
import Proposal.GeometricLiteralCotangentAffineExact

/-!
# The global cotangent short exact sequence of the original deformation

On each native chart the pullback of the global cotangent complex is
isomorphic to the tilde of the split tensor complex. Both squares use
the canonical isomorphisms on the individual terms. The twelve singleton
charts cover the original closed surface, so exactness descends.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentShortExact

open CategoryTheory AlgebraicGeometry CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveCotangent CycleQ2LiteralAffineCotangent
  CycleQ2LiteralCotangentEpsilon CycleQ2LiteralCotangentEpsilonKernel
  CycleQ2LiteralCotangentAffineExact CycleQ2LiteralCotangentEpi
  CycleQ2LiteralCotangentEpsilonMap CycleQ2LiteralCotangentReduction
  CycleQ2GeometricOpenCoverModuleExactness CycleQ2GeometricOpenCoverAdditiveExactness

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def cotangentComplex : ShortComplex ClosedSurface.Modules :=
  ShortComplex.mk epsilonInclusion cotangentReduction epsilonInclusion_cotangentReduction

def cotangentAdditiveComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} ClosedSurface) :=
  additiveComplex cotangentComplex

def chartCotangentComplexIso (s : Finset Vertex) (hs : s.Nonempty) :
    cotangentComplex.map (Scheme.Modules.pullback (closedAffineMap s hs)) ≅
      nativeTildeComplex s :=
  ShortComplex.isoMk (nativeUnitIso s hs) (nativeCotangentIso s hs) (closedDifferentialIso s hs)
    (nativeCotangentEpsilon_comm s hs) (nativeCotangentReduction_comm s hs)

theorem cotangentShortExact : cotangentComplex.ShortExact := by
  apply shortExact_of_open_pullbacks
    (fun i : Vertex => closedAffineMap {i} (Finset.singleton_nonempty i)) closedAffineMap_cover
  intro i
  exact ShortComplex.shortExact_of_iso
    (chartCotangentComplexIso {i} (Finset.singleton_nonempty i)).symm
    (nativeTildeShortExact {i} (Finset.singleton_nonempty i))

theorem cotangentAdditiveShortExact : cotangentAdditiveComplex.ShortExact := by
  apply additiveShortExact_of_open_splittings
    (fun i : Vertex => closedAffineMap {i} (Finset.singleton_nonempty i)) closedAffineMap_cover
  intro i
  exact (nativeTildeSplitting {i} i.1 ⟨i.2, Finset.mem_singleton_self i⟩).ofIso
    (chartCotangentComplexIso {i} (Finset.singleton_nonempty i)).symm

end CycleQ2LiteralCotangentShortExact

end

#print axioms CycleQ2LiteralCotangentShortExact.cotangentShortExact
#print axioms CycleQ2LiteralCotangentShortExact.cotangentAdditiveShortExact
