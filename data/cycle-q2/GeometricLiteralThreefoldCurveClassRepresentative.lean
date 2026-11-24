import Proposal.GeometricClosedEmbeddingCechOne
import Proposal.GeometricLiteralMovingCurveKodairaSpencer
import Proposal.GeometricLiteralThreefoldCurveTestSections

/-!
# The detected differential on the original twelve curve opens

The differential class whose residue is computed by the moving divisor
has the pullback of the twelve native surface edges as its representative
in the cohomology of the central curve itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace CycleQ2LiteralThreefoldCurveClassRepresentative

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralAbelJacobiContractedCocycle
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralMovingCurveDifferentialNonzero
  CycleQ2LiteralMovingCurveKodairaSpencer CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame
  CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralAbelJacobiMovingFaces CycleQ2ClosedEmbeddingCechOne
open CycleQ2FiniteCechOrbitPullback (pullOne pullOne_closed edgeValue_pullOne pullTo)

local instance (Z : TopCat.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _
local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _

variable (t : Fin 3 → ℂ)

def beta : One (curveForms t) (vertexOpen t) :=
  pullOne (curveToSurface t).base (pullbackForms t) cover contractedOne

theorem beta_closed : IsOneCocycle (curveForms t) (vertexOpen t) (beta t) :=
  pullOne_closed _ _ _ _ contractedOne_closed

theorem curveClass_eq_beta : curveClass t =
    cechOneClass (vertexOpen t) (vertexOpen_cover t) (beta t) (beta_closed t) := by
  let j := curveToSurface t
  let e := CycleQ2ClosedEmbeddingCohomology.pushHEquiv j.base j.isClosedEmbedding (curveForms t) 1
  let f : CycleQ2LiteralNativeChernCocycle.differentialAddSheaf.H' 1 ⊤ → (curveForms t).H' 1 ⊤ :=
    fun ξ => e.symm (ξ.comp (Ext.mk₀ (pullbackForms t)) (add_zero 1))
  exact (congrArg f pivotClass_eq_contracted).trans
    (restrict_cech j.base j.isClosedEmbedding (pullbackForms t) cover cover_covers contractedOne contractedOne_closed)

theorem beta_edge (u v : CycleQ2LiteralProjectiveIntersections.Vertex) (P : Surface.Opens)
    (hu : P ≤ cover u) (hv : P ≤ cover v) (W : (Curve t).Opens)
    (h : W ≤ (curveToSurface t) ⁻¹ᵁ P) :
    edgeValue (curveForms t) (vertexOpen t) (beta t) u v W
      (fun _ hx => hu (h hx)) (fun _ hx => hv (h hx)) =
      pullTo (curveToSurface t).base (pullbackForms t) h (contractedValue u v P hu hv) := by
  exact (edgeValue_pullOne (curveToSurface t).base (pullbackForms t) cover contractedOne u v h hu hv).trans
    (congrArg (pullTo (curveToSurface t).base (pullbackForms t) h) (edgeValue_contractedOne u v P hu hv))

end CycleQ2LiteralThreefoldCurveClassRepresentative
end

#print axioms CycleQ2LiteralThreefoldCurveClassRepresentative.curveClass_eq_beta
#print axioms CycleQ2LiteralThreefoldCurveClassRepresentative.beta_edge
