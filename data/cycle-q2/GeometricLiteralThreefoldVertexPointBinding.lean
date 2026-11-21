import Proposal.GeometricLiteralThreefoldCurveTestBinding
import Proposal.GeometricLiteralThreefoldVertexPoint

/-!
# The moving affine vertex point equals the native reduced surface point

These are the scalar maps for the two ambient tangents in the mixed
contraction. Their equality is checked on the entire threefold chart by
restriction along the central fibre of the actual correspondence.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace CycleQ2LiteralThreefoldVertexPointBinding

open CategoryTheory AlgebraicGeometry CycleQ2LiteralThreefoldCurveTestBinding
  CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralThreefoldVertexMotion CycleQ2LiteralThreefoldVertexPoint
  CycleQ2LiteralMovingResidueAdjunction.AffineFrame CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeGaugeSections
  CycleQ2SeedSectionSheafCurveBinding CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceSeedFiberCover CycleQ2LiteralAmbientCharts

attribute [local instance] closedComplexAlgebra curveComplexOn

theorem withinVertex (t : Fin 3 → ℂ) (s : Finset Vertex) (v : Vertex) (hv : v ∈ s)
    (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) : W ≤ vertexOpen t v := by
  apply hW.trans
  apply (curveToSurface t).preimage_mono
  rw [closedOpen_eq]
  exact iInf₂_le v hv

/-- The native point on any nonempty intersection and the original affine
moving-curve point are the same complex algebra homomorphism on that subopen. -/
theorem ambientPoint_eq_native (t : Fin 3 → ℂ) (s : Finset Vertex) (hs : s.Nonempty)
    (v : Vertex) (hv : v ∈ s) (W : (Curve t).Opens) (hW : W ≤ (curveToSurface t) ⁻¹ᵁ closedOpen s) :
    (nativeToCurve t s hs W hW).comp (fixedPoint s v hv) =
      ambientPoint t v W (withinVertex t s v hv W hW) := by
  let hV : seedBasePoint ∈ (⊤ : parameterScheme.Opens) := trivial
  apply AlgHom.ext
  intro x
  exact (fixedPoint_curve ⊤ t hV s hs v hv W hW x).trans
    (ambientPoint_on_subopen ⊤ t hV v (fixedOpen (chartIndex v)) le_rfl W
      (withinVertex t s v hv W hW) (native_within ⊤ t hV s hs v hv W hW) x).symm

end CycleQ2LiteralThreefoldVertexPointBinding
end

#print axioms CycleQ2LiteralThreefoldVertexPointBinding.ambientPoint_eq_native
