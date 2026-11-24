import Proposal.GeometricLiteralCotangentTrace
import Proposal.GeometricCanonicalCurveImage

/-!
# Residue transitivity for the original curve and surface coordinates

The curve coordinate is fixed by its degree-nine Čech representative.
The surface coordinate is fixed by the monomial with Laurent residue one.
The actual residue sequence from the original embedded curve carries its
canonical cohomology onto the canonical cohomology of the surface. In the
two prescribed coordinates, the connecting homomorphism is multiplication
by a single nonzero scalar, determined on the original curve generator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCurveSurfaceTrace

open CycleQ2CanonicalCurveImage CycleQ2GeometricLiteralHOne CycleQ2LiteralCotangentTrace

/-- Conversion between the fixed generator on the original curve and the fixed surface residue. -/
def boundaryScale : ℂ :=
  algebraicTrace (canonicalConnectingOnCurve literalCanonicalNormalization)

theorem boundaryScale_ne_zero : boundaryScale ≠ 0 :=
  fun h => canonicalConnectingOnCurve_normalization_ne_zero
    ((algebraicTrace_eq_zero_iff _).mp h)

/-- Evaluation after the actual canonical residue boundary, for every class on the curve. -/
theorem residue_transitivity (x : CurveHOne) :
    algebraicTrace (canonicalConnectingOnCurve x) = literalCanonicalCoordinate x * boundaryScale := by
  rw [canonicalConnectingOnCurve_formula x, map_smul]
  rfl

theorem canonicalConnectingOnCurve_surjective : Function.Surjective canonicalConnectingOnCurve := by
  intro y
  refine ⟨(algebraicTrace y / boundaryScale) • literalCanonicalNormalization, ?_⟩
  apply algebraicTrace_injective
  rw [residue_transitivity, map_smul, literalCanonicalCoordinate_normalization, smul_eq_mul, mul_one,
    div_mul_cancel₀ _ boundaryScale_ne_zero]

/-- The genuine curve-to-surface residue connecting homomorphism is an isomorphism. -/
def curveSurfaceResidueEquiv : CurveHOne ≃ₗ[ℂ] CanonicalH2 :=
  LinearEquiv.ofBijective canonicalConnectingOnCurve
    ⟨canonicalConnectingOnCurve_injective, canonicalConnectingOnCurve_surjective⟩

/-- The fixed surface residue evaluates the full two-entry row with its common scale. -/
theorem paired_surface_residue (v : Fin 9 → ℂ) :
    algebraicTrace (canonicalConnectingOnCurve (literalPairedCanonicalLinear v)) =
      (((12 + 24 * Complex.I) / 5) * boundaryScale) *
        ((Complex.I * v 1 - (1 + Complex.I) * v 8) / 6) :=
  literal_paired_trace_formula (algebraicTrace.comp canonicalConnectingOnCurve) v

end CycleQ2LiteralCurveSurfaceTrace
end

#print axioms CycleQ2LiteralCurveSurfaceTrace.curveSurfaceResidueEquiv
#print axioms CycleQ2LiteralCurveSurfaceTrace.paired_surface_residue
