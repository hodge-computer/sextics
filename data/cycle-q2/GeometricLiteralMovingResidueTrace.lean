import Proposal.GeometricLiteralMovingResidueConnecting
import Proposal.GeometricLiteralMovingChernTrace
import Proposal.GeometricLiteralMovingQuotientTrace

/-!
# The moving curve detects the contracted differential class

For each regular moving divisor the connecting map sends the actual
contracted class to a canonical class with nonzero trace. The normalized
trace identifies the canonical cohomology with the complex numbers, so
every canonical class dies upon allowing a simple pole along this curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueTrace

open CategoryTheory CategoryTheory.Abelian TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralMovingChernTrace CycleQ2LiteralMovingResidueConnecting
  CycleQ2LiteralMovingQuotientTrace CycleQ2LiteralMovingResidueClass
  CycleQ2LiteralMovingResidueExact CycleQ2LiteralCotangentTrace
  CycleQ2LiteralAbelJacobiMovingFaces CycleQ2SeedSectionAffineInjective

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

theorem residueConnecting_trace_ne_zero :
    algebraicTrace (residueConnecting t ht ⊤ (residueClass t ht pivotOne pivotOne_closed)) ≠ 0 := by
  rw [residueConnecting_contracted]
  exact movingClass_cubic_trace_ne_zero t ht

theorem contracted_residueClass_ne_zero :
    residueClass t ht pivotOne pivotOne_closed ≠ 0 := by
  intro h
  exact residueConnecting_trace_ne_zero t ht (by rw [h, map_zero, map_zero])

/-- The obstruction concerns the displayed contracted cocycle on this very curve. -/
theorem contracted_not_lifted :
    ¬ ∃ y : (residueComplex t).X₂.H' 1 ⊤,
      y.comp (Ext.mk₀ (residueComplex t).g) (add_zero 1) =
        residueClass t ht pivotOne pivotOne_closed :=
  fun h => residueConnecting_trace_ne_zero t ht ((residueTrace_eq_zero_iff t ht _).mpr h)

open CycleQ2GeometricSheafCohomologyScalar CycleQ2SurfaceCechTwoScalar
  CycleQ2GeometricIntrinsicNormal CycleQ2SeedSectionSheafCurveBinding
open CycleQ2SurfaceCoordinateFrames (CanonicalForms)
open CycleQ2CanonicalResidueSheaf (Surface)

include ht in
/-- Every canonical two-class on the literal surface is killed by the
regular inclusion into forms with a simple pole along the moving divisor. -/
theorem canonicalH2_to_poles_zero (x : CanonicalH2) :
    x.comp (Ext.mk₀ (residueComplex t).f) (add_zero 2) = 0 := by
  let y : CanonicalH2 := residueConnecting t ht ⊤ (residueClass t ht pivotOne pivotOne_closed)
  have hy : algebraicTrace y ≠ 0 := residueConnecting_trace_ne_zero t ht
  have hx : x = (algebraicTrace x / algebraicTrace y) • y := by
    apply algebraicTrace_injective
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have hz : y.comp (Ext.mk₀ (residueComplex t).f) (add_zero 2) = 0 := by
    dsimp only [y]
    rw [residueConnecting_apply, Ext.comp_assoc_of_third_deg_zero,
      ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]
  rw [hx]
  have h := cohomologyMap_scalar Surface.sheaf (surfaceGlobalCoefficient 57 1)
    CanonicalForms (CycleQ2LocalHomFrame.idealRegularInclusion (curveToSurface t) CanonicalForms) 2 ⊤
    (algebraicTrace x / algebraicTrace y) y
  refine h.trans ?_
  change cohomologyScalar Surface.sheaf (surfaceGlobalCoefficient 57 1)
    (CycleQ2LiteralMovingResiduePole.PoleForms t) 2 ⊤ (algebraicTrace x / algebraicTrace y)
    (y.comp (Ext.mk₀ (residueComplex t).f) (add_zero 2)) = 0
  rw [hz, map_zero]

theorem residueConnecting_surjective : Function.Surjective (residueConnecting t ht ⊤) := by
  intro x
  exact Ext.covariant_sequence_exact₁ _ (residueShortExact t ht) x (canonicalH2_to_poles_zero t ht x) rfl

end CycleQ2LiteralMovingResidueTrace
end

#print axioms CycleQ2LiteralMovingResidueTrace.contracted_residueClass_ne_zero
#print axioms CycleQ2LiteralMovingResidueTrace.residueConnecting_surjective
