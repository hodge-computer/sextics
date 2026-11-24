import Proposal.GeometricLiteralMovingCurveDifferential
import Proposal.GeometricLiteralMovingResidueConnecting
import Proposal.GeometricLiteralMovingChernTrace

/-!
# The contracted differential class on the moving curve

Restrict the contracted surface differential to the moving curve and
transport the resulting cohomology class from its direct image. Its
image under the curve residue morphism is the actual quotient class
whose boundary is the retained cubic times the moving Chern obstruction.
The nonzero normalized surface trace detects the class in H¹(Γ,Ω¹_Γ).

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingCurveDifferentialNonzero

open CategoryTheory CategoryTheory.Abelian TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueClass
  CycleQ2LiteralAbelJacobiMovingFaces CycleQ2LiteralMovingResidueDifferentialClass
  CycleQ2LiteralMovingResidueConnecting CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralMovingChernTrace CycleQ2LiteralCotangentTrace CycleQ2ClosedEmbeddingCohomology
  CycleQ2LiteralMovingQuotientTrace CycleQ2CanonicalCubicDiagram CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2LiteralCotangentShortExact CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- On the contracted differential this trace is the original moving Chern-cubic pairing. -/
theorem differentialTrace_curveClass :
    differentialTrace t ht (curveClass t) =
      algebraicTrace (cubicH2 firstOrderWeightedCubic
        ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) := by
  change algebraicTrace (residueConnecting t ht ⊤
    (((pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1)
      (curveClass t)).comp (Ext.mk₀ (curveResidue t ht)) (add_zero 1))) = _
  rw [curveClass_residue, residueConnecting_contracted]

theorem differentialTrace_curveClass_ne_zero : differentialTrace t ht (curveClass t) ≠ 0 :=
  (differentialTrace_curveClass t ht).symm ▸ movingClass_cubic_trace_ne_zero t ht

include ht in
/-- The actual contracted differential on the moving curve has nonzero class. -/
theorem curveClass_ne_zero : curveClass t ≠ 0 := by
  intro hx
  apply differentialTrace_curveClass_ne_zero t ht
  rw [hx, map_zero]

/-- Every nonempty principal open of section vectors has a proper flat first-order
family with nonempty seed and a nonzero differential class on that seed curve. -/
theorem exists_flat_curve_with_nonzero_differential
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ (s : Fin 3 → ℂ) (_ : ∀ i, ChartRegular s i),
      MvPolynomial.eval s P ≠ 0 ∧ s ≠ 0 ∧ Flat (firstOrderCurveToBase s) ∧
      IsProper (firstOrderCurveToBase s) ∧ Nonempty (FirstOrderCurveSeedFiber s) ∧ curveClass s ≠ 0 := by
  obtain ⟨s,hs,hPs,hs₀,hf,hp,hn,_⟩ := exists_flat_moving_curve_with_nonzero_trace P hP
  exact ⟨s,hs,hPs,hs₀,hf,hp,hn,curveClass_ne_zero s hs⟩

end CycleQ2LiteralMovingCurveDifferentialNonzero
end

#print axioms CycleQ2LiteralMovingCurveDifferentialNonzero.differentialTrace_curveClass
#print axioms CycleQ2LiteralMovingCurveDifferentialNonzero.curveClass_ne_zero

#print axioms CycleQ2LiteralMovingCurveDifferentialNonzero.exists_flat_curve_with_nonzero_differential
