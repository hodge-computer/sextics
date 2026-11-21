import Proposal.GeometricLiteralMovingCurveDifferential

/-!
# Detecting the surface Kodaira–Spencer class on the moving curve

Contract a tangent class with the canonical form of the retained cubic,
then restrict the resulting differential to the moving curve. For the
Kodaira–Spencer class of the independent ambient test this gives the
curve's actual differential class. The proof compares its native cover
with the refinement on which the moving divisor has its explicit frames.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingCurveKodairaSpencer

open CategoryTheory CategoryTheory.Abelian TopologicalSpace AlgebraicGeometry
  CycleQ2FiniteCechHOne CycleQ2LiteralSheafOneClasses
  CycleQ2LiteralNativeKodairaSpencerCocycle CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralAbelJacobiContractedCocycle CycleQ2LiteralAbelJacobiMovingFaces
  CycleQ2LiteralMovingDivisorChern CycleQ2SeedSectionSheafCurveBinding
  CycleQ2ClosedEmbeddingCohomology CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingCurveDifferentialNonzero CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingResidueClass CycleQ2LiteralMovingQuotientTrace

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- Restriction of the contraction with the canonical cubic to ordinary
differentials on the original moving curve. -/
def restrictContraction : tangentAddSheaf.H' 1 ⊤ →+ (curveForms t).H' 1 ⊤ :=
  (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding
    (curveForms t) 1).symm.toAddMonoidHom.comp
    (((Ext.mk₀ (pullbackForms t)).postcomp _ (add_zero 1)).comp
      ((Ext.mk₀ contractionMap).postcomp _ (add_zero 1)))

theorem pivotClass_eq_contracted :
    cechOneClass pivotCover pivotCover_covers pivotOne pivotOne_closed = contractedClass :=
  cechOneClass_refinement cover pivotCover parentVertex pivot_le_native cover_covers
    pivotCover_covers contractedOne contractedOne_closed

theorem restrictContraction_kodairaSpencer :
    restrictContraction t kodairaSpencerDerivedClass = curveClass t := by
  unfold curveClass
  rw [pivotClass_eq_contracted, contractedClass_eq_image]
  rfl

/-- Evaluation on the original ambient-test tangent via the actual
differential on the curve and its conormal wedge. -/
theorem differentialTrace_restrictContraction :
    differentialTrace t ht (restrictContraction t kodairaSpencerDerivedClass) =
      residueTrace t ht (residueClass t ht pivotOne pivotOne_closed) := by
  rw [restrictContraction_kodairaSpencer]
  exact congrArg (residueTrace t ht) (curveClass_residue t ht)

end CycleQ2LiteralMovingCurveKodairaSpencer
end

#print axioms CycleQ2LiteralMovingCurveKodairaSpencer.restrictContraction_kodairaSpencer
#print axioms CycleQ2LiteralMovingCurveKodairaSpencer.differentialTrace_restrictContraction
