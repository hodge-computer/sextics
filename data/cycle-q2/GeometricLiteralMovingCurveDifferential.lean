import Proposal.GeometricLiteralAbelJacobiMovingFaces
import Proposal.GeometricLiteralMovingResidueCurve
import Proposal.GeometricLiteralMovingResidueDifferentialClass
import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricLiteralMovingQuotientTrace

/-!
# Restricting the contracted differential to the moving curve

Restrict the contracted surface differential to the moving curve and
transport the resulting cohomology class from its direct image. Its
image under the curve residue morphism is the actual quotient class
on the surface. The algebraic trace on curve differentials first applies
this wedge-residue morphism and then the normalized boundary trace.

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
  CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralCotangentTrace CycleQ2ClosedEmbeddingCohomology
  CycleQ2LiteralMovingQuotientTrace

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The restriction of the actual contracted one-cocycle, in the curve's own cohomology. -/
def curveClass : (curveForms t).H' 1 ⊤ :=
  (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1).symm
    ((cechOneClass pivotCover pivotCover_covers pivotOne pivotOne_closed).comp
      (Ext.mk₀ (pullbackForms t)) (add_zero 1))

/-- The residue image of this particular differential recovers the quotient cocycle. -/
theorem curveClass_residue :
    ((pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1)
      (curveClass t)).comp (Ext.mk₀ (curveResidue t ht)) (add_zero 1) =
        residueClass t ht pivotOne pivotOne_closed := by
  rw [curveClass, AddEquiv.apply_symm_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, pullbackForms_curveResidue]
  exact surfaceResidue_class t ht pivotOne pivotOne_closed

/-- The algebraic trace on curve differentials induced by the actual wedge-residue morphism. -/
def differentialTrace : (curveForms t).H' 1 ⊤ →+ ℂ :=
  (residueTrace t ht).comp (((Ext.mk₀ (curveResidue t ht)).postcomp _ (add_zero 1)).comp
    (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1).toAddMonoidHom)

end CycleQ2LiteralMovingCurveDifferentialNonzero
end

#print axioms CycleQ2LiteralMovingCurveDifferentialNonzero.curveClass_residue
