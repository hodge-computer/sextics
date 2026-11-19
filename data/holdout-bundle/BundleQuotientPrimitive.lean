import Proposal.BundleConicEmbedding
import Proposal.BundleCoefficientDerivations
import Proposal.BundleIntegration

/-!
The actual anchored conic integrates every polynomial density in the
relative diagonal quotient. All field, endpoint, normal, determinant and
finite-trace hypotheses are discharged here by the concrete construction.
The physical density and its full six-variable pullback are assembled in
the final certificate module.
-/

noncomputable section

namespace HoldoutBundle
open Polynomial MvPolynomial HoldoutConstruction

local instance quotientPrimitiveConicIntAlgebra : Algebra ℤ ConicFunctionField := Ring.toIntAlgebra _
local instance quotientPrimitiveIntAlgebra : Algebra ℤ QuotientField := Ring.toIntAlgebra _

theorem quotient_polynomial_residue_solution (A : MvPolynomial (Fin 5) BaseField) :
    ∃ w : Fin 4 → QuotientField,
      residueDivergence quotientTangent
          (quotientResidueMap (integerPartial 0 (kPoly genericA genericB))) w =
        -(quotientResidueMap (integerPartial 0 A) /
            quotientResidueMap (integerPartial 0 (kPoly genericA genericB)) -
          quotientResidueMap A *
            quotientResidueMap (integerPartial 0 (integerPartial 0 (kPoly genericA genericB))) /
              (quotientResidueMap (integerPartial 0 (kPoly genericA genericB)))^2) := by
  apply ConicFamily.residue_solution_from_conic (K := QuotientField)
    (E := CoefficientField) quotientProjection quotientProjection_surjective
    genericA genericB A conicEndpoint genericConic coefficientDerivation
    coefficientDerivations_commute coefficientDerivation_parameter coefficientDerivation_base
    quotientTangent quotient_normal_ne_zero
  · intro j f
    exact quotientTangent_apply j f
  · intro f
    change conicTargetFieldMap (quotientResidueMap f) =
      MvPolynomial.eval₂Hom (algebraMap BaseField ConicFunctionField)
        (fun i => algebraMap (Polynomial CoefficientField) ConicFunctionField
          (genericConic.curve i)) f
    exact conicTargetFieldMap_residue f

end HoldoutBundle

#print axioms HoldoutBundle.quotient_polynomial_residue_solution
