import Proposal.JacobianEmbedding

/-! The dominant conic extension is finite, by equality of transcendence
degrees and essential finite generation. Uses the shared dimension lemmas.
Adapted from the accepted constructions of fqlx and hodgepodgeconjecture.
Prepared for benediamond with OpenAI Codex assistance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace MixedPolarJacobianDimension
open HoldoutConstruction MixedPolarJacobianLifting MixedPolarJacobianFamily MixedPolarJacobianEmbedding Algebra
lemma parameterField_trdeg : trdeg ℂ ComplexParameterField=4 := by
  rw [fractionRing_trdeg,MvPolynomial.trdeg_of_isDomain]
  simp
instance parameterField_essFiniteType : Algebra.EssFiniteType ℂ ComplexParameterField :=
  fractionRing_essFiniteType ℂ ComplexParameterRing
lemma functionField_trdeg : trdeg ℂ FunctionField=5 := by
  rw [polynomial_fractionRing_trdeg ℂ ComplexParameterField,parameterField_trdeg]
  norm_num
instance functionField_essFiniteType : Algebra.EssFiniteType ℂ FunctionField :=
  polynomial_fractionRing_essFiniteType ℂ ComplexParameterField CoefficientField
lemma targetField_trdeg : trdeg ℂ TargetField=5 := by
  apply monic_hypersurface_field_trdeg MixedPolarJacobianDomain.equation MixedPolarJacobianDomain.equation_monic
  exact ne_of_gt (MixedPolarJacobianDomain.equation_monic.degree_pos_of_not_isUnit
    MixedPolarJacobianDomain.equation_irreducible.not_isUnit)
instance functionField_finite : Module.Finite TargetField FunctionField := by
  apply finite_of_same_finite_trdeg (K := ℂ)
  · rw [targetField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [targetField_trdeg,functionField_trdeg]
#print axioms functionField_finite
end MixedPolarJacobianDimension
