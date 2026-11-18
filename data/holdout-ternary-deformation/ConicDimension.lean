import Proposal.ConicTarget

/-!
The dominant conic extension is finite. Both fields have transcendence
degree four over the Fermat function field, and the source is essentially
of finite type. This invokes fqlx's shared dimension criterion with every
algebra and injectivity hypothesis supplied by the preceding modules.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open HoldoutConstruction Algebra

lemma parameterField_trdeg_ring : trdeg FermatRing ParameterField=3 := by
  letI : Algebra.IsAlgebraic ParameterRing ParameterField :=
    IsLocalization.isAlgebraic ParameterField (nonZeroDivisors ParameterRing)
  have h := trdeg_add_eq FermatRing ParameterRing (A := ParameterField)
  simpa [trdeg_eq_zero,MvPolynomial.trdeg_of_isDomain] using h.symm
lemma parameterField_trdeg : trdeg BaseField ParameterField=3 := by
  letI : Algebra.IsAlgebraic FermatRing BaseField :=
    IsLocalization.isAlgebraic BaseField (nonZeroDivisors FermatRing)
  have h := trdeg_add_eq FermatRing BaseField (A := ParameterField)
  simpa only [trdeg_eq_zero,zero_add,parameterField_trdeg_ring] using h
instance parameterField_essFiniteType : Algebra.EssFiniteType BaseField ParameterField := by
  letI : Algebra.EssFiniteType ParameterRing ParameterField :=
    Algebra.EssFiniteType.of_isLocalization ParameterField (nonZeroDivisors ParameterRing)
  letI : Algebra.EssFiniteType FermatRing ParameterField :=
    Algebra.EssFiniteType.comp FermatRing ParameterRing ParameterField
  exact Algebra.EssFiniteType.of_comp FermatRing BaseField ParameterField
lemma functionField_trdeg : trdeg BaseField FunctionField=4 := by
  rw [polynomial_fractionRing_trdeg BaseField ParameterField,parameterField_trdeg]
  norm_num
instance functionField_essFiniteType : Algebra.EssFiniteType BaseField FunctionField :=
  polynomial_fractionRing_essFiniteType BaseField ParameterField CoefficientField
lemma targetField_trdeg : trdeg BaseField TargetField=4 := by
  apply monic_hypersurface_field_trdeg targetPolynomial
    (DeformedGeometry.quotientPolynomial_monic _ _ _)
  exact ne_of_gt ((DeformedGeometry.quotientPolynomial_monic _ _ _).degree_pos_of_not_isUnit
    (DeformedGeometry.quotientPolynomial_irreducible _ _ _).not_isUnit)
instance functionField_finite : Module.Finite TargetField FunctionField := by
  apply finite_of_same_finite_trdeg (K := BaseField)
  · rw [targetField_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [targetField_trdeg,functionField_trdeg]

end DeformedConic
#print axioms DeformedConic.functionField_finite
