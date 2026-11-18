import Proposal.BundlePhysicalCoordinates
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import Mathlib.RingTheory.MvPolynomial.Localization

/-! Algebraic spanning proves that the diagonal quotient has the full generic
endpoint. No inversion of a rational-function denominator occurs before
the five parameter coordinates have been proved algebraically independent. -/

noncomputable section

namespace HoldoutBundle
open HoldoutConstruction
open scoped IntermediateField.algebraAdjoinAdjoin

attribute [local instance] holdoutCoordinateRing_isDomain

theorem coordinates_independent_of_spanning
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (x : Fin n → L)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range x)) L]
    (htrdeg : Algebra.trdeg K L=n) : AlgebraicIndependent K x := by
  letI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) L :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin K (Set.range x))
      (IntermediateField.adjoin K (Set.range x)) L
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K x
    (by simp [htrdeg])).1

theorem physical_trdeg : Algebra.trdeg ℂ HoldoutFunctionField=5 := by
  apply monic_hypersurface_field_trdeg (holdoutPolynomial (R := ℂ)) holdoutPolynomial_monic
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6 : ℕ)=2*3 by decide,pow_mul,Complex.I_sq]
    norm_num
  exact ne_of_gt (holdoutPolynomial_monic.degree_pos_of_not_isUnit
    (holdoutPolynomial_irreducible Complex.I hi).not_isUnit)

def physicalParameters : Fin 5 → HoldoutFunctionField :=
  ![physicalLambda,physicalY 1,physicalY 2,physicalP,physicalQ]

abbrev PhysicalParameterField := IntermediateField.adjoin ℂ (Set.range physicalParameters)

theorem physicalParameter_mem (j : Fin 5) : physicalParameters j ∈ PhysicalParameterField :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self j)

theorem physicalParameter_algebraic (j : Fin 5) :
    IsAlgebraic PhysicalParameterField (physicalParameters j) :=
  isAlgebraic_algebraMap (⟨physicalParameters j,physicalParameter_mem j⟩ : PhysicalParameterField)

theorem physicalI_algebraic : IsAlgebraic PhysicalParameterField physicalI :=
  isAlgebraic_algebraMap (algebraMap ℂ PhysicalParameterField Complex.I)

theorem physicalY1_sixth_relation :
    physicalY 4^6=physicalLambda*(physicalP^3+physicalI*physicalQ^3) :=
  (lambdaValue_times_factor physicalI (physicalY 3) (physicalY 4) (physicalY 5)
    physicalBranch_ne_zero).symm

theorem physicalY1_algebraic : IsAlgebraic PhysicalParameterField (physicalY 4) := by
  apply IsAlgebraic.of_pow (by decide : 0 < 6)
  rw [physicalY1_sixth_relation]
  exact (physicalParameter_algebraic 0).mul
    (((physicalParameter_algebraic 3).pow 3).add
      (physicalI_algebraic.mul ((physicalParameter_algebraic 4).pow 3)))

theorem physicalY0_as_ratio : physicalY 3=physicalP/physicalY 4 := by
  simp [physicalP,physicalY4_ne_zero]

theorem physicalY2_as_ratio : physicalY 5=physicalQ/physicalY 4 := by
  simp [physicalQ,physicalY4_ne_zero]

theorem physical_remaining_algebraic (j : Fin 5) :
    IsAlgebraic PhysicalParameterField (physicalY j.succ) := by
  fin_cases j
  · exact physicalParameter_algebraic 1
  · exact physicalParameter_algebraic 2
  · change IsAlgebraic PhysicalParameterField (physicalY 3)
    rw [physicalY0_as_ratio,div_eq_mul_inv]
    exact (physicalParameter_algebraic 3).mul physicalY1_algebraic.inv
  · exact physicalY1_algebraic
  · change IsAlgebraic PhysicalParameterField (physicalY 5)
    rw [physicalY2_as_ratio,div_eq_mul_inv]
    exact (physicalParameter_algebraic 4).mul physicalY1_algebraic.inv

private def physicalAlgebraicCoefficientMap :
    MvPolynomial (Fin 5) ℂ →+* algebraicClosure PhysicalParameterField HoldoutFunctionField :=
  MvPolynomial.eval₂Hom
    (algebraMap ℂ (algebraicClosure PhysicalParameterField HoldoutFunctionField))
    (fun j => ⟨physicalY j.succ,mem_algebraicClosure_iff.mpr (physical_remaining_algebraic j)⟩)

theorem physical_root_algebraic : IsAlgebraic PhysicalParameterField (physicalY 0) := by
  apply IsAlgebraic.restrictScalars PhysicalParameterField
    (S := algebraicClosure PhysicalParameterField HoldoutFunctionField)
  apply IsIntegral.isAlgebraic
  refine ⟨(holdoutPolynomial (R := ℂ)).map physicalAlgebraicCoefficientMap,
    holdoutPolynomial_monic.map _,?_⟩
  have h := physicalY_equation
  simp only [Polynomial.aeval_def,Polynomial.eval₂_map,holdoutPolynomial,
    Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,RingHom.comp_apply,
    physicalAlgebraicCoefficientMap,MvPolynomial.eval₂Hom_X',map_add,map_mul,map_pow]
  change physicalY 0^6+(physicalY 1*physicalY 3*physicalY 4*physicalY 0^3+
    (physicalY 1^6+physicalY 2^6+physicalY 3^6+physicalY 4^6+physicalY 5^6+
      physicalY 1^3*physicalY 2*physicalY 4*physicalY 5))=0
  linear_combination h

theorem physical_all_coordinates_algebraic (j : Fin 6) :
    IsAlgebraic PhysicalParameterField (physicalY j) :=
  Fin.cases physical_root_algebraic physical_remaining_algebraic j

theorem physical_residue_polynomial_algebraic (p : MvPolynomial (Fin 6) ℂ) :
    IsAlgebraic PhysicalParameterField (physicalResidueMap p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [physicalResidueMap_C]
    exact isAlgebraic_algebraMap (algebraMap ℂ PhysicalParameterField c)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p j hp =>
    simpa only [map_mul,physicalY] using hp.mul (physical_all_coordinates_algebraic j)

theorem physical_field_algebraic (z : HoldoutFunctionField) :
    IsAlgebraic PhysicalParameterField z := by
  obtain ⟨a,b,_hb,rfl⟩ := IsFractionRing.div_surjective HoldoutCoordinateRing z
  obtain ⟨p,rfl⟩ := physicalProjection_surjective a
  obtain ⟨q,rfl⟩ := physicalProjection_surjective b
  rw [div_eq_mul_inv]
  exact (physical_residue_polynomial_algebraic p).mul
    (physical_residue_polynomial_algebraic q).inv

theorem physical_algebraic_over_parameters :
    Algebra.IsAlgebraic PhysicalParameterField HoldoutFunctionField :=
  ⟨physical_field_algebraic⟩

theorem physicalParameters_independent : AlgebraicIndependent ℂ physicalParameters := by
  letI := physical_algebraic_over_parameters
  exact coordinates_independent_of_spanning physicalParameters physical_trdeg

theorem physical_parameter_evaluation_injective :
    Function.Injective (MvPolynomial.aeval (R := ℂ) physicalParameters) :=
  physicalParameters_independent

end HoldoutBundle

#print axioms HoldoutBundle.physicalParameters_independent
