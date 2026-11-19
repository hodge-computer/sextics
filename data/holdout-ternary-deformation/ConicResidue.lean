import Proposal.ConicTransport
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace

/-!
Polynomial integration on the replacement conic, followed by normalized
finite trace, yields a residue primitive on the deformed weighted quotient.
This is an application of fqlx's shared polynomial-family and finite-trace
theorems to the exact new family. Prepared with OpenAI Codex assistance
for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open HoldoutConstruction Polynomial
local instance conicResidue_local_1 : Algebra ℤ TargetField := Ring.toIntAlgebra _
local instance conicResidue_local_2 : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def targetTangent (i : Fin 4) : Derivation ℤ TargetField TargetField :=
  DeformedGeometry.quotientTangent (14⁻¹) baseFieldAlpha baseFieldBeta i
def targetDerivation (i : Fin 4) : Derivation ℤ FunctionField FunctionField :=
  extendFiniteDerivation (targetTangent i)
lemma targetDerivation_apply (i : Fin 4) (x : TargetField) :
    targetDerivation i (algebraMap TargetField FunctionField x)=
      algebraMap TargetField FunctionField (targetTangent i x) :=
  extendFiniteDerivation_apply _ x
lemma targetTangent_apply (i : Fin 4) (p : MvPolynomial (Fin 5) BaseField) :
    targetTangent i (targetResidueMap p)=
      targetResidueMap (integerPartial i.succ p)-
        targetResidueMap (integerPartial i.succ quotientEquation)/
          targetResidueMap (integerPartial 0 quotientEquation)*targetResidueMap (integerPartial 0 p) :=
  DeformedGeometry.quotientTangent_apply _ _ _ i p
lemma target_normal_ne_zero : targetResidueMap (integerPartial 0 quotientEquation) ≠ 0 :=
  DeformedGeometry.quotient_normal_ne_zero _ _ _

theorem quotient_residue_solution (A : MvPolynomial (Fin 5) BaseField) :
    ∃ w : Fin 4 → TargetField,
      residueDivergence targetTangent (targetResidueMap (integerPartial 0 quotientEquation)) w=
        -(targetResidueMap (integerPartial 0 A)/targetResidueMap (integerPartial 0 quotientEquation)-
          targetResidueMap A*targetResidueMap (integerPartial 0 (integerPartial 0 quotientEquation))/
            (targetResidueMap (integerPartial 0 quotientEquation))^2) := by
  let ρ := finiteQuotientEvaluation (K := TargetField) (L := FunctionField) targetProjection
  let χ := algebraMap CoefficientField FunctionField
  have hρ (p : MvPolynomial (Fin 5) BaseField) : ρ p=fieldEval p := finiteQuotientEvaluation_eq p
  have hρX (i : Fin 5) : ρ (MvPolynomial.X i)=fieldCoordinate i := by
    rw [hρ]
    simp [fieldEval]
  have hρC (r : BaseField) : ρ (MvPolynomial.C r)=algebraMap BaseField FunctionField r := by
    rw [hρ]
    simp [fieldEval]
  have hρmap (p : MvPolynomial (Fin 5) BaseField) :
      ρ p=algebraMap TargetField FunctionField (targetResidueMap p) := rfl
  have hf : ρ quotientEquation=0 := by
    rw [hρmap]
    have hz : targetResidueMap quotientEquation=0 :=
      (DeformedGeometry.quotientResidueMap_kernel (14⁻¹) baseFieldAlpha baseFieldBeta _).mpr (dvd_refl _)
    rw [hz,map_zero]
  have hg : ρ (integerPartial 0 quotientEquation) ≠ 0 := by
    rw [hρmap]
    exact (map_ne_zero (algebraMap TargetField FunctionField)).mpr target_normal_ne_zero
  have hE (j : Fin 4) (p : MvPolynomial (Fin 5) BaseField) :
      targetDerivation j (ρ p)=ρ (MvPolynomial.pderiv j.succ p)-
        ρ (MvPolynomial.pderiv j.succ quotientEquation)/ρ (MvPolynomial.pderiv 0 quotientEquation)*
          ρ (MvPolynomial.pderiv 0 p) := by
    simp only [hρmap,targetDerivation_apply,targetTangent_apply,map_sub,map_div₀,map_mul,
      integerPartial_apply]
  have hfamily : ∃ w : Fin 4 → FunctionField,
      residueDivergence targetDerivation (ρ (integerPartial 0 quotientEquation)) w=
        -(ρ (integerPartial 0 A)/ρ (integerPartial 0 quotientEquation)-
          ρ A*ρ (integerPartial 0 (integerPartial 0 quotientEquation))/
            (ρ (integerPartial 0 quotientEquation))^2) := by
    apply residue_solution_from_polynomial_curve (K := TargetField) targetProjection
      (DeformedGeometry.quotientProjection_surjective _ _ _) quotientEquation A
      sourceDerivation targetDerivation quotientEvaluationMatrix quotientNormal
      χ (curveTime (E := CoefficientField)) 0
    · exact sourceDerivation_time_constant
    · exact sourceDerivation_time
    · exact hf
    · exact hg
    · exact quotientEvaluationMatrix_det_ne_zero
    · intro i; rfl
    · intro i j
      rw [hρX]
      change algebraMap (Polynomial CoefficientField) FunctionField
        (polynomialDerivation j (conicCurve i))=
          sourceDerivation j (algebraMap (Polynomial CoefficientField) FunctionField (conicCurve i))
      exact (sourceDerivation_polynomial j _).symm
    · simpa only [finiteQuotientEvaluation_eq,integerPartial_apply] using quotientNormal_pairing
    · intro j r
      rw [hρC]
      exact sourceDerivation_baseField j r
    · exact sourceDerivations_commute
    · exact hE
    · intro r
      rw [hρC,curvePolynomial_eval₂]
      exact ⟨C (algebraMap BaseField CoefficientField r),rfl⟩
    · intro i
      rw [hρX,curvePolynomial_eval₂]
      exact ⟨conicCurve i,rfl⟩
    · intro i
      rw [curvePolynomial_eval₂]
      refine ⟨14*conicNormal i,?_⟩
      simp only [map_mul,map_ofNat,quotientNormal]
    · intro i x hx
      rw [curvePolynomial_eval₂] at hx ⊢
      exact extendRingDerivation_mem_range (polynomialDerivation i) x hx
  apply residue_solution_descends_finite targetTangent targetDerivation targetDerivation_apply
  obtain ⟨w,hw⟩ := hfamily
  refine ⟨w,?_⟩
  simp only [hρmap] at hw
  simpa only [map_neg,map_sub,map_div₀,map_mul,map_pow] using hw

end DeformedConic
#print axioms DeformedConic.quotient_residue_solution
