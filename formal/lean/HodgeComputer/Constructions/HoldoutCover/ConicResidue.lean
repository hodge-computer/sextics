import HodgeComputer.Constructions.HoldoutCover.ConicEmbedding
import HodgeComputer.Constructions.HoldoutCover.ConicSourceDerivations
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.QuotientDerivatives

/- Source component: ConicResidue -/
section
/-!
The checked generic conic supplies an actual residue primitive on the
weighted quotient. All coefficient, coordinate and tangent compatibility
conditions are discharged for the exact polynomial family, and normalized
trace then returns the primitive to the quotient's own function field.
-/

noncomputable section

namespace HoldoutConicIncidence

open HoldoutConstruction Polynomial
open scoped BigOperators

private theorem map_residue_source {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (a b c d : K) :
    φ (-(a/b-c*d/b^2)) = -(φ a/φ b-φ c*φ d/(φ b)^2) := by
  simp only [map_neg, map_sub, map_div₀, map_mul, map_pow]

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero
attribute [local instance] quotient_adjoinRoot_isDomain quotient_charZero

local instance : Algebra ℤ ConicTargetField := Ring.toIntAlgebra _
local instance (p : HoldoutConic.Seed) : Algebra ℤ (ConicFunctionField p) := Ring.toIntAlgebra _

def conicTargetDerivation (p : HoldoutConic.Seed) (j : Fin 4) :
    Derivation ℤ (ConicFunctionField p) (ConicFunctionField p) :=
  extendFiniteDerivation (L := ConicFunctionField p)
    (quotientTangent genericAlpha genericBeta j)

theorem conicTargetDerivation_apply (p : HoldoutConic.Seed) (j : Fin 4)
    (x : ConicTargetField) :
    conicTargetDerivation p j (algebraMap ConicTargetField (ConicFunctionField p) x) =
      algebraMap ConicTargetField (ConicFunctionField p)
        (quotientTangent genericAlpha genericBeta j x) :=
  extendFiniteDerivation_apply _ x

theorem conic_finiteQuotientEvaluation (p : HoldoutConic.Seed)
    (f : MvPolynomial (Fin 5) FermatBaseField) :
    finiteQuotientEvaluation (K := ConicTargetField) (L := ConicFunctionField p)
      (quotientProjection genericAlpha genericBeta) f = conicFieldEval p f :=
  conicTargetFieldMap_residue p f

theorem conicFieldEval_polynomial (p : HoldoutConic.Seed)
    (f : MvPolynomial (Fin 5) FermatBaseField) :
    conicFieldEval p f =
      algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)
        (MvPolynomial.eval₂Hom
          (Polynomial.C.comp (algebraMap FermatBaseField (ConicCoefficientField p)))
          (conicCurve p) f) := by
  have h :
      (algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)).comp
        (MvPolynomial.eval₂Hom
          (Polynomial.C.comp (algebraMap FermatBaseField (ConicCoefficientField p)))
          (conicCurve p)) = conicFieldEval p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, conicFieldEval]
      rfl
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', conicFieldEval,
        conicFieldCoordinate]
  exact (congrArg (fun φ : MvPolynomial (Fin 5) FermatBaseField →+*
    ConicFunctionField p => φ f) h).symm

theorem conic_gradient_evaluation (p : HoldoutConic.Seed) (j : Fin 5) :
    conicFieldEval p (MvPolynomial.pderiv j (weightedHypersurface genericAlpha genericBeta)) =
      algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)
        (gradient (C (conicAlpha p)) (C (conicBeta p)) (conicCurve p) j) := by
  rw [conicFieldEval_polynomial]
  change algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)
    (MvPolynomial.eval₂Hom
      (Polynomial.C.comp (algebraMap FermatBaseField (ConicCoefficientField p)))
      (conicCurve p) (integerPartial j (weightedHypersurface genericAlpha genericBeta))) = _
  rw [weightedHypersurface_integerPartial_eval₂]
  change algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)
    (gradient (C (algebraMap FermatBaseField (ConicCoefficientField p) genericAlpha))
      (C (algebraMap FermatBaseField (ConicCoefficientField p) genericBeta)) (conicCurve p) j) = _
  simp only [genericAlpha, genericBeta]
  rw [← conicAlpha_base, ← conicBeta_base]

theorem conic_gradient_normal_pairing (p : HoldoutConic.Seed) :
    (∑ j, conicFieldEval p
        (MvPolynomial.pderiv j (weightedHypersurface genericAlpha genericBeta)) *
      algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p)
        (conicNormal p j)) = 1 := by
  have h := congrArg
    (algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p))
    (conicNormal_pairing p)
  simpa only [polynomialPairing, map_sum, map_mul, map_one,
    conic_gradient_evaluation] using h

theorem conic_target_residue_solution (p : HoldoutConic.Seed)
    (A : MvPolynomial (Fin 5) FermatBaseField) :
    ∃ w : Fin 4 → ConicTargetField,
      residueDivergence (quotientTangent genericAlpha genericBeta)
        (quotientResidueMap genericAlpha genericBeta
          (MvPolynomial.pderiv 0 (weightedHypersurface genericAlpha genericBeta))) w =
      -(quotientResidueMap genericAlpha genericBeta (MvPolynomial.pderiv 0 A) /
          quotientResidueMap genericAlpha genericBeta
            (MvPolynomial.pderiv 0 (weightedHypersurface genericAlpha genericBeta)) -
        quotientResidueMap genericAlpha genericBeta A *
          quotientResidueMap genericAlpha genericBeta
            (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0
              (weightedHypersurface genericAlpha genericBeta))) /
          (quotientResidueMap genericAlpha genericBeta
            (MvPolynomial.pderiv 0 (weightedHypersurface genericAlpha genericBeta)))^2) := by
  let π := quotientProjection genericAlpha genericBeta
  let f := weightedHypersurface genericAlpha genericBeta
  let ρ := finiteQuotientEvaluation (K := ConicTargetField) (L := ConicFunctionField p) π
  let χ := algebraMap (ConicCoefficientField p) (ConicFunctionField p)
  let ψ : Fin 5 → ConicFunctionField p := fun j =>
    algebraMap (Polynomial (ConicCoefficientField p)) (ConicFunctionField p) (conicNormal p j)
  have hρ (a : MvPolynomial (Fin 5) FermatBaseField) : ρ a = conicFieldEval p a :=
    conic_finiteQuotientEvaluation p a
  have hρbase (r : FermatBaseField) : ρ (MvPolynomial.C r) =
      algebraMap FermatBaseField (ConicFunctionField p) r := by
    rw [hρ]
    simp [conicFieldEval]
  have hρX (i : Fin 5) : ρ (MvPolynomial.X i) = conicFieldCoordinate p i := by
    rw [hρ]
    simp [conicFieldEval]
  have hf : ρ f = 0 := by
    change algebraMap ConicTargetField (ConicFunctionField p)
      (quotientResidueMap genericAlpha genericBeta f) = 0
    rw [(quotientResidueMap_kernel genericAlpha genericBeta f).mpr (dvd_refl _), map_zero]
  have hg0 : ρ (MvPolynomial.pderiv 0 f) ≠ 0 := by
    change algebraMap ConicTargetField (ConicFunctionField p)
      (quotientResidueMap genericAlpha genericBeta (integerPartial 0 f)) ≠ 0
    exact (_root_.map_ne_zero (algebraMap ConicTargetField (ConicFunctionField p))).2
      (quotient_normal_ne_zero genericAlpha genericBeta)
  have hE (j : Fin 4) (a : MvPolynomial (Fin 5) FermatBaseField) :
      conicTargetDerivation p j (ρ a) = ρ (MvPolynomial.pderiv j.succ a) -
        ρ (MvPolynomial.pderiv j.succ f)/ρ (MvPolynomial.pderiv 0 f)*
          ρ (MvPolynomial.pderiv 0 a) := by
    change conicTargetDerivation p j (algebraMap ConicTargetField (ConicFunctionField p)
      (quotientResidueMap genericAlpha genericBeta a)) = _
    rw [conicTargetDerivation_apply, quotientTangent_apply]
    simp only [map_sub, map_div₀, map_mul, integerPartial_apply]
    rfl
  have hfamily : ∃ w : Fin 4 → ConicFunctionField p,
      residueDivergence (conicTargetDerivation p) (ρ (MvPolynomial.pderiv 0 f)) w =
        -(ρ (MvPolynomial.pderiv 0 A)/ρ (MvPolynomial.pderiv 0 f) -
          ρ A * ρ (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 f)) /
            (ρ (MvPolynomial.pderiv 0 f))^2) := by
    apply residue_solution_from_polynomial_curve (K := ConicTargetField)
      π (quotientProjection_surjective genericAlpha genericBeta) f A
      (conicSourceDerivation p) (conicTargetDerivation p)
      (conicEvaluationMatrix p) ψ χ (curveTime (E := ConicCoefficientField p)) 0
    · exact conicSourceDerivation_time_constant p
    · simp
    · exact hf
    · exact hg0
    · exact conicEvaluationMatrix_det_ne_zero p
    · exact conicEvaluationMatrix_normal p
    · intro k i
      rw [hρX]
      exact conicEvaluationMatrix_tangent p k i
    · simpa only [π, f, ψ, conic_finiteQuotientEvaluation] using
        conic_gradient_normal_pairing p
    · intro i r
      rw [hρbase]
      exact conicSourceDerivation_base p i r
    · exact conicSourceDerivations_commute p
    · exact hE
    · intro r
      rw [hρbase]
      exact conicCoefficient_polynomial p (algebraMap FermatBaseField (ConicCoefficientField p) r)
    · intro i
      rw [hρX]
      exact conicCurve_polynomial p i
    · exact conicNormal_polynomial p
    · exact conicSourceDerivation_eval_range p
  apply residue_solution_descends_finite
    (quotientTangent genericAlpha genericBeta) (conicTargetDerivation p)
    (conicTargetDerivation_apply p)
  obtain ⟨w,hw⟩ := hfamily
  refine ⟨w, ?_⟩
  have hρmap (a : MvPolynomial (Fin 5) FermatBaseField) :
      ρ a = algebraMap ConicTargetField (ConicFunctionField p)
        (quotientResidueMap genericAlpha genericBeta a) := rfl
  simp_rw [hρmap] at hw
  rw [map_residue_source]
  exact hw

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.conic_target_residue_solution
end
end
