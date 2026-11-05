import Proposal.TargetEmbedding
import Proposal.QuarticSource
import Proposal.QuotientGradient
import Proposal.CurveClosure
import Proposal.ReflectionLift

/-!
Closing the geometric argument from an actual finite quartic family.
Dominance supplies the finite extension of the target function field;
the polynomial normal and commuting source derivations supply integration.
Finite trace and denominator clearing produce normalized quotient data.
Reflection pullback and homogeneous extraction then yield the exact
pole-order-one certificate for the physical sextic.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace ReflectionCoupledFano
open Polynomial HoldoutConstruction
open scoped BigOperators

attribute [local irreducible] Endpoint.polynomial polynomial

variable {c : ℂ} {E : Type} [Field E]
variable [Algebra ℂ E] [Algebra (Endpoint.Field c) E]
variable [IsScalarTower ℂ (Endpoint.Field c) E]

def QuarticFamily.anchoredFamily (p : QuarticFamily c E) : Target.AnchoredFamily c E where
  curve := p.curve
  constant := p.curve_constant
  equation := p.curve_equation
  moves := p.curve_one_ne_zero

/-- All geometric and differential consequences needed by the certificate
are obtained from the lifted family, with finite coefficient extension
retained as an explicit hypothesis. -/
theorem quotient_normalized_of_quartic_family
    [Module.Finite (Endpoint.Field c) E] (p : QuarticFamily c E) :
    ∃ d : HodgeComputer.Poly, ∃ N : Fin 6 → HodgeComputer.Poly,
      ∃ Q : HodgeComputer.Poly,
        d ≠ 0 ∧ IsRelPrime (hypersurface c 3 1) d ∧
        HodgeTestbed.directional (hypersurface c 3 1) N = quotientSource * d ∧
        HodgeTestbed.divergenceNumerator d N = hypersurface c 3 1 * Q := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  let a := p.anchoredFamily
  letI := a.targetAlgebra
  letI := a.baseTower
  letI := a.functionField_finite
  let ρ := finiteQuotientEvaluation (K := Target.Field c)
    (L := CurveFunctionField E) (Target.projection c)
  have hρ (f : HodgeComputer.Poly) :
      ρ f = MvPolynomial.eval₂Hom (algebraMap ℂ (CurveFunctionField E))
        (fun i => algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i)) f := by
    exact a.fieldMap_residue f
  have hρX (i : Fin 6) : ρ (MvPolynomial.X i) =
      algebraMap (Polynomial E) (CurveFunctionField E) (p.curve i) := by
    rw [hρ]
    simp
  have hρC (r : ℂ) : ρ (MvPolynomial.C r) =
      algebraMap E (CurveFunctionField E) (algebraMap ℂ E r) := by
    rw [hρ, MvPolynomial.eval₂Hom_C]
    rfl
  have hρgrad (i : Fin 6) : ρ (MvPolynomial.pderiv i (hypersurface c 3 1)) =
      algebraMap (Polynomial E) (CurveFunctionField E)
        (gradient (Polynomial.C (algebraMap ℂ E c)) p.curve i) := by
    rw [hρ, hypersurface_pderiv_eval, gradient_map]
    rfl
  apply normalized_data_from_polynomial_family
    (K := Target.Field c) (L := CurveFunctionField E)
    (Target.projection c) (Target.projection_surjective c)
    (hypersurface c 3 1) quotientSource
    (weighted_quotient_irreducible c) (Target.projection_kernel c)
    (Target.normal_ne_zero c)
    p.sourceDerivation p.evaluationMatrix
    (fun i => algebraMap (Polynomial E) (CurveFunctionField E) (p.normal i))
    (algebraMap E (CurveFunctionField E)) (curveTime (E := E)) 0
  · exact p.sourceDerivation_time_constant
  · simpa using p.sourceDerivation_time 0
  · exact p.evaluationMatrix_det_ne_zero
  · exact p.evaluationMatrix_normal
  · intro k i
    change p.evaluationMatrix k i.succ = p.sourceDerivation i (ρ (MvPolynomial.X k))
    rw [hρX]
    exact p.evaluationMatrix_tangent k i
  · change (∑ j, ρ (MvPolynomial.pderiv j (hypersurface c 3 1)) *
        algebraMap (Polynomial E) (CurveFunctionField E) (p.normal j)) = 1
    simp_rw [hρgrad]
    exact p.normal_field_pairing
  · intro i r
    change p.sourceDerivation i (ρ (MvPolynomial.C r)) = 0
    rw [hρC]
    exact p.sourceDerivation_base i r
  · exact p.sourceDerivations_commute
  · intro r
    change ρ (MvPolynomial.C r) ∈ _
    rw [hρC]
    exact QuarticFamily.coefficient_polynomial (algebraMap ℂ E r)
  · intro i
    change ρ (MvPolynomial.X i) ∈ _
    rw [hρX]
    exact p.curve_polynomial i
  · exact p.normal_polynomial
  · exact p.sourceDerivation_eval_range

/-- The finite quartic family yields a homogeneous certificate for the
physical equation with its exact reflected numerator. -/
theorem physical_certificate_of_quartic_family
    [Module.Finite (Endpoint.Field c) E] (p : QuarticFamily c E) :
    HodgeComputer.HasCertificate (hypersurface c 6 2) physicalSource 1 := by
  obtain ⟨d, N, Q, _, hlegal, hnormal, hdiv⟩ := quotient_normalized_of_quartic_family p
  obtain ⟨hlegal', hnormal', hdiv'⟩ :=
    reflection_normalized_data c d Q N hlegal hnormal hdiv
  exact hasCertificate_of_normalized (hypersurface c 6 2) physicalSource
    (squareLast d) (liftNumerators N) (MvPolynomial.X 5 * squareLast Q)
    (physical_isHomogeneous c) physicalSource_isHomogeneous
    (physical_irreducible c).prime hlegal' hnormal' hdiv' 0
    (hypersurface_not_dvd_pderiv_zero c 6 2 (by decide))

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.quotient_normalized_of_quartic_family
#print axioms ReflectionCoupledFano.physical_certificate_of_quartic_family
