import Proposal.GeometricCurveNormalContraction

/-!
# Independence of the time lift on affine opens of the moving curve

On an affine open of the infinitesimal moving curve, its closed fibre is
obtained by dividing its coordinate ring by epsilon. Two velocities that
evaluate epsilon to one agree on that entire ideal. Their difference
descends to the closed smooth curve, where the exterior square of the
cotangent module vanishes. Consequently the two evaluations agree on
every two-form of the infinitesimal family over this affine open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationOverlap

open scoped DualNumber TensorProduct
open CategoryTheory AlgebraicGeometry
open CycleQ2LiteralAbelJacobiContraction CycleQ2CurveNormalContraction

section Quotient

variable {S C : Type} [CommRing S] [CommRing C] [Algebra ℂ S] [Algebra ℂ C]
  [Algebra S C] [IsScalarTower ℂ S C]

/-- On a common closed curve, the epsilon normalization determines evaluation on every two-form. -/
theorem contract_eq_of_epsilon (e : S) (hs : Function.Surjective (algebraMap S C))
    (hk : RingHom.ker (algebraMap S C) = Ideal.span {e})
    [Subsingleton (⋀[C]^2 (KaehlerDifferential ℂ C))]
    (v w : Derivation ℂ S C) (hv : v e = 1) (hw : w e = 1) :
    contractRestrict v = contractRestrict w := by
  apply contractRestrict_eq_of_normal_eq v w hs
  apply LinearMap.ext
  intro z
  obtain ⟨p, rfl⟩ := (RingHom.ker (algebraMap S C)).toCotangent_surjective z
  rw [normalComponent_equation, normalComponent_equation]
  have he : algebraMap S C e = 0 := (le_of_eq hk.symm) (Ideal.subset_span (Set.mem_singleton e))
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp ((le_of_eq hk) p.property)
  rw [ha, v.leibniz, w.leibniz, Algebra.smul_def e, Algebra.smul_def e, he, zero_mul, zero_mul, hv, hw]

end Quotient

end CycleQ2LiteralAbelJacobiEvaluationOverlap
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationOverlap.contract_eq_of_epsilon
