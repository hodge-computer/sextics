import Proposal.GeometricGenericWeightedDivergence
import Proposal.GeometricGenericWeightedSource

/-!
# Weighted relative primitives on the actual deformed function field

In the double-cover coordinates, the fixed-parameter residue density of the
protected numerator is λ times the weighted density. Transferring a weighted
primitive in the three fibre directions gives its four-coordinate primitive.
Laurent specialization then yields an exterior primitive of the protected
residue on the original, undeformed hypersurface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedTransfer

open HodgeComputer CycleQ2GenericSpecialization CycleQ2GenericWeightedCoordinates
  CycleQ2GenericWeightedDivergence CycleQ2GenericWeightedSource CycleQ2AffineClearing
open CycleQ2AffineWeightedTransfer (weightedSource)
open scoped BigOperators

/-- The normal derivative of the deformed equation at fixed deformation parameter. -/
abbrev normal (d : Direction) : RF := familyNormalJet d 0

theorem normal_ne_zero (d : Direction) : normal d ≠ 0 :=
  familyPartial_zero_ne_zero d

/-- The signed residue-primitive equation in the three weighted directions. -/
def relativeResidueExpression (d : Direction) (w : Fin 3 → RF) : RF :=
  normal d * genericDensity d weightedSource +
    ((∑ j, relativeDerivation d j (w j)) -
      (∑ j, w j * relativeDerivation d j (normal d)) / normal d)

/-- The corresponding equation for the four tangent directions of the generic hypersurface. -/
def residueExpression (d : Direction) (A : Poly) (v : Fin 4 → RF) : RF :=
  normal d * genericDensity d A +
    ((∑ j, tangent d j (v j)) - (∑ j, v j * tangent d j (normal d)) / normal d)

theorem generic_residue_transfer (d : Direction) (w : Fin 3 → RF) :
    residueExpression d affineA (transferVector w) = lambda * relativeResidueExpression d w := by
  rw [residueExpression, relativeResidueExpression, genericDensity_source_ratio,
    transferred_density_divergence]
  ring

/-- A three-variable weighted primitive yields the four-variable primitive of the actual
protected numerator, in the field of the deformed hypersurface. -/
theorem generic_primitive_of_weighted_primitive (d : Direction)
    (hp : ∃ v : Fin 3 → RF, ∑ j, relativeDerivation d j (v j) = genericDensity d weightedSource) :
    ∃ w : Fin 4 → RF, ∑ i, tangent d i (w i) = genericDensity d affineA := by
  obtain ⟨v, hv⟩ := hp
  exact ⟨transferVector v, by rw [transferred_divergence, hv, genericDensity_source_ratio]⟩

theorem weighted_primitive_iff (d : Direction) :
    (∃ w : Fin 3 → RF, relativeResidueExpression d w = 0) ↔
      ∃ v : Fin 3 → RF, ∑ j, relativeDerivation d j (v j) = genericDensity d weightedSource := by
  let n := normal d
  have hn : n ≠ 0 := normal_ne_zero d
  have calc_div (w : Fin 3 → RF) :
      relativeResidueExpression d w =
        n * (genericDensity d weightedSource + ∑ j, relativeDerivation d j (w j / n)) := by
    have hc : (∑ j, relativeDerivation d j (w j)) -
          (∑ j, w j * relativeDerivation d j n) / n =
        n * ∑ j, relativeDerivation d j (w j / n) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Derivation.leibniz_div]
      simp only [smul_eq_mul]
      field_simp [hn]
    exact (congrArg (n * genericDensity d weightedSource + ·) hc).trans (mul_add ..).symm
  constructor
  · rintro ⟨w, hw⟩
    rw [calc_div] at hw
    have hz := (mul_eq_zero.mp hw).resolve_left hn
    refine ⟨fun j => -(w j / n), ?_⟩
    simp only [map_neg, Finset.sum_neg_distrib]
    exact (eq_neg_of_add_eq_zero_left hz).symm
  · rintro ⟨v, hv⟩
    refine ⟨fun j => -v j * n, ?_⟩
    rw [calc_div]
    simp only [mul_div_cancel_right₀ _ hn, map_neg, Finset.sum_neg_distrib, hv, add_neg_cancel, mul_zero]

/-- Specializing a rational weighted primitive gives exactness of the original protected
exterior four-form, allowing Laurent poles in the deformation parameter. -/
theorem exact_form_of_weighted_primitive (d : Direction)
    (hp : ∃ v : Fin 3 → RF, ∑ j, relativeDerivation d j (v j) = genericDensity d weightedSource) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  (CycleQ2AffineExactness.exact_residueSourceForm_iff affineA).mpr
    (affine_primitive_of_generic_primitive d affineA (generic_primitive_of_weighted_primitive d hp))

theorem exact_form_of_relative_primitive (d : Direction)
    (hp : ∃ w : Fin 3 → RF, relativeResidueExpression d w = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA :=
  exact_form_of_weighted_primitive d ((weighted_primitive_iff d).mp hp)

theorem protected_certificate_of_relative_primitive (d : Direction)
    (hp : ∃ w : Fin 3 → RF, relativeResidueExpression d w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (exact_form_of_relative_primitive d hp)

end CycleQ2GenericWeightedTransfer
end

#print axioms CycleQ2GenericWeightedTransfer.generic_residue_transfer
#print axioms CycleQ2GenericWeightedTransfer.exact_form_of_weighted_primitive
#print axioms CycleQ2GenericWeightedTransfer.protected_certificate_of_relative_primitive
