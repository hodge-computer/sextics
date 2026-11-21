import Proposal.GeometricLiteralAmbientChartJacobian
import Proposal.GeometricLiteralThreefoldResidueMinors

/-!
# A regular three-form on the entire fixed sextic chart

A Bézout identity for the four partial derivatives assembles the signed
coordinate wedges into one regular three-form on the affine chart. Its
restriction to any gradient open is the normalized hypersurface residue.
The equations for all four gradients uniquely characterize the form after
every complex-algebra restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldChartVolume

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientChartJacobian
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap

/-- A partition of one written in the order of the affine coordinates. -/
theorem chartBezout (i : Fin 4) : ∃ c : Fin 4 → T i, ∑ j, c j * gradient i j = 1 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp (derivatives_span_top i))
  refine ⟨fun j => c (coordIndex j), ?_⟩
  exact (Equiv.sum_comp coordIndex (fun j => c j * derivative i j)).trans hc

private def coefficient (i : Fin 4) := Classical.choose (chartBezout i)

private theorem coefficient_identity (i : Fin 4) : ∑ j, coefficient i j * gradient i j = 1 :=
  Classical.choose_spec (chartBezout i)

/-- The regular affine hypersurface residue, without inverting a gradient. -/
def chartVolume (i : Fin 4) : ⋀[T i]^3 (KaehlerDifferential ℂ (T i)) :=
  ∑ j, coefficient i j • signedOmitted (T i) (coordinateForm i (AlgHom.id ℂ (T i))) j

variable {S : Type} [CommRing S] [Algebra ℂ S]

private theorem map_coefficient_identity (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    ∑ j, f (coefficient i j) * f (gradient i j) = 1 := by
  simpa only [map_sum, map_mul, map_one] using congrArg f (coefficient_identity i)

private theorem map_signedOmitted (i : Fin 4) (f : T i →ₐ[ℂ] S) (j : Fin 4) :
    exteriorDifferentialMap f 3 (signedOmitted (T i) (coordinateForm i (AlgHom.id ℂ (T i))) j) =
      signedOmitted S (coordinateForm i f) j := by
  rw [signedOmitted, map_smulₛₗ, exteriorDifferentialMap_wedge]
  simp only [RingHom.map_pow, map_neg, map_one]
  unfold signedOmitted coordinateForm
  simp only [Function.comp_apply, differentialMap_D, AlgHom.id_apply]
  rfl

/-- Multiplying the restricted volume by any chart partial recovers its
signed omitted-coordinate wedge, even when that partial is a zero divisor. -/
theorem gradient_smul_chartVolume (i : Fin 4) (f : T i →ₐ[ℂ] S) (k : Fin 4) :
    f (gradient i k) • exteriorDifferentialMap f 3 (chartVolume i) =
      signedOmitted S (coordinateForm i f) k := by
  let z := signedOmitted S (coordinateForm i f)
  have hdiff (j : Fin 4) : f (gradient i k) • z j = f (gradient i j) • z k :=
    signedOmitted_cross _ _ (gradient_relation i f) j k
  rw [chartVolume, map_sum]
  simp only [map_smulₛₗ, map_signedOmitted, Finset.smul_sum]
  change ∑ j, f (gradient i k) • (f (coefficient i j) • z j) = z k
  calc
    _ = ∑ j, (f (coefficient i j) * f (gradient i j)) • z k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_comm (f (gradient i k)), hdiff, mul_smul]
    _ = z k := by rw [← Finset.sum_smul, map_coefficient_identity, one_smul]

/-- The gradient equations determine the restriction uniquely. -/
theorem chartVolume_unique (i : Fin 4) (f : T i →ₐ[ℂ] S)
    (ω : ⋀[S]^3 (KaehlerDifferential ℂ S))
    (hω : ∀ j, f (gradient i j) • ω = signedOmitted S (coordinateForm i f) j) :
    ω = exteriorDifferentialMap f 3 (chartVolume i) := by
  let v := exteriorDifferentialMap f 3 (chartVolume i)
  calc
    ω = (∑ j, f (coefficient i j) * f (gradient i j)) • ω := by
      rw [map_coefficient_identity, one_smul]
    _ = (∑ j, f (coefficient i j) * f (gradient i j)) • v := by
      simp only [Finset.sum_smul, mul_smul]
      exact Finset.sum_congr rfl fun j _ =>
        congrArg (fun x => f (coefficient i j) • x)
          ((hω j).trans (gradient_smul_chartVolume i f j).symm)
    _ = _ := by rw [map_coefficient_identity, one_smul]

theorem chartVolume_eq_residue (i : Fin 4) (f : T i →ₐ[ℂ] S) (j : Fin 4)
    (hj : IsUnit (f (gradient i j))) :
    exteriorDifferentialMap f 3 (chartVolume i) = residue i f j hj :=
  (IsUnit.smul_left_cancel hj).mp ((gradient_smul_chartVolume i f j).trans
    (gradient_smul_residue i f j hj).symm)

theorem chartVolume_on_patch (i j : Fin 4) :
    exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) 3 (chartVolume i) =
      patchResidue i j :=
  chartVolume_eq_residue i _ j _

end CycleQ2LiteralThreefoldChartVolume

end

#print axioms CycleQ2LiteralThreefoldChartVolume.gradient_smul_chartVolume
#print axioms CycleQ2LiteralThreefoldChartVolume.chartVolume_unique
#print axioms CycleQ2LiteralThreefoldChartVolume.chartVolume_on_patch
