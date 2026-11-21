import Proposal.GeometricLiteralThreefoldVolumeVariation
import Proposal.GeometricLiteralThreefoldResidueMinors

/-! Directional derivatives in the three independent coordinates on a Jacobian patch.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldVolumeVariationPatch

open Module MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldVolumeVariation

abbrev patchMap (i j : Fin 4) : T i →ₐ[ℂ] Patch i j := IsScalarTower.toAlgHom ℂ _ _
abbrev eval (i j : Fin 4) : P →ₐ[ℂ] Patch i j := (patchMap i j).comp (q i)

def patchPartial (i j : Fin 4) (r : Fin 3) : Derivation ℂ (Patch i j) (Patch i j) :=
  ((basis i j).coord r).compDer (KaehlerDifferential.D ℂ _)

private theorem partial_free (i j : Fin 4) (r s : Fin 3) :
    patchPartial i j r (eval i j (X (coordIndex (j.succAbove s)))) = if s = r then 1 else 0 := by
  change (basis i j).repr (KaehlerDifferential.D ℂ _ _) r = _
  have hb : basis i j s = KaehlerDifferential.D ℂ (Patch i j)
      (eval i j (X (coordIndex (j.succAbove s)))) := basis_apply i j s
  rw [← hb, Basis.repr_self, Finsupp.single_apply]

private theorem chain (i j : Fin 4) (r : Fin 3) (p : P) :
    patchPartial i j r (eval i j p) =
      eval i j (pderiv (coordIndex j) p) * patchPartial i j r (eval i j (X (coordIndex j))) +
      eval i j (pderiv (coordIndex (j.succAbove r)) p) := by
  have h := congrArg ((basis i j).coord r) (differential_polynomial (eval i j) p)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  change patchPartial i j r (eval i j p) =
    ∑ l : Index, eval i j (pderiv l p) * patchPartial i j r (eval i j (X l)) at h
  rw [← Equiv.sum_comp coordIndex, Fin.sum_univ_succAbove _ j] at h
  simp_rw [partial_free] at h
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true] using h

/-- The intrinsic derivative in a retained coordinate, with denominators cleared. -/
theorem partial_scaled (i j : Fin 4) (r : Fin 3) (p : P) :
    eval i j (pderiv (coordIndex j) (seedF i)) * patchPartial i j r (eval i j p) =
      eval i j (pderiv (coordIndex j) (seedF i) * pderiv (coordIndex (j.succAbove r)) p -
        pderiv (coordIndex j) p * pderiv (coordIndex (j.succAbove r)) (seedF i)) := by
  have hF : eval i j (seedF i) = 0 := by
    change patchMap i j (q i (seedF i)) = 0
    rw [show q i (seedF i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _)), map_zero]
  have hc := chain i j r (seedF i)
  rw [hF, map_zero] at hc
  rw [chain i j r p, map_sub, map_mul, map_mul]
  linear_combination -(eval i j (pderiv (coordIndex j) p)) * hc

/-- Sum the intrinsic diagonal derivatives of the velocities in the true canonical
jet. The omitted-pivot summand of the ambient cofactor formula is zero. -/
theorem canonical_trace_scaled {i : Fin 4} {V : Index → P} (hV : Represents i V) (j : Fin 4) :
    eval i j (pderiv (coordIndex j) (seedF i)) *
      (∑ r, patchPartial i j r (((canonical i (patchMap i j)).x (coordIndex (j.succAbove r))).snd)) =
    eval i j (∑ l, (pderiv (coordIndex j) (seedF i) * pderiv l (V l) -
      pderiv (coordIndex j) (V l) * pderiv l (seedF i))) := by
  have hvel (l : Index) : ((canonical i (patchMap i j)).x l).snd = eval i j (V l) :=
    congrArg (patchMap i j) (hV l).symm
  simp_rw [hvel]
  rw [Finset.mul_sum, ← Equiv.sum_comp coordIndex, Fin.sum_univ_succAbove _ j, map_add,
    map_sum]
  rw [show pderiv (coordIndex j) (seedF i) * pderiv (coordIndex j) (V (coordIndex j)) -
    pderiv (coordIndex j) (V (coordIndex j)) * pderiv (coordIndex j) (seedF i) = 0 by ring,
    map_zero, zero_add]
  exact Finset.sum_congr rfl fun r _ => partial_scaled i j r _

/-- The trace of the actual three chart velocities differs from the corrected
volume coefficient precisely by the logarithmic variation of the pivot gradient. -/
theorem canonical_trace {i : Fin 4} {V : Index → P} {H : P}
    (hV : Represents i V) (hH : IsMultiplier i V H) (j : Fin 4)
    (h : IsUnit (patchMap i j (gradient i j))) :
    (∑ r, patchPartial i j r (((canonical i (patchMap i j)).x (coordIndex (j.succAbove r))).snd)) =
      patchMap i j (residueCoefficient i V H) +
        (↑h.unit⁻¹ : Patch i j) * patchMap i j ((gradientJet i (coordIndex j)).snd) := by
  have hc := congrArg (patchMap i j) (cofactor_variation hV hH (coordIndex j))
  simp only [map_add, map_mul] at hc
  have hs := canonical_trace_scaled hV j
  have he := hs.trans hc.symm
  change patchMap i j (gradient i j) * _ =
    patchMap i j (gradient i j) * _ + _ at he
  have mul_inv : (↑h.unit⁻¹ : Patch i j) * patchMap i j (gradient i j) = 1 := h.val_inv_mul
  have hmul := congrArg ((↑h.unit⁻¹ : Patch i j) * ·) he
  simpa only [mul_add, ← mul_assoc, mul_inv, one_mul] using hmul

end CycleQ2LiteralThreefoldVolumeVariationPatch
end
