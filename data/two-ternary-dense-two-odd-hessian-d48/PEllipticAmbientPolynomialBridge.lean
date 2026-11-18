import Proposal.PEllipticAmbientHomogeneousRules

/-! Recover the protected polynomial equations from genuine rational derivative identities. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.FrozenChart HodgeTestbed.Conic
open scoped BigOperators

variable (D F : Poly 6) (N : Fin 6 → Poly 6)

theorem ratio_contraction : fieldAction rationalPartial (fun i => embed (N i)/embed D) (embed F) =
    embed (directional F N)/embed D := by
  simp only [fieldAction_apply, directional, map_sum, map_mul, partial_embed]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem ratio_divergence (hD : D ≠ 0) :
    fieldDivergence rationalPartial (fun i => embed (N i)/embed D) =
      embed (divergenceNumerator D N)/(embed D)^2 := by
  have hd : embed D ≠ 0 := by intro hh; apply hD; exact embed_injective (by simpa using hh)
  simp only [fieldDivergence, Derivation.leibniz_div, smul_eq_mul, partial_embed,
    divergenceNumerator, divergence, directional, map_sub, map_mul, map_sum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem equations_of_rational_field (A C : Poly 6) (hD : D ≠ 0) (v : Fin 6 → K6)
    (hv : ∀ i, v i = embed (N i)/embed D)
    (hfirst : fieldAction rationalPartial v (embed F) = embed A)
    (hdiv : fieldDivergence rationalPartial v = embed F*embed C/(embed D)^2) :
    Equations F A D N C := by
  have hd : embed D ≠ 0 := by intro hh; apply hD; exact embed_injective (by simpa using hh)
  have he : v = fun i => embed (N i)/embed D := funext hv
  rw [he, ratio_contraction] at hfirst
  rw [he, ratio_divergence D N hD] at hdiv
  constructor
  · apply embed_injective
    rw [map_mul]
    exact (div_eq_iff hd).mp hfirst
  · apply embed_injective
    rw [map_mul]
    exact (div_left_inj₀ (pow_ne_zero 2 hd)).mp hdiv

end HodgeTestbed.EllipticAmbient
