import Proposal.PEllipticAmbientSplit

/-! # Four-variable operator and the full ambient F-multiple

The normal independence premise on B0 will be discharged for the explicit
embedding QQ(x,y,r,z) → QQ(x,y,r,z,λ) in the following module.
-/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.EllipticAmbient
open HodgeTestbed.Conic HodgeTestbed.FrozenChart
open scoped BigOperators

def dp (B : Fin 4 → K) : K := fieldAction basePartial B p
def dq (B : Fin 4 → K) : K := fieldAction basePartial B q
/-- The weighted four-variable primitive operator. -/
def L4 (B : Fin 4 → K) : K :=
  fieldDivergence basePartial B - dp B / (3 * p) + dq B / (3 * q)
/-- The rescaled scalar equation, with target exactly one. -/
def LW (W : Fin 4 → K) : K :=
  fieldDivergence basePartial W - 4 * dp W / (3 * p) - 2 * dq W / (3 * q)
def scaledB (B : Fin 4 → K) (i : Fin 4) : K := B i / lambda ^ 2
def liftBase (B : Fin 4 → K) : Fin 4 → K := baseField h density (scaledB B)
def liftNormal (B : Fin 4 → K) : K := normalField basePartial splitF lambda h density (scaledB B)
def liftDivergence (B : Fin 4 → K) : K :=
  volumeDivergence basePartial normalPartial density (liftBase B) (liftNormal B)

theorem lifted_first (B : Fin 4 → K) :
    ambientAction basePartial normalPartial (liftBase B) (liftNormal B) splitF = lambda :=
  ambient_first _ _ _ _ _ _ _ h_ne_zero density_ne_zero normal_splitF

/-- A component calculation retains the term lost by restricting prematurely to F=0. -/
theorem tangent_scaled_component (B : Fin 4 → K)
    (hind : ∀ i, normalPartial (B i) = 0) (i : Fin 4) :
    tangent basePartial normalPartial splitF h i (scaledB B i) =
      basePartial i (B i) / lambda ^ 2 - B i * basePartial i p / (3 * p * lambda ^ 2) +
      B i * basePartial i q / (3 * q * lambda ^ 2) +
      splitF * (B i * basePartial i p) / (3 * p * q * lambda ^ 8) := by
  simp only [tangent_apply, scaledB, Derivation.leibniz_div, Derivation.leibniz_pow,
    smul_eq_mul, hind, base_lambda, normal_lambda, base_splitF]
  norm_num
  unfold splitF h
  field_simp [lambda_ne_zero, p_ne_zero, q_ne_zero]
  <;> ring

/-- Exact four-variable reduction before passing to the hypersurface. -/
theorem tangent_scaled (B : Fin 4 → K) (hind : ∀ i, normalPartial (B i) = 0) :
    fieldDivergence (tangent basePartial normalPartial splitF h) (scaledB B) =
      L4 B / lambda ^ 2 + splitF * dp B / (3 * p * q * lambda ^ 8) := by
  simp only [fieldDivergence, tangent_scaled_component B hind, L4, dp, dq,
    fieldAction_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The normal residue density has its own F-multiple correction. -/
theorem residue_density_full : normalPartial (density * lambda / h) / h =
    1 / (18 * p * q * lambda ^ 2) - splitF / (18 * p * q ^ 2 * lambda ^ 8) := by
  rw [residue_density]
  unfold splitF
  field_simp [lambda_ne_zero, p_ne_zero, q_ne_zero]
  <;> ring

/-- Full reviewed ambient divergence defect; the scalar equation is not assumed. -/
theorem lifted_divergence_full (B : Fin 4 → K)
    (hind : ∀ i, normalPartial (B i) = 0) :
    liftDivergence B =
      6 * lambda * q * (1 / (18 * p * q) - L4 B) -
      splitF * (1 + 6 * q * dp B) / (3 * p * q * lambda ^ 5) := by
  change volumeDivergence basePartial normalPartial density (baseField h density (scaledB B))
    (normalField basePartial splitF lambda h density (scaledB B)) = _
  rw [ambient_divergence basePartial normalPartial splitF lambda h density (scaledB B)
    h_ne_zero density_ne_zero normal_splitF (fun i => rationalPartial_commute i.castSucc 4)]
  rw [residue_density_full, tangent_scaled B hind]
  unfold h density
  field_simp [lambda_ne_zero, p_ne_zero, q_ne_zero]
  <;> ring

/-- A supplied primitive solves only the displayed ambient divisibility identity. -/
theorem lifted_divergence_of_primitive (B : Fin 4 → K)
    (hind : ∀ i, normalPartial (B i) = 0) (hprimitive : L4 B = 1 / (18 * p * q)) :
    liftDivergence B = -splitF * (1 + 6 * q * dp B) / (3 * p * q * lambda ^ 5) := by
  rw [lifted_divergence_full B hind, hprimitive]
  ring

/-- Exact rescaling of the differential operator, including derivatives of p and q. -/
theorem LW_scale (B : Fin 4 → K) :
    LW (fun i => (18 * p * q) * B i) = (18 * p * q) * L4 B := by
  have c18 : fieldAction basePartial B (18 : K) = 0 := (fieldAction basePartial B).map_natCast 18
  simp only [LW, L4, dp, dq, fieldDivergence_scale, fieldAction_scale,
    Derivation.leibniz, smul_eq_mul, c18]
  field_simp [p_ne_zero, q_ne_zero]
  <;> ring

/-- The input scalar equation may be supplied in either reviewed normalization. -/
theorem primitive_iff_rescaled (B : Fin 4 → K) :
    L4 B = 1 / (18 * p * q) ↔ LW (fun i => (18 * p * q) * B i) = 1 := by
  rw [LW_scale]
  have hn : (18 : K) * p * q ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) p_ne_zero) q_ne_zero
  constructor
  · intro hh
    rw [hh]
    field_simp [p_ne_zero, q_ne_zero]
  · intro hh
    apply (eq_div_iff hn).mpr
    simpa [mul_comm] using hh

end HodgeTestbed.EllipticAmbient
