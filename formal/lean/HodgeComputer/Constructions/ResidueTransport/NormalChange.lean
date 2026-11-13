import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Changes of normal source and coordinate normal

Replacing a source `h` by `h - c * g`, where `g` is the nonzero normal,
changes the derivative of its normal ratio by `-D c`. In particular a
constant coefficient leaves the complete ratio derivative unchanged.

The source with numerator `B * p * q` can be expressed using the paired
normal `p * f + q * g`, with an explicit residue-divergence correction.
The statement is a field identity with specified tangent derivatives; it
requires neither a hypersurface presentation nor characteristic zero.

The residue-normal transport architecture follows `hodgepodgeconjecture`'s
accepted cyclic cubic construction (PR #165), building on `fqlx` and the
Hodge Computer collaborators' residue framework. This balanced-source
identity was prepared for `benediamond` with OpenAI ChatGPT and Codex
assistance for the mixed-polar construction. Applications supply their
normal and Hessian values, tangent identities and nonvanishing proofs.
The source-ratio identities isolate the elementary normal-source adjustment
used in `fqlx`'s quadratic-shear construction, prepared with OpenAI Codex
assistance.
-/

namespace ResidueNormalChange

variable {K : Type*} [Field K]

/-- Subtracting a multiple of the normal changes the complete source-ratio
derivative by the derivative of that multiple. No constant-coefficient
hypothesis is needed for this identity. -/
lemma normal_source_gauge (D : Derivation ℤ K K) (h c g : K) (hg : g ≠ 0) :
    D ((h - c * g) / g) = D (h / g) - D c := by
  rw [sub_div, mul_div_cancel_right₀ c hg, map_sub]

/-- A coefficient constant for the normal derivation does not change the
complete normal source, including its differentiated denominator. -/
lemma normal_source_gauge_of_constant (D : Derivation ℤ K K) (h c g : K)
    (hg : g ≠ 0) (hc : D c = 0) :
    D ((h - c * g) / g) = D (h / g) := by
  rw [normal_source_gauge D h c g hg, hc, sub_zero]

/-- Change the coordinate normal `f` to the paired normal `p * f + q * g`.
The final summand is `D C - C * D f / f` for
`C = -B * p * q ^ 2 / (p * f + q * g)`. In a hypersurface application,
`f` and `g` are the two coordinate partials, the three `fpp`, `fpq`, `fqq`
are the Hessian entries, and `D` is the tangent derivative in `q`.
The passive factor `B` need only satisfy `D B = 0`. -/
lemma paired_normal_change (D : Derivation ℤ K K)
    (p q B f g fpp fpq fqq : K)
    (hf : f ≠ 0) (hh : p * f + q * g ≠ 0)
    (DB : D B = 0)
    (Dp : D p = -g / f) (Dq : D q = 1)
    (Df : D f = fpq - g / f * fpp) (Dg : D g = fqq - g / f * fpq) :
    B * q / f - B * p * q * fpp / f ^ 2 =
      B * p * q * (3 * (p * f + q * g) -
        (p ^ 2 * fpp + 2 * p * q * fpq + q ^ 2 * fqq)) / (p * f + q * g) ^ 2 +
      (D (-B * p * q ^ 2 / (p * f + q * g)) -
        (-B * p * q ^ 2 / (p * f + q * g)) * D f / f) := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    map_neg, map_add, smul_eq_mul, nsmul_eq_mul, Dp, Dq, Df, Dg, DB]
  generalize hG : p * f + q * g = G at *
  field_simp [hf, hh]
  rw [← hG]
  ring

/-- The same change of normal for the source with numerator `p ^ 3 * q ^ 3`.
The final summand is `D C - C * D f / f` for
`C = -p ^ 3 * q ^ 4 / (p * f + q * g)`. -/
lemma cubed_paired_normal_change (D : Derivation ℤ K K)
    (p q f g fpp fpq fqq : K)
    (hf : f ≠ 0) (hh : p * f + q * g ≠ 0)
    (Dp : D p = -g / f) (Dq : D q = 1)
    (Df : D f = fpq - g / f * fpp) (Dg : D g = fqq - g / f * fpq) :
    3 * p ^ 2 * q ^ 3 / f - p ^ 3 * q ^ 3 * fpp / f ^ 2 =
      p ^ 3 * q ^ 3 * (7 * (p * f + q * g) -
        (p ^ 2 * fpp + 2 * p * q * fpq + q ^ 2 * fqq)) / (p * f + q * g) ^ 2 +
      (D (-p ^ 3 * q ^ 4 / (p * f + q * g)) -
        (-p ^ 3 * q ^ 4 / (p * f + q * g)) * D f / f) := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    map_neg, map_add, smul_eq_mul, nsmul_eq_mul, Dp, Dq, Df, Dg]
  norm_num
  field_simp
  ring

end ResidueNormalChange
