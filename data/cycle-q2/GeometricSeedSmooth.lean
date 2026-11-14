import Proposal.GeometricTarget02Part03

/-!
# A nonsingular member of the actual fixed-parameter seed family

Source-only continuation of the written geometric proof. This file has not
been elaborated or compiled in this pass.

The polynomial family below contains the existing incidence seed exactly:
specializing its cubic parameter to `CycleQ2IncidenceEquations.smoothB`
gives `smoothF r Complex.I`. At the zero cubic, an explicit calculation
shows that the five partial derivatives have no common nonzero zero when
`r ^ 3` is different from both zero and four. In particular this holds for
the literal complex parameter `r = 57` used by the existing incidence
rank calculation, as well as for the written proof's `r ^ 3 = 2` seed.

This is a witness in the full, unnormalized invariant-cubic parameter
space. The zero cubic is not asserted to belong to the normalized chart
where the leading coefficient of the cubic section is one. Passing to a
nonempty geometric smooth open, intersecting that open with the rank
open, and interpreting the gradient condition through the projective
Jacobian criterion remain separate steps.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricSeedSmooth

open MvPolynomial

abbrev SeedPolynomial := MvPolynomial (Fin 5) ℂ

/-- The same factorized seed equation, with its invariant cubic allowed
to vary. The fixed parameter `r` is not required to satisfy `r ^ 3 = 2`. -/
def seedFamily (r : ℂ) (b : SeedPolynomial) : SeedPolynomial :=
  CycleQ2IncidenceEquations.seedG r +
    (b - C Complex.I * CycleQ2IncidenceEquations.smoothA) *
    (b + C Complex.I * CycleQ2IncidenceEquations.smoothA)

/-- The existing incidence seed is an exact member of this family. -/
theorem seedFamily_at_incidence_seed (r : ℂ) :
    seedFamily r CycleQ2IncidenceEquations.smoothB =
      CycleQ2IncidenceEquations.smoothF r Complex.I := rfl

/-- Varying the cubic inside the actual invariant degree-three piece
preserves the invariant degree-six piece used by the incidence family. -/
theorem seedFamily_homogeneous (r : ℂ) (b : SeedPolynomial)
    (hb : CycleQ2IncidenceEquations.HG b (3, 0)) :
    CycleQ2IncidenceEquations.HG (seedFamily r b) (6, 0) := by
  have ha := (CycleQ2IncidenceEquations.smoothA_homogeneous (R := ℂ)).C_mul Complex.I
  have hprod := (hb.sub ha).mul (hb.add ha)
  have hdegree : ((3, 0) : CycleQ2IncidenceEquations.Grade) + (3, 0) = (6, 0) :=
    by decide
  exact (CycleQ2IncidenceEquations.seedG_homogeneous r).add (hdegree ▸ hprod)

/-- The extra mixed coefficient records the distinction between the
literal complex parameter 57 and a cube root of two. -/
theorem seedFamily_expanded (r : ℂ) (b : SeedPolynomial) :
    seedFamily r b =
      X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 +
        C (2 - r ^ 3) * X 1 ^ 3 * X 3 ^ 3 + b ^ 2 := by
  have hi : (C Complex.I : SeedPolynomial) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hprod :
      (b - C Complex.I * CycleQ2IncidenceEquations.smoothA) *
        (b + C Complex.I * CycleQ2IncidenceEquations.smoothA) =
          b ^ 2 + CycleQ2IncidenceEquations.smoothA ^ 2 := by
    calc
      _ = b ^ 2 - (C Complex.I : SeedPolynomial) ^ 2 *
          CycleQ2IncidenceEquations.smoothA ^ 2 := by ring
      _ = _ := by rw [hi]; ring
  unfold seedFamily
  rw [hprod, CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG_expanded]
  simp only [CycleQ2IncidenceEquations.smoothA, map_sub, map_ofNat, map_pow]
  ring

theorem seedFamily_zero (r : ℂ) :
    seedFamily r 0 =
      X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 +
        C (2 - r ^ 3) * X 1 ^ 3 * X 3 ^ 3 := by
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
    seedFamily_expanded r 0

/-- The cube-root specialization recovers the Fermat member exactly. -/
theorem seedFamily_zero_of_cube_two (r : ℂ) (hr : r ^ 3 = 2) :
    seedFamily r 0 =
      X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 := by
  simpa [hr] using seedFamily_zero r

/-- Factored values of the actual five partial derivatives at the zero
cubic. Factoring the middle pair isolates the two exceptional parameters. -/
def zeroCubicGradient (r : ℂ) (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![6 * x 0 ^ 5,
    3 * x 1 ^ 2 * (2 * x 1 ^ 3 + (2 - r ^ 3) * x 3 ^ 3),
    6 * x 2 ^ 5,
    3 * x 3 ^ 2 * (2 * x 3 ^ 3 + (2 - r ^ 3) * x 1 ^ 3),
    3 * x 4 ^ 2]

theorem eval_pderiv_zeroCubic (r : ℂ) (x : Fin 5 → ℂ) (j : Fin 5) :
    eval x (pderiv j (seedFamily r 0)) = zeroCubicGradient r x j := by
  rw [seedFamily_zero]
  fin_cases j <;>
    norm_num [zeroCubicGradient, map_add, pderiv_mul, pderiv_pow,
      pderiv_C, Pi.single_apply, Fin.ext_iff] <;> ring

theorem zeroCubicGradient_common_zero (r : ℂ)
    (hr0 : r ^ 3 ≠ 0) (hr4 : r ^ 3 ≠ 4) (x : Fin 5 → ℂ)
    (hx : ∀ j, zeroCubicGradient r x j = 0) : x = 0 := by
  have h0 : (6 : ℂ) * x 0 ^ 5 = 0 := by
    simpa [zeroCubicGradient] using hx 0
  have h2 : (6 : ℂ) * x 2 ^ 5 = 0 := by
    simpa [zeroCubicGradient] using hx 2
  have h4 : (3 : ℂ) * x 4 ^ 2 = 0 := by
    simpa [zeroCubicGradient] using hx 4
  have hx0 : x 0 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h0).resolve_left (by norm_num))
  have hx2 : x 2 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h2).resolve_left (by norm_num))
  have hx4 : x 4 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h4).resolve_left (by norm_num))
  have hdisc : (4 : ℂ) - (2 - r ^ 3) ^ 2 ≠ 0 := by
    have heq : (4 : ℂ) - (2 - r ^ 3) ^ 2 = r ^ 3 * (4 - r ^ 3) := by ring
    rw [heq]
    exact mul_ne_zero hr0 (sub_ne_zero.mpr (Ne.symm hr4))
  have hx1 : x 1 = 0 := by
    by_contra hne1
    have hgrad1 :
        (3 : ℂ) * x 1 ^ 2 * (2 * x 1 ^ 3 + (2 - r ^ 3) * x 3 ^ 3) = 0 := by
      simpa [zeroCubicGradient] using hx 1
    have hleft : 2 * x 1 ^ 3 + (2 - r ^ 3) * x 3 ^ 3 = 0 :=
      (mul_eq_zero.mp hgrad1).resolve_left
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hne1))
    have hne3 : x 3 ≠ 0 := by
      intro heq
      have hz : (2 : ℂ) * x 1 ^ 3 = 0 := by simpa [heq] using hleft
      exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hne1)) hz
    have hgrad3 :
        (3 : ℂ) * x 3 ^ 2 * (2 * x 3 ^ 3 + (2 - r ^ 3) * x 1 ^ 3) = 0 := by
      simpa [zeroCubicGradient] using hx 3
    have hright : 2 * x 3 ^ 3 + (2 - r ^ 3) * x 1 ^ 3 = 0 :=
      (mul_eq_zero.mp hgrad3).resolve_left
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hne3))
    have hprod : ((4 : ℂ) - (2 - r ^ 3) ^ 2) * x 1 ^ 3 = 0 := by
      linear_combination 2 * hleft - (2 - r ^ 3) * hright
    exact (mul_ne_zero hdisc (pow_ne_zero 3 hne1)) hprod
  have h3 : (3 : ℂ) * x 3 ^ 2 * (2 * x 3 ^ 3) = 0 := by
    simpa [zeroCubicGradient, hx1] using hx 3
  have h3' : (6 : ℂ) * x 3 ^ 5 = 0 := by linear_combination h3
  have hx3 : x 3 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h3').resolve_left (by norm_num))
  funext j
  fin_cases j <;> simp [hx0, hx1, hx2, hx3, hx4]

/-- Algebraic nonsingularity of the zero-cubic member: at each nonzero
cone point at least one actual partial derivative is nonzero. -/
theorem zeroCubic_gradient_nonzero (r : ℂ)
    (hr0 : r ^ 3 ≠ 0) (hr4 : r ^ 3 ≠ 4) (x : Fin 5 → ℂ) (hx : x ≠ 0) :
    ∃ j, eval x (pderiv j (seedFamily r 0)) ≠ 0 := by
  by_contra! hzero
  apply hx
  apply zeroCubicGradient_common_zero r hr0 hr4 x
  intro j
  simpa only [eval_pderiv_zeroCubic] using hzero j

/-- The literal complex parameter in the existing incidence rank proof
has a nonsingular zero-cubic member in its own polynomial family. -/
theorem zeroCubic_gradient_nonzero_57 (x : Fin 5 → ℂ) (hx : x ≠ 0) :
    ∃ j, eval x (pderiv j (seedFamily 57 0)) ≠ 0 :=
  zeroCubic_gradient_nonzero 57 (by norm_num) (by norm_num) x hx

/-- A genuine invariant-cubic parameter with the required gradient
condition exists. No topological openness or geometric smoothness is
silently substituted for this explicit algebraic conclusion. -/
theorem exists_invariant_cubic_gradient_nonzero (r : ℂ)
    (hr0 : r ^ 3 ≠ 0) (hr4 : r ^ 3 ≠ 4) :
    ∃ b : SeedPolynomial,
      CycleQ2IncidenceEquations.HG b (3, 0) ∧
        ∀ x : Fin 5 → ℂ, x ≠ 0 →
          ∃ j, eval x (pderiv j (seedFamily r b)) ≠ 0 := by
  refine ⟨0, ?_, zeroCubic_gradient_nonzero r hr0 hr4⟩
  exact isWeightedHomogeneous_zero ℂ CycleQ2IncidenceNormalForm.fullGrading (3, 0)

end CycleQ2GeometricSeedSmooth

end
