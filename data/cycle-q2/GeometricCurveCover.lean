import Proposal.GeometricCurveCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The actual two denominator opens cover the curve

This is the existing prime-ideal cover argument from SolutionSupport07Part03.
It retains the literal quadratic and theta-family cubic, with their original
parameters. It does not assert smoothness, adjunction, or a Serre trace.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
open MvPolynomial

namespace CycleQ2SeedTwoOpenCover

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2SeedCech (curveA curveB)

private theorem mem_of_C_mul (Q : Ideal Poly) (c : ℂ) (hc : c ≠ 0) (p : Poly)
    (hp : C c * p ∈ Q) : p ∈ Q := by
  have hh := Q.mul_mem_left (C (c⁻¹)) hp
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

private theorem one_sub_I_ne_zero : (1 - Complex.I : ℂ) ≠ 0 := by
  intro hzero
  have hh := congrArg Complex.im hzero
  norm_num at hh

/-- The two small homogeneous functions have no common relevant prime
on the literal theta-family curve. -/
theorem coordinates_mem_of_A_B (r θ : ℂ) (Q : Ideal Poly) [Q.IsPrime]
    (hcurve : curveIdeal r θ ≤ Q) (hA : curveA ∈ Q) (hB : curveB ∈ Q) :
    ∀ j : Fin 4, X j ∈ Q := by
  have hF : relation r 0 ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hH : curveH θ ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hx0sq : (X (0 : Fin 4)) ^ 2 ∈ Q := by
    have hh := Q.add_mem hF (Q.mul_mem_left (C r) hA)
    simpa [relation, curveA, mul_assoc] using hh
  have hx0 : (X (0 : Fin 4)) ∈ Q :=
    (inferInstance : Q.IsPrime).mem_of_pow_mem 2 hx0sq
  have hx2 : (X (2 : Fin 4)) ∈ Q := hB
  have hrest : X (2 : Fin 4) * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
      X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2) ∈ Q :=
    Q.add_mem (Q.mul_mem_right _ hx2) (Q.mul_mem_right _ hx0)
  have hshape : curveH θ =
      (C (1 - Complex.I) * X 3 ^ 3 - C Complex.I * X 1 ^ 3) +
        (X 2 * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
          X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2)) := by
    simp [curveH, h, b, map_sub]
    ring
  have htail : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 -
      C Complex.I * X 1 ^ 3 ∈ Q := by
    have hh := Q.sub_mem hH hrest
    simpa only [hshape, add_sub_cancel_right] using hh
  have h13 : X (1 : Fin 4) ∈ Q ∧ X (3 : Fin 4) ∈ Q := by
    rcases (inferInstance : Q.IsPrime).mem_or_mem hA with hx1 | hx3
    · have hx1pow := Q.pow_mem_of_mem hx1 3 (by decide)
      have hh := Q.add_mem htail (Q.mul_mem_left (C Complex.I) hx1pow)
      have hc : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_add_cancel] using hh
      exact ⟨hx1, (inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ one_sub_I_ne_zero _ hc)⟩
    · have hx3pow := Q.pow_mem_of_mem hx3 3 (by decide)
      have hh := Q.sub_mem (Q.mul_mem_left (C (1 - Complex.I)) hx3pow) htail
      have hc : C Complex.I * X (1 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_sub_cancel] using hh
      exact ⟨(inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ Complex.I_ne_zero _ hc), hx3⟩
  intro j
  fin_cases j
  · exact hx0
  · exact h13.1
  · exact hx2
  · exact h13.2

/-- If both denominator functions lie in a prime of the actual curve,
then all four ordinary homogeneous coordinates lie in that prime. -/
theorem coordinates_mem_of_denominators (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (h1 : curveG1 r θ ∈ Q) (h2 : curveG2 r θ ∈ Q) :
    ∀ j : Fin 4, curveMap r θ (X j) ∈ Q := by
  let T : Ideal Poly := Q.comap (curveMap r θ)
  letI : T.IsPrime := Ideal.comap_isPrime _ _
  have hcurve : curveIdeal r θ ≤ T := by
    intro p hp
    change curveMap r θ p ∈ Q
    have hz : curveMap r θ p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hz]
    exact Q.zero_mem
  have hg1 : C (3 * r ^ 2) * curveA ^ 2 ∈ T := by
    change curveMap r θ (C (3 * r ^ 2) * curveA ^ 2) ∈ Q
    rw [← ambientCurveMap_g1]
    exact h1
  have hg2 : C 3 * curveB ^ 4 ∈ T := by
    change curveMap r θ (C 3 * curveB ^ 4) ∈ Q
    rw [← ambientCurveMap_g2]
    exact h2
  have hA : curveA ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 2
    (mem_of_C_mul T _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) _ hg1)
  have hB : curveB ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 4
    (mem_of_C_mul T _ (by norm_num) _ hg2)
  exact coordinates_mem_of_A_B r θ T hcurve hA hB

/-- The actual denominator opens cover every relevant prime of the
ordinary homogeneous curve presentation. -/
theorem relevant_prime_cover (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (hx : ∃ j : Fin 4, curveMap r θ (X j) ∉ Q) :
    curveG1 r θ ∉ Q ∨ curveG2 r θ ∉ Q := by
  by_contra! hbad
  obtain ⟨j, hj⟩ := hx
  exact hj (coordinates_mem_of_denominators r θ hr Q hbad.1 hbad.2 j)

/-- The same cover on the literal weighted curve: w=-x2² introduces no
additional relevant prime outside the two opens. -/
theorem weighted_relevant_prime_cover (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (hx : ∃ j : Fin 5, ambientCurveMap r θ (X j) ∉ Q) :
    curveG1 r θ ∉ Q ∨ curveG2 r θ ∉ Q := by
  by_contra! hbad
  have hc := coordinates_mem_of_denominators r θ hr Q hbad.1 hbad.2
  have hw : ∀ j : Fin 5, ambientCurveMap r θ (X j) ∈ Q := by
    intro j
    fin_cases j
    · simpa [ambientCurveMap, substitute] using hc 0
    · simpa [ambientCurveMap, substitute] using hc 1
    · simpa [ambientCurveMap, substitute] using hc 2
    · simpa [ambientCurveMap, substitute] using hc 3
    · simpa [ambientCurveMap, substitute] using
        Q.neg_mem (Q.pow_mem_of_mem (hc 2) 2 (by decide))
  obtain ⟨j, hj⟩ := hx
  exact hj (hw j)

end CycleQ2SeedTwoOpenCover

end
