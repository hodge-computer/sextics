import HodgeComputer.CertificateOperations
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Same-denominator radial normalization

A homogeneous certificate can be normalized to the two equations
`q * dF(N) = A * D` and `divergenceNumerator D N = F^q * Q`, without changing
its denominator or quotient. The radial correction preserves the entire
cleared defect, rather than merely its restriction to the hypersurface.

The theorem applies in every projective dimension `n`, at every degree `d`
and pole parameter `q` with `n + 1 ≤ d * q`. This condition makes the radial
degree shift nonnegative and implies `d ≠ 0` and `q ≠ 0`. Cases below that
bound are not asserted by this natural-degree formulation.

Extracted and generalized from `fqlx`'s radial normalization of a physical
current, with OpenAI assistance. The formulas below contain no fixed
hypersurface, source, degree, dimension, or denominator.
-/

noncomputable section
set_option autoImplicit false

namespace HodgeComputer.RadialNormalization

open MvPolynomial HodgeTestbed
open scoped BigOperators

variable {n : ℕ}

abbrev coordinates : Fin (n + 1) → AmbientPoly n := fun i => X i

def euler (P : AmbientPoly n) : AmbientPoly n := directional P coordinates

/-- The radial correction scaled by the inverse of the normal Euler factor. -/
def radial (d q : ℕ) (H : AmbientPoly n) : Fin (n + 1) → AmbientPoly n :=
  fun i => C (1 / ((q * d : ℕ) : ℂ)) * H * X i

def normalizeNumerators (d q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (H : AmbientPoly n) : Fin (n + 1) → AmbientPoly n :=
  fun i => N i + radial d q H i

theorem euler_add (P Q : AmbientPoly n) : euler (P + Q) = euler P + euler Q := by
  simp [euler, directional, map_add, add_mul, Finset.sum_add_distrib]

theorem euler_mul (P Q : AmbientPoly n) : euler (P * Q) = Q * euler P + P * euler Q := by
  exact HodgeTestbed.directional_product Q P coordinates

theorem euler_C (c : ℂ) : euler (C c : AmbientPoly n) = 0 := by
  simp [euler, directional, coordinates]

theorem euler_of_homogeneous {P : AmbientPoly n} {e : ℕ} (h : P.IsHomogeneous e) :
    euler P = C (e : ℂ) * P := by
  calc
    euler P = ∑ i : Fin (n + 1), X i * pderiv i P := by
      simp [euler, directional, coordinates, mul_comm]
    _ = e • P := h.sum_X_mul_pderiv
    _ = C (e : ℂ) * P := by simp only [nsmul_eq_mul, map_natCast]

theorem coeff_euler (P : AmbientPoly n) (m : Fin (n + 1) →₀ ℕ) :
    coeff m (euler P) = (m.degree : ℂ) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial a c =>
      rw [euler_of_homogeneous (isHomogeneous_monomial c rfl), coeff_C_mul]
      by_cases ha : a = m
      · subst a
        rfl
      · simp [coeff_monomial, ha]
  | add P Q hP hQ =>
      rw [euler_add, coeff_add, hP, hQ, coeff_add]
      ring

theorem homogeneous_of_euler {P : AmbientPoly n} {e : ℕ}
    (h : euler P = C (e : ℂ) * P) : P.IsHomogeneous e := by
  classical
  intro m hm
  have hc := congrArg (coeff m) h
  rw [coeff_euler, coeff_C_mul] at hc
  have he : (m.degree : ℂ) = (e : ℂ) := (mul_right_cancel₀ hm) hc
  have hd : m.degree = e := Nat.cast_injective he
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd

/-- A quotient of homogeneous polynomials has the forced degree. In particular,
the normalization does not assume any separate homogeneity hypothesis on `Q`. -/
theorem homogeneous_quotient {F H : AmbientPoly n} {a b : ℕ}
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous a)
    (hFH : (F * H).IsHomogeneous (a + b)) : H.IsHomogeneous b := by
  apply homogeneous_of_euler
  apply mul_left_cancel₀ hF0
  have ht := euler_of_homogeneous hFH
  rw [euler_mul, euler_of_homogeneous hF] at ht
  simp only [Nat.cast_add, map_add] at ht
  linear_combination ht

theorem divergence_coordinates : divergence (coordinates (n := n)) = (n + 1 : AmbientPoly n) := by
  simp [divergence, coordinates]

theorem directional_radial (P H : AmbientPoly n) (d q : ℕ) :
    directional P (radial d q H) = C (1 / ((q * d : ℕ) : ℂ)) * H * euler P := by
  exact HodgeTestbed.directional_mul P (C (1 / ((q * d : ℕ) : ℂ)) * H) coordinates

theorem divergence_radial (H : AmbientPoly n) (d q : ℕ) :
    divergence (radial d q H) =
      C (1 / ((q * d : ℕ) : ℂ)) * (euler H + (n + 1 : AmbientPoly n) * H) := by
  change divergence (fun i => (C (1 / ((q * d : ℕ) : ℂ)) * H) * coordinates i) = _
  rw [HodgeTestbed.divergence_mul, divergence_coordinates]
  change euler (C (1 / ((q * d : ℕ) : ℂ)) * H) +
    (C (1 / ((q * d : ℕ) : ℂ)) * H) * (n + 1 : AmbientPoly n) = _
  rw [euler_mul, euler_C]
  ring

theorem divergenceNumerator_radial (D H : AmbientPoly n) (d q : ℕ) :
    divergenceNumerator D (radial d q H) = C (1 / ((q * d : ℕ) : ℂ)) *
      (D * euler H + (n + 1 : AmbientPoly n) * D * H - H * euler D) := by
  unfold divergenceNumerator
  rw [divergence_radial, directional_radial]
  ring

/-- At the forced Euler degree, the radial correction preserves the complete
polynomial defect for every source and every current. -/
theorem radial_gauge_preserves_defect (F A D H : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) {d q e r : ℕ}
    (hshift : r + (n + 1) = d * q) (hF : F.IsHomogeneous d)
    (hD : D.IsHomogeneous e) (hH : H.IsHomogeneous (e + r)) :
    defect F A D q (normalizeNumerators d q N H) = defect F A D q N := by
  have hs : (r : AmbientPoly n) + (n + 1 : AmbientPoly n) =
      (d : AmbientPoly n) * q := by exact_mod_cast hshift
  unfold normalizeNumerators defect
  rw [HodgeComputer.directional_add, HodgeComputer.divergenceNumerator_add,
    directional_radial, divergenceNumerator_radial,
    euler_of_homogeneous hF, euler_of_homogeneous hD, euler_of_homogeneous hH]
  simp only [Nat.cast_add, map_add, map_natCast]
  linear_combination C (1 / ((q * d : ℕ) : ℂ)) * F * D * H * hs

theorem first_normal_after_gauge (F A D H : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) {d q : ℕ}
    (hd : d ≠ 0) (hq : q ≠ 0) (hF : F.IsHomogeneous d)
    (hH : A * D - (q : AmbientPoly n) * directional F N = F * H) :
    (q : AmbientPoly n) * directional F (normalizeNumerators d q N H) = A * D := by
  have hqd : ((q * d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hq hd)
  have hc : (q : AmbientPoly n) * (d : AmbientPoly n) *
      C (1 / ((q * d : ℕ) : ℂ)) = 1 := by
    have h := congrArg (C (σ := Fin (n + 1))) (mul_one_div_cancel hqd)
    simpa only [map_mul, Nat.cast_mul, map_natCast, map_one] using h
  unfold normalizeNumerators
  rw [HodgeComputer.directional_add, directional_radial, euler_of_homogeneous hF]
  simp only [map_natCast]
  linear_combination -hH + (F * H) * hc

theorem directional_homogeneous {F : AmbientPoly n} {N : Fin (n + 1) → AmbientPoly n}
    {d e r : ℕ} (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hN : ∀ i, (N i).IsHomogeneous (e + r + 1)) :
    (directional F N).IsHomogeneous (e + (d + r)) := by
  unfold directional
  apply IsHomogeneous.sum
  intro i _
  simpa only [show d - 1 + (e + r + 1) = e + (d + r) by omega] using
    (hF.pderiv (i := i)).mul (hN i)

theorem normalizeNumerators_homogeneous {N : Fin (n + 1) → AmbientPoly n}
    {H : AmbientPoly n} {e r : ℕ} (d q : ℕ)
    (hN : ∀ i, (N i).IsHomogeneous (e + r + 1))
    (hH : H.IsHomogeneous (e + r)) :
    ∀ i, (normalizeNumerators d q N H i).IsHomogeneous (e + r + 1) := by
  intro i
  apply (hN i).add
  change (C (1 / ((q * d : ℕ) : ℂ)) * H * X i).IsHomogeneous (e + r + 1)
  exact (hH.C_mul _).mul (isHomogeneous_X ℂ i)

/-- Divisibility by `F` already suffices to normalize the first equation.
The denominator and full defect stay unchanged. -/
theorem normalize_of_first_divisibility
    {F A D : AmbientPoly n} {N : Fin (n + 1) → AmbientPoly n} {d q e r : ℕ}
    (hshift : r + (n + 1) = d * q)
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous d) (hA : A.IsHomogeneous (d + r))
    (hD : D.IsHomogeneous e) (hN : ∀ i, (N i).IsHomogeneous (e + r + 1))
    (hlegal : IsRelPrime F D) (hdiv : F ∣ defect F A D q N) :
    ∃ H : AmbientPoly n, H.IsHomogeneous (e + r) ∧
      A * D - (q : AmbientPoly n) * directional F N = F * H ∧
      (∀ i, (normalizeNumerators d q N H i).IsHomogeneous (e + r + 1)) ∧
      (q : AmbientPoly n) * directional F (normalizeNumerators d q N H) = A * D ∧
      defect F A D q (normalizeNumerators d q N H) = defect F A D q N := by
  classical
  have hd : d ≠ 0 := by intro h; rw [h, zero_mul] at hshift; omega
  have hq : q ≠ 0 := by intro h; rw [h, mul_zero] at hshift; omega
  obtain ⟨W, hW⟩ := hdiv
  have hprod : F ∣ D * (A * D - (q : AmbientPoly n) * directional F N) := by
    refine ⟨W - divergenceNumerator D N, ?_⟩
    unfold defect at hW
    linear_combination hW
  obtain ⟨H, hH⟩ := hlegal.dvd_of_dvd_mul_left hprod
  have hS : (A * D - (q : AmbientPoly n) * directional F N).IsHomogeneous (e + (d + r)) := by
    apply IsHomogeneous.sub
    · simpa only [Nat.add_comm] using hA.mul hD
    · simpa only [map_natCast] using
        (directional_homogeneous (Nat.pos_of_ne_zero hd) hF hN).C_mul (q : ℂ)
  have hFH : (F * H).IsHomogeneous (d + (e + r)) := by
    rw [← hH]
    convert hS using 1
    omega
  have hh := homogeneous_quotient hF0 hF hFH
  exact ⟨H, hh, hH, normalizeNumerators_homogeneous d q hN hh,
    first_normal_after_gauge F A D H N hd hq hF hH,
    radial_gauge_preserves_defect F A D H N hshift hF hD hh⟩

/-- Every certificate in the stated degree range admits an exactly normalized
representative with the same polynomial denominator and quotient. -/
theorem normalize_verify {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n} (hdim : n + 1 ≤ d * q)
    (h : Verify F A d q D N Q) :
    ∃ N' : Fin (n + 1) → AmbientPoly n, Verify F A d q D N' Q ∧
      (q : AmbientPoly n) * directional F N' = A * D ∧
      divergenceNumerator D N' = F ^ q * Q := by
  let r := d * q - (n + 1)
  have hshift : r + (n + 1) = d * q := Nat.sub_add_cancel hdim
  have hshiftZ : (r : ℤ) + (n + 1 : ℤ) = (d : ℤ) * q := by exact_mod_cast hshift
  have hN : ∀ i, (N i).IsHomogeneous (D.totalDegree + r + 1) := by
    intro i
    have hn : Homogeneous (N i) ((D.totalDegree + r + 1 : ℕ) : ℤ) := by
      convert h.numerator_homogeneous i using 1
      push_cast
      omega
    simpa only [Int.toNat_natCast] using hn.isHomogeneous (by omega)
  have hA : A.IsHomogeneous (d + r) := by
    have ha : Homogeneous A ((d + r : ℕ) : ℤ) := by
      convert h.source_homogeneous using 1
      push_cast
      nlinarith [hshiftZ]
    simpa only [Int.toNat_natCast] using ha.isHomogeneous (by omega)
  have hdvd : F ∣ defect F A D q N := by
    refine ⟨F ^ q * Q, ?_⟩
    rw [h.identity, pow_succ]
    ring
  obtain ⟨H, _, _, hhom, hfirst, hsame⟩ :=
    normalize_of_first_divisibility hshift h.hypersurface_ne_zero h.hypersurface_homogeneous
      hA h.denominator_homogeneous hN h.denominator_legal hdvd
  let N' := normalizeNumerators d q N H
  have hidentity : defect F A D q N' = F ^ (q + 1) * Q := hsame.trans h.identity
  have hv : Verify F A d q D N' Q := {
    hypersurface_ne_zero := h.hypersurface_ne_zero
    hypersurface_homogeneous := h.hypersurface_homogeneous
    source_homogeneous := h.source_homogeneous
    denominator_ne_zero := h.denominator_ne_zero
    denominator_homogeneous := h.denominator_homogeneous
    numerator_homogeneous := by
      intro i
      convert Homogeneous.of_isHomogeneous (hhom i) using 1
      push_cast
      omega
    denominator_legal := h.denominator_legal
    identity := hidentity
  }
  have hs : divergenceNumerator D N' = F ^ q * Q := by
    apply mul_left_cancel₀ h.hypersurface_ne_zero
    calc
      F * divergenceNumerator D N' = defect F A D q N' := by
        unfold defect
        linear_combination D * hfirst
      _ = F ^ (q + 1) * Q := hidentity
      _ = F * (F ^ q * Q) := by rw [pow_succ]; ring
  exact ⟨N', hv, hfirst, hs⟩

end HodgeComputer.RadialNormalization
