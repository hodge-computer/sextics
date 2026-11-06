import HodgeComputer.Verify
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!Addition of certificates with different denominators, including nonzero
quotient remainders. Extracted from fqlx's holdout-bundle construction
(PR #161), which credits the addition formula in the accepted one-reflection
proof. The common-denominator identities apply at every pole parameter.
-/

noncomputable section
namespace HodgeComputer
open HodgeTestbed MvPolynomial
open scoped BigOperators

theorem directional_add {n : ℕ} (P : AmbientPoly n) (N M : Fin (n + 1) → AmbientPoly n) :
    directional P (fun i => N i + M i) = directional P N + directional P M := by
  simp [directional, mul_add, Finset.sum_add_distrib]

theorem divergence_add {n : ℕ} (N M : Fin (n + 1) → AmbientPoly n) :
    divergence (fun i => N i + M i) = divergence N + divergence M := by
  simp [divergence, map_add, Finset.sum_add_distrib]

theorem divergenceNumerator_add {n : ℕ} (D : AmbientPoly n) (N M : Fin (n + 1) → AmbientPoly n) :
    divergenceNumerator D (fun i => N i + M i) =
      divergenceNumerator D N + divergenceNumerator D M := by
  simp only [divergenceNumerator, divergence_add, directional_add]
  ring

theorem defect_add_same_denominator {n : ℕ} (F A B D : AmbientPoly n) (q : ℕ)
    (N M : Fin (n + 1) → AmbientPoly n) :
    defect F (A+B) D q (fun i => N i + M i) =
      defect F A D q N + defect F B D q M := by
  simp only [defect, directional_add, divergenceNumerator_add]
  ring

theorem defect_scale_denominator {n : ℕ} (F A D H : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) :
    defect F A (H*D) q (fun i => H*N i) = H^2 * defect F A D q N := by
  simp only [defect, HodgeTestbed.directional_mul,
    HodgeTestbed.divergenceNumerator_mul]
  ring

theorem defect_add {n : ℕ} (F A B D E : AmbientPoly n) (q : ℕ) (N M : Fin (n + 1) → AmbientPoly n) :
    defect F (A+B) (D*E) q (fun i => E*N i + D*M i) =
      E^2 * defect F A D q N + D^2 * defect F B E q M := by
  rw [defect_add_same_denominator]
  conv_lhs => lhs; rw [mul_comm D E]
  rw [defect_scale_denominator, defect_scale_denominator]

theorem Verify.add {n : ℕ} {F A B D E Q R : AmbientPoly n} {d q : ℕ}
    {N M : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q E M R) :
    Verify F (A+B) d q (D*E) (fun i => E*N i + D*M i)
      (E^2*Q+D^2*R) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.add k.source_homogeneous
  denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
  denominator_homogeneous := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero]
    exact h.denominator_homogeneous.mul k.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := (Homogeneous.of_isHomogeneous k.denominator_homogeneous).mul (h.numerator_homogeneous i)
    have hm := (Homogeneous.of_isHomogeneous h.denominator_homogeneous).mul (k.numerator_homogeneous i)
    rw [MvPolynomial.totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero, Nat.cast_add]
    convert hn.add (by convert hm using 1 <;> ring) using 1 <;> ring
  denominator_legal := h.denominator_legal.mul_right k.denominator_legal
  identity := by
    rw [defect_add, h.identity, k.identity]
    ring

theorem HasCertificate.add {n : ℕ} {F A B : AmbientPoly n} {q : ℕ}
    (h : HasCertificate F q A) (k : HasCertificate F q B) :
    HasCertificate F q (A+B) := by
  obtain ⟨D, N, Q, h⟩ := h
  obtain ⟨E, M, R, k⟩ := k
  exact ⟨D*E, (fun i => E*N i+D*M i), E^2*Q+D^2*R, Verify.add h k⟩

/-- The zero source has a certificate with constant denominator. -/
theorem HasCertificate.zero {n : ℕ} (F : AmbientPoly n) {d : ℕ} (q : ℕ)
    (hF : F ≠ 0) (hd : F.IsHomogeneous d) : HasCertificate F q 0 := by
  rw [HasCertificate, hd.totalDegree hF]
  refine ⟨1, (fun _ => 0), 0, ?_⟩
  exact {
    hypersurface_ne_zero := hF
    hypersurface_homogeneous := hd
    source_homogeneous := homogeneous_zero _
    denominator_ne_zero := one_ne_zero
    denominator_homogeneous := by simpa using isHomogeneous_one (Fin (n+1)) ℂ
    numerator_homogeneous := fun _ => homogeneous_zero _
    denominator_legal := isRelPrime_one_right
    identity := by simp [defect, directional, divergenceNumerator, divergence]
  }

end HodgeComputer
