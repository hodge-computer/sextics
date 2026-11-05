import HodgeComputer.Verify

/-!Addition of certificates with different denominators, including nonzero
quotient remainders. Extracted from fqlx's holdout-bundle construction
(PR #161), which credits the addition formula in the accepted one-reflection
proof. The common-denominator identities apply at every positive pole order.
-/

noncomputable section
namespace HodgeComputer
open HodgeTestbed MvPolynomial
open scoped BigOperators

theorem directional_add (P : Poly) (N M : Fin 6 → Poly) :
    directional P (fun i => N i + M i) = directional P N + directional P M := by
  simp [directional, mul_add, Finset.sum_add_distrib]

theorem divergence_add (N M : Fin 6 → Poly) :
    divergence (fun i => N i + M i) = divergence N + divergence M := by
  simp [divergence, map_add, Finset.sum_add_distrib]

theorem divergenceNumerator_add (D : Poly) (N M : Fin 6 → Poly) :
    divergenceNumerator D (fun i => N i + M i) =
      divergenceNumerator D N + divergenceNumerator D M := by
  simp only [divergenceNumerator, divergence_add, directional_add]
  ring

theorem defect_add_same_denominator (F A B D : Poly) (q : ℕ)
    (N M : Fin 6 → Poly) :
    defect F (A+B) D q (fun i => N i + M i) =
      defect F A D q N + defect F B D q M := by
  simp only [defect, directional_add, divergenceNumerator_add]
  ring

theorem defect_scale_denominator (F A D H : Poly) (q : ℕ)
    (N : Fin 6 → Poly) :
    defect F A (H*D) q (fun i => H*N i) = H^2 * defect F A D q N := by
  simp only [defect, HodgeTestbed.directional_mul,
    HodgeTestbed.divergenceNumerator_mul]
  ring

theorem defect_add (F A B D E : Poly) (q : ℕ) (N M : Fin 6 → Poly) :
    defect F (A+B) (D*E) q (fun i => E*N i + D*M i) =
      E^2 * defect F A D q N + D^2 * defect F B E q M := by
  rw [defect_add_same_denominator]
  conv_lhs => lhs; rw [mul_comm D E]
  rw [defect_scale_denominator, defect_scale_denominator]

theorem Verify.add {F A B D E Q R : Poly} {q d e : ℕ}
    {N M : Fin 6 → Poly}
    (hq : 0 < q) (h : Verify F A q d D N Q) (k : Verify F B q e E M R) :
    Verify F (A+B) q (d+e) (D*E) (fun i => E*N i + D*M i)
      (E^2*Q+D^2*R) where
  denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous.mul k.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := k.denominator_homogeneous.mul (h.numerator_homogeneous i)
    have hm := h.denominator_homogeneous.mul (k.numerator_homogeneous i)
    have hnd : e + (d + 6*q - 5) = (d+e) + 6*q - 5 := by omega
    have hmd : d + (e + 6*q - 5) = (d+e) + 6*q - 5 := by omega
    rw [hnd] at hn
    rw [hmd] at hm
    exact hn.add hm
  denominator_legal := h.denominator_legal.mul_right k.denominator_legal
  identity := by
    rw [defect_add, h.identity, k.identity]
    ring

theorem HasCertificate.add {F A B : Poly} {q : ℕ} (hq : 0 < q)
    (h : HasCertificate F A q) (k : HasCertificate F B q) :
    HasCertificate F (A+B) q := by
  obtain ⟨d, D, N, Q, h⟩ := h
  obtain ⟨e, E, M, R, k⟩ := k
  exact ⟨d+e, D*E, (fun i => E*N i+D*M i), E^2*Q+D^2*R,
    Verify.add hq h k⟩


/-- The zero source has a certificate with constant denominator. -/
theorem HasCertificate.zero (F : Poly) (q : ℕ) : HasCertificate F 0 q := by
  refine ⟨0, 1, (fun _ => 0), 0, ?_⟩
  exact {
    denominator_ne_zero := one_ne_zero
    denominator_homogeneous := isHomogeneous_one _ _
    numerator_homogeneous := fun _ => isHomogeneous_zero _ _ _
    denominator_legal := isRelPrime_one_right
    identity := by simp [defect, directional, divergenceNumerator, divergence]
  }

end HodgeComputer
