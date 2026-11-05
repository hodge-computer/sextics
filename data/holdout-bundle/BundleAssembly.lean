import HodgeComputer.Constructions.HoldoutCover.ConicResidue
import HodgeComputer.Constructions.HoldoutCover.CoverCertificate

/-!
The unchanged holdout-bundle target and certificate addition.  The first
summand is supplied by fqlx's accepted Fermat-cover construction (PR #128).
The short addition lemmas follow the exact non-strict construction in the
accepted one-reflection proof; both quotient remainders are retained.

Prepared with OpenAI ChatGPT collaborating-agent assistance.
-/

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace HoldoutBundle

open HodgeComputer HodgeTestbed HoldoutConstruction HoldoutConicIncidence MvPolynomial
open scoped BigOperators

def Astar : HodgeComputer.Poly := X 0^3 * X 3 * X 4^2

def Abundle : HodgeComputer.Poly := holdoutSource + Astar

theorem Astar_isHomogeneous : Astar.IsHomogeneous 6 := by
  exact ((isHomogeneous_X_pow (R := ℂ) (0 : Fin 6) 3).mul
    (isHomogeneous_X ℂ (3 : Fin 6))).mul
      (isHomogeneous_X_pow (R := ℂ) (4 : Fin 6) 2)

theorem Abundle_isHomogeneous : Abundle.IsHomogeneous 6 :=
  holdoutSource_isHomogeneous.add Astar_isHomogeneous

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

theorem verify_add_q1 {F A B D E Q R : Poly} {d e : ℕ}
    {N M : Fin 6 → Poly}
    (h : Verify F A 1 d D N Q) (k : Verify F B 1 e E M R) :
    Verify F (A+B) 1 (d+e) (D*E) (fun i => E*N i + D*M i)
      (E^2*Q+D^2*R) where
  denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous.mul k.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := k.denominator_homogeneous.mul (h.numerator_homogeneous i)
    have hm := h.denominator_homogeneous.mul (k.numerator_homogeneous i)
    have hnd : e + (d + 6*1 - 5) = (d+e) + 6*1 - 5 := by omega
    have hmd : d + (e + 6*1 - 5) = (d+e) + 6*1 - 5 := by omega
    rw [hnd] at hn
    rw [hmd] at hm
    exact hn.add hm
  denominator_legal := h.denominator_legal.mul_right k.denominator_legal
  identity := by
    rw [defect_add, h.identity, k.identity]
    ring

theorem certificate_add_q1 {F A B : Poly}
    (h : HasCertificate F A 1) (k : HasCertificate F B 1) :
    HasCertificate F (A+B) 1 := by
  obtain ⟨d, D, N, Q, h⟩ := h
  obtain ⟨e, E, M, R, k⟩ := k
  exact ⟨d+e, D*E, (fun i => E*N i+D*M i), E^2*Q+D^2*R,
    verify_add_q1 h k⟩

theorem first_summand_certificate :
    HasCertificate holdoutSextic holdoutSource 1 := by
  obtain ⟨p⟩ := HoldoutConic.exists_seed
  obtain ⟨w, hw⟩ := conic_target_residue_solution p coverQuotientSource
  exact holdout_hasCertificate_of_quotient_divergence w hw

theorem bundle_certificate_of_star
    (hstar : HasCertificate holdoutSextic Astar 1) :
    HasCertificate holdoutSextic Abundle 1 :=
  certificate_add_q1 first_summand_certificate hstar

end HoldoutBundle

#print axioms HoldoutBundle.first_summand_certificate
#print axioms HoldoutBundle.bundle_certificate_of_star
