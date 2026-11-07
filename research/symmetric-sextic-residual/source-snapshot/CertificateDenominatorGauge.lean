import HodgeComputer.Constructions.Explicit
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
A degree-preserving denominator gauge for normalized pole-one certificates.

The input is an actual ordinary Verify record with an exact first equation.
The quotient may be nonzero. Legality, nonzero denominator, homogeneity, and
the transformed quotient are all proved. No certificate existence is asserted.
-/

noncomputable section
namespace CertificateDenominatorGauge
open MvPolynomial HodgeComputer HodgeTestbed
open scoped BigOperators

abbrev Poly := AmbientPoly 5
abbrev Vector := Fin 6 → Poly

theorem vector_directional_add (F : Poly) (N M : Vector) :
    directional F (fun i => N i+M i) = directional F N+directional F M := by
  simp [directional, mul_add, Finset.sum_add_distrib]

theorem vector_divergenceNumerator_add (D : Poly) (N M : Vector) :
    divergenceNumerator D (fun i => N i+M i) =
      divergenceNumerator D N+divergenceNumerator D M := by
  simp only [divergenceNumerator, divergence, map_add, Finset.sum_add_distrib,
    vector_directional_add]
  ring

def sixth : Poly := C (1/6 : ℂ)
def scaledEuler (P : Poly) : Vector := fun i => sixth * (P * X i)

theorem sixth_six : sixth * 6 = 1 := by
  rw [sixth, show (6 : Poly) = C (6 : ℂ) from (map_natCast C 6).symm, ← map_mul]
  norm_num

theorem scaledEuler_action {k : ℕ} {F : Poly} (hF : F.IsHomogeneous k) (P : Poly) :
    directional F (scaledEuler P) = sixth * (k : Poly) * (P*F) := by
  calc
    _ = (sixth*P) * (∑ i : Fin 6, X i * pderiv i F) := by
      simp only [directional, scaledEuler, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hF.sum_X_mul_pderiv]; simp only [nsmul_eq_mul]; ring

theorem scaledEuler_divergence {k : ℕ} {P : Poly} (hP : P.IsHomogeneous k) :
    divergence (scaledEuler P) = sixth * ((k : Poly)+6) * P := by
  have hs : divergence (scaledEuler P) =
      sixth * ((∑ i : Fin 6, X i * pderiv i P) + 6*P) := by
    simp only [divergence, scaledEuler, sixth, pderiv_C_mul, pderiv_mul,
      pderiv_X_self, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [hs, hP.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul]
  ring

theorem scaledEuler_homogeneous {k : ℕ} {P : Poly} (hP : P.IsHomogeneous k) (i : Fin 6) :
    (scaledEuler P i).IsHomogeneous (k+1) :=
  (hP.mul (isHomogeneous_X ℂ i)).C_mul (1/6 : ℂ)

theorem euler_add_divergenceNumerator {k : ℕ} {D P : Poly}
    (hD : D.IsHomogeneous k) (hP : P.IsHomogeneous k) (N : Vector) :
    divergenceNumerator D (fun i => N i+scaledEuler P i) =
      divergenceNumerator D N + P*D := by
  rw [vector_divergenceNumerator_add]
  congr 1
  rw [divergenceNumerator, scaledEuler_divergence hP, scaledEuler_action hD]
  linear_combination (P*D)*sixth_six

theorem directional_add_source (F G : Poly) (N : Vector) :
    directional (F+G) N = directional F N+directional G N := by
  simp [directional, map_add, add_mul, Finset.sum_add_distrib]

/-- Coprimality is unchanged by adding a multiple of the hypersurface. -/
theorem legal_shift {F D B : Poly} (h : IsRelPrime F D) :
    IsRelPrime F (D+B*F) := by
  intro a ha hb
  apply h ha
  have hBF : a ∣ B*F := dvd_mul_of_dvd_right ha B
  simpa using dvd_sub hb hBF

theorem first_equation_shift {F A D B : Poly} {N : Vector}
    (hF : F.IsHomogeneous 6) (hfirst : directional F N = A*D) :
    directional F (fun i => N i+scaledEuler (A*B) i) = A*(D+B*F) := by
  rw [vector_directional_add, hfirst, scaledEuler_action hF]
  simp only [Nat.cast_ofNat]
  rw [sixth_six, one_mul]
  ring

/-- Exact polynomial identity, retaining every ordinary divergence quotient. -/
theorem second_equation_shift {b : ℕ} {F A D B : Poly} {N : Vector}
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6)
    (hD : D.IsHomogeneous (b+6)) (hB : B.IsHomogeneous b)
    (hfirst : directional F N = A*D) :
    divergenceNumerator (D+B*F) (fun i => N i+scaledEuler (A*B) i) =
      divergenceNumerator D N + F*(B*divergence N-directional B N+A*B^2) := by
  have hAB : (A*B).IsHomogeneous (b+6) := by
    simpa only [Nat.add_comm] using hA.mul hB
  rw [euler_add_divergenceNumerator (hD.add (hB.mul hF)) hAB]
  rw [divergenceNumerator, directional_add_source, directional_product, hfirst]
  unfold divergenceNumerator
  ring

theorem homogeneous_sextic_not_unit {F : Poly} (hF : F ≠ 0)
    (hdegree : F.IsHomogeneous 6) : ¬ IsUnit F := by
  intro hu
  have hc : coeff 0 F = 0 := hdegree.coeff_eq_zero (by simp)
  have he : eval (fun _ => (0 : ℂ)) F = 0 := by simpa only [eval_zero', constantCoeff_eq] using hc
  have hunit := hu.map (eval (fun _ => (0 : ℂ)))
  rw [he] at hunit
  exact not_isUnit_zero hunit

/-- Polynomial denominator shifts preserve actual ordinary Verify records.
The first equation is explicitly normalized; the quotient Q is unrestricted.
The new denominator is proved legal and nonzero, without extra assumptions. -/
theorem verify_shift {b : ℕ} {F A D B Q : Poly} {N : Vector}
    (h : Verify F A 6 1 D N Q)
    (hfirst : directional F N = A*D)
    (hB : B.IsHomogeneous b) (hdegree : D.totalDegree = b+6) :
    Verify F A 6 1 (D+B*F) (fun i => N i+scaledEuler (A*B) i)
      (Q+B*divergence N-directional B N+A*B^2) := by
  have hA : A.IsHomogeneous 6 := by
    have ha := h.source_homogeneous.isHomogeneous (by norm_num)
    simpa using ha
  have hD : D.IsHomogeneous (b+6) := by
    simpa only [hdegree] using h.denominator_homogeneous
  have hlegal := legal_shift (B := B) h.denominator_legal
  have hD0 : D+B*F ≠ 0 := by
    intro hz
    apply homogeneous_sextic_not_unit h.hypersurface_ne_zero h.hypersurface_homogeneous
    exact hlegal (dvd_refl F) (by rw [hz]; exact dvd_zero F)
  have hAB : (A*B).IsHomogeneous (b+6) := by
    simpa only [Nat.add_comm] using hA.mul hB
  have hN (i : Fin 6) : (N i).IsHomogeneous (b+7) := by
    have hn := (h.numerator_homogeneous i).isHomogeneous (by omega)
    rw [hdegree] at hn
    convert hn using 1 <;> omega
  have hN' (i : Fin 6) : (N i+scaledEuler (A*B) i).IsHomogeneous (b+7) := by
    have he := scaledEuler_homogeneous hAB i
    convert (hN i).add he using 1 <;> omega
  have hdiv : divergenceNumerator D N = F*Q := by
    apply mul_left_cancel₀ h.hypersurface_ne_zero
    calc
      F*divergenceNumerator D N = defect F A D 1 N := by
        simp only [defect, Nat.cast_one, one_mul, hfirst]
        ring
      _ = F^2*Q := h.identity
      _ = F*(F*Q) := by ring
  apply Verify.of_normalized h.hypersurface_ne_zero h.hypersurface_homogeneous
    h.source_homogeneous hD0 (hD.add (hB.mul h.hypersurface_homogeneous)) hN'
    (by omega) hlegal
  · simpa only [Nat.cast_one, one_mul] using
      first_equation_shift h.hypersurface_homogeneous hfirst
  · rw [second_equation_shift h.hypersurface_homogeneous hA hD hB hfirst, hdiv]
    simp only [pow_one]
    ring

#print axioms second_equation_shift
#print axioms verify_shift
end CertificateDenominatorGauge
