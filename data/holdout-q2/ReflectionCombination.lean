import Proposal.HoldoutAlgebra
import HodgeComputer.Verify

/-! Exact combination of the two endpoint sources and common-denominator
combination of formal certificates. Complex coefficients are allowed by the
protected contract, so rational coefficient descent is unnecessary. -/

noncomputable section
namespace HoldoutReflectionCombination
open MvPolynomial HodgeTestbed HodgeComputer

section Algebra
variable {K : Type*} [Field K] [CharZero K]

theorem target_decomposition {k : K} (hk : k^2+k+1=0) (P c d : K) :
    P*c^2=(2+k)/3*(P*(c^2-k^2*d^2))+
      (2+k^2)/3*(P*(c^2-k*d^2)) := by
  field_simp
  linear_combination -P*(c^2-2*k*d^2)*hk

theorem target_decomposition_delta {k : K} (hk : k^2+k+1=0) (P c d : K) :
    P*c^2=(2+k)/3*(P*HoldoutAlgebra.delta k c d)+
      (2+k^2)/3*(P*HoldoutAlgebra.delta (k^2) c d) := by
  have h4 : (k^2)^2=k := by
    linear_combination (k^2-k)*hk
  simpa only [HoldoutAlgebra.delta,h4] using target_decomposition hk P c d

end Algebra

def combinedNumerators (l m : ℂ) (D E : HodgeComputer.Poly)
    (N M : Fin 6 → HodgeComputer.Poly) : Fin 6 → HodgeComputer.Poly :=
  fun i => C l*E*N i+C m*D*M i

theorem combined_directional (l m : ℂ) (F D E : HodgeComputer.Poly)
    (N M : Fin 6 → HodgeComputer.Poly) :
    directional F (combinedNumerators l m D E N M)=
      C l*E*directional F N+C m*D*directional F M := by
  simp only [directional,combinedNumerators,Fin.sum_univ_six]
  ring

theorem combined_divergenceNumerator (l m : ℂ) (D E : HodgeComputer.Poly)
    (N M : Fin 6 → HodgeComputer.Poly) :
    divergenceNumerator (D*E) (combinedNumerators l m D E N M)=
      C l*E^2*divergenceNumerator D N+C m*D^2*divergenceNumerator E M := by
  simp only [divergenceNumerator,divergence,directional,combinedNumerators,
    Fin.sum_univ_six,map_add,pderiv_mul,pderiv_C,zero_mul,add_zero]
  ring

theorem combined_defect (l m : ℂ) (F A B D E : HodgeComputer.Poly)
    (q : ℕ) (N M : Fin 6 → HodgeComputer.Poly) :
    defect F (C l*A+C m*B) (D*E) q (combinedNumerators l m D E N M)=
      C l*E^2*defect F A D q N+C m*D^2*defect F B E q M := by
  simp only [defect,combined_directional,combined_divergenceNumerator]
  ring

/-- Combining two certificates preserves the exact protected contract, including
complex relative primality. This lemma also allows non-strict input fields. -/
theorem combine_q2 (l m : ℂ) {F A B D E Q R : HodgeComputer.Poly}
    {d e : ℕ} {N M : Fin 6 → HodgeComputer.Poly}
    (hN : Verify F A 2 d D N Q) (hM : Verify F B 2 e E M R) :
    Verify F (C l*A+C m*B) 2 (d+e) (D*E)
      (combinedNumerators l m D E N M) (C l*E^2*Q+C m*D^2*R) := by
  refine ⟨mul_ne_zero hN.denominator_ne_zero hM.denominator_ne_zero,
    hN.denominator_homogeneous.mul hM.denominator_homogeneous, ?_,
    hN.denominator_legal.mul_right hM.denominator_legal, ?_⟩
  · intro i
    have hleft := (hM.denominator_homogeneous.mul (hN.numerator_homogeneous i)).C_mul l
    have hright := (hN.denominator_homogeneous.mul (hM.numerator_homogeneous i)).C_mul m
    have hl : e+(d+6*2-5)=d+e+6*2-5 := by omega
    have hr : d+(e+6*2-5)=d+e+6*2-5 := by omega
    rw [hl] at hleft
    rw [hr] at hright
    simpa only [combinedNumerators,mul_assoc] using hleft.add hright
  · rw [combined_defect,hN.identity,hM.identity]
    ring

theorem hasCertificate_combine_q2 (l m : ℂ) {F A B : HodgeComputer.Poly}
    (hA : HasCertificate F A 2) (hB : HasCertificate F B 2) :
    HasCertificate F (C l*A+C m*B) 2 := by
  obtain ⟨d,D,N,Q,hN⟩ := hA
  obtain ⟨e,E,M,R,hM⟩ := hB
  exact ⟨d+e,D*E,combinedNumerators l m D E N M,
    C l*E^2*Q+C m*D^2*R,combine_q2 l m hN hM⟩

end HoldoutReflectionCombination

#print axioms HoldoutReflectionCombination.combine_q2
#print axioms HoldoutReflectionCombination.target_decomposition_delta
