import HodgeComputer.Sextic
import Proposal.HoldoutAlgebra
import HodgeComputer.CertificateOperations

/-! Exact combination of the two endpoint sources and common-denominator
combination of formal certificates. Complex coefficients are allowed by the
protected contract, so rational coefficient descent is unnecessary. -/

noncomputable section
namespace HoldoutReflectionCombination
open MvPolynomial HodgeTestbed HodgeComputer HodgeComputer.Sextic

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

def combinedNumerators (l m : ℂ) (D E : HodgeComputer.Sextic.Poly)
    (N M : Fin 6 → HodgeComputer.Sextic.Poly) : Fin 6 → HodgeComputer.Sextic.Poly :=
  fun i => C l*E*N i+C m*D*M i

theorem combined_directional (l m : ℂ) (F D E : HodgeComputer.Sextic.Poly)
    (N M : Fin 6 → HodgeComputer.Sextic.Poly) :
    directional F (combinedNumerators l m D E N M)=
      C l*E*directional F N+C m*D*directional F M := by
  simp only [directional,combinedNumerators,Fin.sum_univ_six]
  ring

theorem combined_divergenceNumerator (l m : ℂ) (D E : HodgeComputer.Sextic.Poly)
    (N M : Fin 6 → HodgeComputer.Sextic.Poly) :
    divergenceNumerator (D*E) (combinedNumerators l m D E N M)=
      C l*E^2*divergenceNumerator D N+C m*D^2*divergenceNumerator E M := by
  simp only [divergenceNumerator,divergence,directional,combinedNumerators,
    Fin.sum_univ_six,map_add,pderiv_mul,pderiv_C,zero_mul,add_zero]
  ring

theorem combined_defect (l m : ℂ) (F A B D E : HodgeComputer.Sextic.Poly)
    (q : ℕ) (N M : Fin 6 → HodgeComputer.Sextic.Poly) :
    defect F (C l*A+C m*B) (D*E) q (combinedNumerators l m D E N M)=
      C l*E^2*defect F A D q N+C m*D^2*defect F B E q M := by
  change (C l*A+C m*B)*(D*E)^2 - (q : HodgeComputer.Sextic.Poly)*(D*E)*
      directional F (combinedNumerators l m D E N M) +
      F*divergenceNumerator (D*E) (combinedNumerators l m D E N M) =
    C l*E^2*(A*D^2-(q : HodgeComputer.Sextic.Poly)*D*directional F N+F*divergenceNumerator D N) +
    C m*D^2*(B*E^2-(q : HodgeComputer.Sextic.Poly)*E*directional F M+F*divergenceNumerator E M)
  rw [combined_directional, combined_divergenceNumerator]
  ring

/-- Combining two certificates preserves the exact protected contract, including
complex relative primality. This lemma also allows non-strict input fields. -/
theorem combine_q2 (l m : ℂ) {F A B D E Q R : HodgeComputer.Sextic.Poly}
    {N M : Fin 6 → HodgeComputer.Sextic.Poly}
    (hN : Verify F A 6 2 D N Q) (hM : Verify F B 6 2 E M R) :
    Verify F (C l*A+C m*B) 6 2 (D*E)
      (combinedNumerators l m D E N M) (C l*E^2*Q+C m*D^2*R) := by
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hN.denominator_ne_zero hM.denominator_ne_zero
  refine ⟨hN.hypersurface_ne_zero, hN.hypersurface_homogeneous,
    (hN.source_homogeneous.C_mul l).add (hM.source_homogeneous.C_mul m),
    mul_ne_zero hN.denominator_ne_zero hM.denominator_ne_zero, ?_, ?_,
    hN.denominator_legal.mul_right hM.denominator_legal, ?_⟩
  · rw [hdeg]
    exact hN.denominator_homogeneous.mul hM.denominator_homogeneous
  · intro i
    have hleft := ((Homogeneous.of_isHomogeneous hM.denominator_homogeneous).mul (hN.numerator_homogeneous i)).C_mul l
    have hright := ((Homogeneous.of_isHomogeneous hN.denominator_homogeneous).mul (hM.numerator_homogeneous i)).C_mul m
    rw [hdeg, Nat.cast_add]
    simp only [combinedNumerators, mul_assoc]
    convert hleft.add (by convert hright using 1 <;> ring) using 1 <;> ring
  · rw [combined_defect,hN.identity,hM.identity]
    ring

theorem hasCertificate_combine_q2 (l m : ℂ) {F A B : HodgeComputer.Sextic.Poly}
    (hA : HasCertificate F A 6 2) (hB : HasCertificate F B 6 2) :
    HasCertificate F (C l*A+C m*B) 6 2 := by
  obtain ⟨D,N,Q,hN⟩ := hA
  obtain ⟨E,M,R,hM⟩ := hB
  exact ⟨D*E,combinedNumerators l m D E N M,
    C l*E^2*Q+C m*D^2*R,combine_q2 l m hN hM⟩

end HoldoutReflectionCombination

#print axioms HoldoutReflectionCombination.combine_q2
#print axioms HoldoutReflectionCombination.target_decomposition_delta
