import HodgeComputer.CertificateOperations

/-!
Coordinate changes for certificate constructions. The sign-involution formulas
come from `fqlx`'s one-reflection proof (#123); permutation transport comes from
`benediamond`'s cyclic-triple-fano proof (#153). Both now apply in every ambient
dimension. The field components transform as well as the polynomials.
-/
noncomputable section
namespace HodgeComputer
open MvPolynomial HodgeTestbed
open scoped BigOperators
variable {n : ℕ}

def signChange (s : Fin (n + 1) → ℂ) : AmbientPoly n →+* AmbientPoly n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => C (s i) * X i)

@[simp] theorem signChange_C (s : Fin (n + 1) → ℂ) (c : ℂ) :
    signChange s (C c) = C c := by simp [signChange]

@[simp] theorem signChange_X (s : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    signChange s (X i) = C (s i) * X i := by simp [signChange]

theorem signChange_involutive (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1) :
    (signChange s).comp (signChange s) = RingHom.id (AmbientPoly n) := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i
    simp only [RingHom.comp_apply, RingHom.id_apply, signChange_X, map_mul, signChange_C]
    rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

@[simp] theorem signChange_twice (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1) (p : AmbientPoly n) :
    signChange s (signChange s p) = p :=
  DFunLike.congr_fun (signChange_involutive s hs) p

theorem pderiv_signChange (s : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (p : AmbientPoly n) :
    pderiv i (signChange s p) = C (s i) * signChange s (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p j hp =>
    simp only [map_mul, signChange_X, pderiv_mul, pderiv_C, hp, map_add]
    by_cases hj : j = i
    · subst j; simp only [pderiv_X_self, map_one]; ring
    · simp only [pderiv_X_of_ne hj, map_zero]; ring

def signField (s : Fin (n + 1) → ℂ) (N : Fin (n + 1) → AmbientPoly n) : Fin (n + 1) → AmbientPoly n :=
  fun i => C (s i) * signChange s (N i)

theorem directional_signChange (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (p : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    directional (signChange s p) (signField s N) = signChange s (directional p N) := by
  simp only [directional, signField, pderiv_signChange, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show C (s i) * signChange s (pderiv i p) *
      (C (s i) * signChange s (N i)) =
      C (s i * s i) * (signChange s (pderiv i p) * signChange s (N i)) by
        rw [map_mul]; ring, hs, map_one, one_mul]

theorem divergence_signField (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (N : Fin (n + 1) → AmbientPoly n) :
    divergence (signField s N) = signChange s (divergence N) := by
  simp only [divergence, signField, pderiv_C_mul, pderiv_signChange, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

theorem divergenceNumerator_signChange (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    divergenceNumerator (signChange s D) (signField s N) =
      signChange s (divergenceNumerator D N) := by
  simp only [divergenceNumerator, divergence_signField s hs,
    directional_signChange s hs, map_sub, map_mul]

theorem signChange_homogeneous (s : Fin (n + 1) → ℂ) {p : AmbientPoly n} {d : ℕ}
    (h : p.IsHomogeneous d) : (signChange s p).IsHomogeneous d := by
  simpa only [signChange, coe_eval₂Hom, one_mul] using
    h.eval₂ C (fun i => C (s i) * X i)
      (fun c => isHomogeneous_C (Fin (n + 1)) c)
      (fun i => isHomogeneous_C_mul_X (s i) i)

theorem signChange_graded (s : Fin (n + 1) → ℂ) {p : AmbientPoly n} {k : ℤ}
    (h : Homogeneous p k) : Homogeneous (signChange s p) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      Homogeneous.of_isHomogeneous (signChange_homogeneous s (h.isHomogeneous hk))
  · rw [h.eq_zero_of_neg (by omega), map_zero]
    exact homogeneous_zero _

theorem signChange_ne_zero (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    {p : AmbientPoly n} (hp : p ≠ 0) : signChange s p ≠ 0 := by
  intro hz
  have ht := congrArg (signChange s) hz
  rw [signChange_twice s hs, map_zero] at ht
  exact hp ht

/-- Pull a certificate through a diagonal sign involution. Polynomial
substitution alone is insufficient: every field component also receives its
coordinate's sign, which is necessary for both derivative identities. -/
theorem Verify.sign_change (s : Fin (n + 1) → ℂ) (hs : ∀ i, s i * s i = 1)
    {F A D Q : AmbientPoly n} {d q : ℕ} {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) :
    Verify (signChange s F) (signChange s A) d q (signChange s D)
      (signField s N) (signChange s Q) where
  hypersurface_ne_zero := signChange_ne_zero s hs h.hypersurface_ne_zero
  hypersurface_homogeneous := signChange_homogeneous s h.hypersurface_homogeneous
  source_homogeneous := signChange_graded s h.source_homogeneous
  denominator_ne_zero := signChange_ne_zero s hs h.denominator_ne_zero
  denominator_homogeneous := by
    rw [(signChange_homogeneous s h.denominator_homogeneous).totalDegree
      (signChange_ne_zero s hs h.denominator_ne_zero)]
    exact signChange_homogeneous s h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    rw [(signChange_homogeneous s h.denominator_homogeneous).totalDegree
      (signChange_ne_zero s hs h.denominator_ne_zero)]
    exact (signChange_graded s (h.numerator_homogeneous i)).C_mul (s i)
  denominator_legal := by
    apply relPrime_of_retract (signChange s) (signChange s) (signChange_involutive s hs)
    simpa only [signChange_twice s hs] using h.denominator_legal
  identity := by
    have hi := congrArg (signChange s) h.identity
    simpa only [defect, directional_signChange s hs,
      divergenceNumerator_signChange s hs, map_add, map_sub, map_mul, map_pow, map_natCast] using hi

def renamedVector (e : Fin (n + 1) ≃ Fin (n + 1)) (N : Fin (n + 1) → AmbientPoly n) :
    Fin (n + 1) → AmbientPoly n := fun i => rename e (N (e.symm i))

theorem rename_directional (e : Fin (n + 1) ≃ Fin (n + 1)) (F : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    HodgeTestbed.directional (rename e F) (renamedVector e N) =
      rename e (HodgeTestbed.directional F N) := by
  unfold HodgeTestbed.directional
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul]

theorem rename_divergence (e : Fin (n + 1) ≃ Fin (n + 1)) (N : Fin (n + 1) → AmbientPoly n) :
    HodgeTestbed.divergence (renamedVector e N) = rename e (HodgeTestbed.divergence N) := by
  unfold HodgeTestbed.divergence
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum]

theorem HasCertificate.rename (e : Fin (n + 1) ≃ Fin (n + 1)) (F A : AmbientPoly n) (q : ℕ)
    (h : HodgeComputer.HasCertificate F q A) :
    HodgeComputer.HasCertificate (MvPolynomial.rename e F) q (MvPolynomial.rename e A) := by
  rw [HodgeComputer.HasCertificate, show (MvPolynomial.rename e F).totalDegree = F.totalDegree from
    totalDegree_renameEquiv e F]
  obtain ⟨D,N,Q,h⟩ := h
  have hD0 : MvPolynomial.rename e D ≠ 0 :=
    (rename_injective _ e.injective).ne (by simpa using h.denominator_ne_zero)
  have hdeg := h.denominator_homogeneous.rename_isHomogeneous (f := e) |>.totalDegree hD0
  refine ⟨MvPolynomial.rename e D,renamedVector e N,MvPolynomial.rename e Q,?_,?_,?_,hD0,?_,?_,?_,?_⟩
  · exact (rename_injective _ e.injective).ne (by simpa using h.hypersurface_ne_zero)
  · exact h.hypersurface_homogeneous.rename_isHomogeneous
  · exact h.source_homogeneous.rename e
  · rw [hdeg]
    exact h.denominator_homogeneous.rename_isHomogeneous
  · intro i
    rw [hdeg]
    exact (h.numerator_homogeneous (e.symm i)).rename e
  · let E := renameEquiv ℂ e
    change IsRelPrime (E F) (E D)
    intro p hp hq
    have h1 : E.symm p ∣ F := by simpa using map_dvd E.symm.toRingHom hp
    have h2 : E.symm p ∣ D := by simpa using map_dvd E.symm.toRingHom hq
    have hu := (h.denominator_legal h1 h2).map E.toRingHom
    simpa using hu
  · have hi := congrArg (MvPolynomial.rename e) h.identity
    change MvPolynomial.rename e (A*D^2-(q : AmbientPoly n)*D*HodgeTestbed.directional F N+
      F*(D*HodgeTestbed.divergence N-HodgeTestbed.directional D N)) =
      MvPolynomial.rename e (F^(q+1)*Q) at hi
    change MvPolynomial.rename e A*(MvPolynomial.rename e D)^2-(q : AmbientPoly n)*MvPolynomial.rename e D*
      HodgeTestbed.directional (MvPolynomial.rename e F) (renamedVector e N)+
      MvPolynomial.rename e F*(MvPolynomial.rename e D*HodgeTestbed.divergence (renamedVector e N)-
        HodgeTestbed.directional (MvPolynomial.rename e D) (renamedVector e N)) =
      (MvPolynomial.rename e F)^(q+1)*MvPolynomial.rename e Q
    rw [rename_directional, rename_directional, rename_divergence]
    simpa only [map_sub, map_add, map_mul, map_pow, map_natCast] using hi

end HodgeComputer
