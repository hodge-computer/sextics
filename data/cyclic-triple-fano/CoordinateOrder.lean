import HodgeComputer.Verify

/-! Transport of the certificate under a permutation of its six coordinates. -/
noncomputable section
namespace CyclicTriple
open MvPolynomial
open scoped BigOperators

private def renamedVector (e : Fin 6 ≃ Fin 6) (N : Fin 6 → HodgeComputer.Poly) :
    Fin 6 → HodgeComputer.Poly := fun i => rename e (N (e.symm i))

theorem rename_directional (e : Fin 6 ≃ Fin 6) (F : HodgeComputer.Poly)
    (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.directional (rename e F) (renamedVector e N) =
      rename e (HodgeTestbed.directional F N) := by
  unfold HodgeTestbed.directional
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul]

theorem rename_divergence (e : Fin 6 ≃ Fin 6) (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.divergence (renamedVector e N) = rename e (HodgeTestbed.divergence N) := by
  unfold HodgeTestbed.divergence
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum]

theorem certificate_rename (e : Fin 6 ≃ Fin 6) (F A : HodgeComputer.Poly) (q : ℕ)
    (h : HodgeComputer.HasCertificate F A q) :
    HodgeComputer.HasCertificate (rename e F) (rename e A) q := by
  obtain ⟨d,D,N,Q,h⟩ := h
  refine ⟨d,rename e D,renamedVector e N,rename e Q,?_,?_,?_,?_,?_⟩
  · exact (rename_injective _ e.injective).ne (by simpa using h.denominator_ne_zero)
  · exact h.denominator_homogeneous.rename_isHomogeneous
  · intro i
    exact (h.numerator_homogeneous (e.symm i)).rename_isHomogeneous
  · let E := renameEquiv ℂ e
    change IsRelPrime (E F) (E D)
    intro p hp hq
    have h1 : E.symm p ∣ F := by simpa using map_dvd E.symm.toRingHom hp
    have h2 : E.symm p ∣ D := by simpa using map_dvd E.symm.toRingHom hq
    have hu := (h.denominator_legal h1 h2).map E.toRingHom
    simpa using hu
  · have hi := congrArg (rename e) h.identity
    simpa only [HodgeComputer.defect, HodgeTestbed.divergenceNumerator,
      rename_directional, rename_divergence, map_sub, map_add, map_mul,
      map_pow, map_natCast] using hi

def coordinateOrder : Fin 6 ≃ Fin 6 where
  toFun := ![3,4,0,1,5,2]
  invFun := ![2,3,5,0,1,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

end CyclicTriple
#print axioms CyclicTriple.certificate_rename
