import HodgeComputer.Sextic
import HodgeComputer.Verify

/-! Transport of the certificate under a permutation of its six coordinates. -/
noncomputable section
namespace CyclicTriple
open MvPolynomial
open scoped BigOperators

private def renamedVector (e : Fin 6 ≃ Fin 6) (N : Fin 6 → HodgeComputer.Sextic.Poly) :
    Fin 6 → HodgeComputer.Sextic.Poly := fun i => rename e (N (e.symm i))

theorem rename_directional (e : Fin 6 ≃ Fin 6) (F : HodgeComputer.Sextic.Poly)
    (N : Fin 6 → HodgeComputer.Sextic.Poly) :
    HodgeTestbed.directional (rename e F) (renamedVector e N) =
      rename e (HodgeTestbed.directional F N) := by
  unfold HodgeTestbed.directional
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul]

theorem rename_divergence (e : Fin 6 ≃ Fin 6) (N : Fin 6 → HodgeComputer.Sextic.Poly) :
    HodgeTestbed.divergence (renamedVector e N) = rename e (HodgeTestbed.divergence N) := by
  unfold HodgeTestbed.divergence
  rw [← Equiv.sum_comp e]
  simp only [renamedVector, Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum]

theorem certificate_rename (e : Fin 6 ≃ Fin 6) (F A : HodgeComputer.Sextic.Poly) (q : ℕ)
    (h : HodgeComputer.HasCertificate F A 6 q) :
    HodgeComputer.HasCertificate (rename e F) (rename e A) 6 q := by
  obtain ⟨D,N,Q,h⟩ := h
  have hD0 : rename e D ≠ 0 :=
    (rename_injective _ e.injective).ne (by simpa using h.denominator_ne_zero)
  have hdeg := h.denominator_homogeneous.rename_isHomogeneous (f := e) |>.totalDegree hD0
  refine ⟨rename e D,renamedVector e N,rename e Q,?_,?_,?_,hD0,?_,?_,?_,?_⟩
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
  · have hi := congrArg (rename e) h.identity
    change rename e (A*D^2-(q : HodgeComputer.Sextic.Poly)*D*HodgeTestbed.directional F N+
      F*(D*HodgeTestbed.divergence N-HodgeTestbed.directional D N)) =
      rename e (F^(q+1)*Q) at hi
    change rename e A*(rename e D)^2-(q : HodgeComputer.Sextic.Poly)*rename e D*
      HodgeTestbed.directional (rename e F) (renamedVector e N)+
      rename e F*(rename e D*HodgeTestbed.divergence (renamedVector e N)-
        HodgeTestbed.directional (rename e D) (renamedVector e N)) =
      (rename e F)^(q+1)*rename e Q
    rw [rename_directional, rename_directional, rename_divergence]
    simpa only [map_sub, map_add, map_mul, map_pow, map_natCast] using hi

def coordinateOrder : Fin 6 ≃ Fin 6 where
  toFun := ![3,4,0,1,5,2]
  invFun := ![2,3,5,0,1,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

end CyclicTriple
#print axioms CyclicTriple.certificate_rename
