import Proposal.GeometricLiteralThreefoldResidueContraction

/-!
# Contraction with a volume form in rank three

The three ordered complementary wedges are a basis for the exterior square.
In this basis contraction with the ordered volume has the three coefficients
of the covector, with alternating signs. This gives an isomorphism over any
commutative ring, including after scaling the volume by a unit.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeEulerContraction

open CycleQ2LiteralThreefoldResidueContraction

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

private def omitIndex (j : Fin 3) : Set.powersetCard (Fin 3) 2 :=
  ⟨{j}ᶜ, by simp [Finset.card_compl]⟩

private def omitEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 := by
  apply Equiv.ofBijective omitIndex
  constructor
  · intro i j h
    have he := congrArg (fun s : Set.powersetCard (Fin 3) 2 => (s : Finset (Fin 3))ᶜ) h
    simpa only [omitIndex, compl_compl, Finset.singleton_inj] using he
  · intro s
    have hc : ((s : Finset (Fin 3))ᶜ).card = 1 := by simp [Finset.card_compl]
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    refine ⟨j, Subtype.ext ?_⟩
    change {j}ᶜ = (s : Finset (Fin 3))
    rw [← hj, compl_compl]

def twoBasis (b : Module.Basis (Fin 3) R M) : Module.Basis (Fin 3) R (⋀[R]^2 M) :=
  (b.exteriorPower 2).reindex omitEquiv.symm

theorem twoBasis_apply (b : Module.Basis (Fin 3) R M) (j : Fin 3) :
    twoBasis b j = exteriorPower.ιMulti R 2 (j.removeNth b) := by
  rw [twoBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change b.exteriorPower 2 (omitIndex j) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext k
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply, omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

private def signs : (Fin 3 → R) ≃ₗ[R] (Fin 3 → R) where
  toFun v j := (-1 : R)^j.val * v j
  invFun v j := (-1 : R)^j.val * v j
  left_inv v := by
    funext j
    change (-1 : R)^j.val * ((-1 : R)^j.val * v j) = v j
    rw [← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]
  right_inv v := by
    funext j
    change (-1 : R)^j.val * ((-1 : R)^j.val * v j) = v j
    rw [← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]
  map_add' v w := by funext j; exact mul_add _ _ _
  map_smul' a v := by funext j; exact mul_left_comm _ _ _

def contractionEquiv (b : Module.Basis (Fin 3) R M) : (M →ₗ[R] R) ≃ₗ[R] (⋀[R]^2 M) :=
  ((b.constr R).symm.trans signs).trans (twoBasis b).equivFun.symm

theorem contractionEquiv_apply (b : Module.Basis (Fin 3) R M) (v : M →ₗ[R] R) :
    contractionEquiv b v = interior 2 v (exteriorPower.ιMulti R 3 b) := by
  change (twoBasis b).equivFun.symm (fun j => (-1 : R)^j.val * v (b j)) = _
  rw [Module.Basis.equivFun_symm_apply, interior_wedge]
  apply Finset.sum_congr rfl
  intro j _
  rw [twoBasis_apply, ← Int.cast_smul_eq_zsmul R, ← mul_smul, Int.cast_pow, Int.cast_neg, Int.cast_one]

def unitContractionEquiv (b : Module.Basis (Fin 3) R M) (u : Rˣ) :
    (M →ₗ[R] R) ≃ₗ[R] (⋀[R]^2 M) :=
  (contractionEquiv b).trans (LinearEquiv.smulOfUnit u)

theorem unitContractionEquiv_apply (b : Module.Basis (Fin 3) R M) (u : Rˣ) (v : M →ₗ[R] R) :
    unitContractionEquiv b u v = interior 2 v ((u : R) • exteriorPower.ιMulti R 3 b) := by
  change (u : R) • contractionEquiv b v = _
  rw [contractionEquiv_apply, map_smul]

end CycleQ2HodgeEulerContraction
end

#print axioms CycleQ2HodgeEulerContraction.unitContractionEquiv_apply
