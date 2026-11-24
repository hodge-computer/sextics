import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricExteriorSheaf

/-!
# Contraction against a surface two-form

On a rank-two module, taking the wedge with a contracted two-form
evaluates the covector on the vector and multiplies the original form.
The contraction is intrinsic and the frame is used only in the proof.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSurfaceWedge

open Module CycleQ2GeometricSurfaceAdjunction

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Interior multiplication of a two-form by a vector in the dual of its
module of one-forms. -/
def contract (v : M →ₗ[R] R) : (⋀[R]^2 M) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv
    { toFun := fun m => v (m 0) • m 1 - v (m 1) • m 0
      map_update_add' := by
        intro _ m i x y
        fin_cases i <;> simp [Function.update, add_smul, smul_add] <;> abel
      map_update_smul' := by
        intro _ m i r x
        fin_cases i <;> simp [Function.update, smul_sub, smul_smul, mul_comm]
      map_eq_zero_of_eq' := by
        intro m i j he hne
        fin_cases i <;> fin_cases j <;> simp_all }

theorem contract_wedge (v : M →ₗ[R] R) (a b : M) :
    contract v (exteriorPower.ιMulti R 2 ![a, b]) = v a • b - v b • a := by
  rw [contract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem wedge_contract (b : Basis (Fin 2) R M) (v : M →ₗ[R] R)
    (c : M) (w : ⋀[R]^2 M) :
    exteriorPower.ιMulti R 2 ![c, contract v w] = v c • w := by
  have hw : determinantEquiv b w • exteriorPower.ιMulti R 2 b = w := by
    apply (determinantEquiv b).injective
    rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]
  have hv := congrArg v (basis_two_decomposition b c)
  simp only [map_add, map_smul, smul_eq_mul] at hv
  have hb : contract v (exteriorPower.ιMulti R 2 b) = v (b 0) • b 1 - v (b 1) • b 0 := by
    rw [contract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  have hc : contract v w = determinantEquiv b w • (v (b 0) • b 1 - v (b 1) • b 0) := by
    calc
      _ = contract v (determinantEquiv b w • exteriorPower.ιMulti R 2 b) := congrArg (contract v) hw.symm
      _ = _ := by rw [map_smul, hb]
  apply (determinantEquiv b).injective
  rw [determinantEquiv_pair, map_smul, hc, ← hv]
  simp [smul_eq_mul, Basis.repr_self]
  ring

section Restriction

open CycleQ2GeometricExteriorSheaf

variable {R S M N : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

/-- Restriction of a tangent and a two-form commutes with contraction. -/
theorem contract_natural (φ : R →+* S) (f : M →ₛₗ[φ] N)
    (v : M →ₗ[R] R) (u : N →ₗ[S] S) (h : ∀ x, u (f x) = φ (v x)) (w : ⋀[R]^2 M) :
    contract u (exteriorMap φ f 2 w) = f (contract v w) := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [exteriorMap_wedge, contract, contract,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      change u (f (a 0)) • f (a 1) - u (f (a 1)) • f (a 0) =
        f (v (a 0) • a 1 - v (a 1) • a 0)
      rw [h, h, map_sub, map_smulₛₗ, map_smulₛₗ]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]

end Restriction

end CycleQ2LiteralAbelJacobiSurfaceWedge
end

#print axioms CycleQ2LiteralAbelJacobiSurfaceWedge.wedge_contract
#print axioms CycleQ2LiteralAbelJacobiSurfaceWedge.contract_natural
