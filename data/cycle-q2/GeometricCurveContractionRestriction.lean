import Proposal.GeometricLiteralThreefoldMixedChartChange
import Proposal.GeometricLiteralAbelJacobiContraction

/-!
# Restricting a curve-valued contraction through its coefficient homomorphism

An ambient two-form contracted by a vector along a curve gives the same
one-form after restriction of the curve coefficients. On a principal
localization it suffices to compare the velocities on the original chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2CurveContractionRestriction
open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldMixedChartChange CycleQ2GeometricAffineOverlap

variable {U C D : Type} [CommRing U] [CommRing C] [CommRing D]
  [Algebra ℂ U] [Algebra ℂ C] [Algebra ℂ D] [Algebra U C] [Algebra U D]
  [IsScalarTower ℂ U C] [IsScalarTower ℂ U D]

private theorem exact_pair {R A : Type} [CommRing R] [CommRing A] [Algebra ℂ R] [Algebra ℂ A]
    [Algebra R A] [IsScalarTower ℂ R A] (v : Derivation ℂ R A) (r s : R) :
    contractRestrict v (exteriorPower.ιMulti R 2 ![KaehlerDifferential.D ℂ R r, KaehlerDifferential.D ℂ R s]) =
      v r • KaehlerDifferential.D ℂ A (algebraMap R A s) -
      v s • KaehlerDifferential.D ℂ A (algebraMap R A r) := by
  rw [contractRestrict_wedge, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D]

variable (f : C →ₐ[ℂ] D) (hf : ∀ x : U, f (algebraMap U C x) = algebraMap U D x)
  (v : Derivation ℂ U C) (w : Derivation ℂ U D)

include hf in
theorem contract_natural (hv : ∀ x : U, f (v x) = w x) (ω : ⋀[U]^2 (KaehlerDifferential ℂ U)) :
    differentialMap f (contractRestrict v ω) = contractRestrict w ω := by
  let d := KaehlerDifferential.D ℂ U
  have hm : ω ∈ Submodule.span U (exteriorPower.ιMulti U 2 ''
      {m : Fin 2 → KaehlerDifferential ℂ U | Set.range m ⊆ Set.range d}) := by
    rw [exteriorPower.ιMulti_span_of_span U 2 _ (KaehlerDifferential.span_range_derivation ℂ U)]
    trivial
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,hm,rfl⟩ := hz
    choose r hr using (fun a : Fin 2 => hm (Set.mem_range_self a))
    have he : m = ![d (r 0),d (r 1)] := by
      funext a
      fin_cases a
      · exact (hr 0).symm
      · exact (hr 1).symm
    rw [he, exact_pair, exact_pair, map_sub, differentialMap_smul, differentialMap_smul, differentialMap_D, differentialMap_D]
    simp only [hf, hv]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [(contractRestrict v).map_smul, (contractRestrict w).map_smul,
      ← IsScalarTower.algebraMap_smul C r (contractRestrict v x), differentialMap_smul, hf, hx,
      IsScalarTower.algebraMap_smul]

variable {R : Type} [CommRing R] [Algebra ℂ R] [Algebra R U] [IsScalarTower ℂ R U]

include hf in
theorem velocity_ext (m : Submonoid R) [IsLocalization m U]
    (hr : ∀ r : R, f (v (algebraMap R U r)) = w (algebraMap R U r)) :
    ∀ x : U, f (v x) = w x := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower U C D := IsScalarTower.of_algebraMap_eq fun r => (hf r).symm
  let h := (algebraMap U D).comp (algebraMap R U)
  let := h.toAlgebra
  let : IsScalarTower R U D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower ℂ R D := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ D c = algebraMap U D (algebraMap R U (algebraMap ℂ R c))
    rw [← IsScalarTower.algebraMap_apply ℂ R U, ← IsScalarTower.algebraMap_apply ℂ U D]
  let v' := ((Algebra.linearMap C D).restrictScalars U).compDer v
  have hd : v'.compAlgebraMap R = w.compAlgebraMap R := by ext r; exact hr r
  let huniq := existsUnique_localized_vector (U := U) m (w.compAlgebraMap R)
  have eq := huniq.unique hd rfl
  exact fun x => congrArg (fun y : Derivation ℂ U D => y x) eq

end CycleQ2CurveContractionRestriction
end

#print axioms CycleQ2CurveContractionRestriction.contract_natural
#print axioms CycleQ2CurveContractionRestriction.velocity_ext
