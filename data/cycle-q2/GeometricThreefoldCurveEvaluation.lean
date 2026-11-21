import Proposal.GeometricLiteralThreefoldSurfaceAdjunction
import Proposal.GeometricThreefoldContractionAlongMap
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Evaluating interior products along a sequence of affine chart maps

Evaluation of a contracted exterior form on tangent vectors is evaluation
of the initial form with one more argument. On a smooth curve chart its
ordinary differentials are detected by their values on ring derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldCurveEvaluation

open CycleQ2ThreefoldContractionAlongMap CycleQ2GeometricAffineOverlap
  CycleQ2LiteralThreefoldSurfaceAdjunction CycleQ2LiteralAbelJacobiContraction

section Towers

variable {R S C : Type} [CommRing R] [CommRing S] [CommRing C]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ C] [Algebra R S] [Algebra R C] [Algebra S C]
  [IsScalarTower ℂ R S] [IsScalarTower ℂ R C] [IsScalarTower ℂ S C] [IsScalarTower R S C]

private abbrev hom (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    [Algebra R S] [IsScalarTower ℂ R S] := IsScalarTower.toAlgHom ℂ R S

theorem lift_map (y : Derivation ℂ S C) (α : KaehlerDifferential ℂ R) :
    y.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R S α) =
      (y.compAlgebraMap R).liftKaehlerDifferential α := by
  let f := (y.liftKaehlerDifferential.restrictScalars R).comp (KaehlerDifferential.map ℂ ℂ R S)
  have h : f = (y.compAlgebraMap R).liftKaehlerDifferential := by
    apply Derivation.liftKaehlerDifferential_unique
    ext r
    change y.liftKaehlerDifferential (KaehlerDifferential.map ℂ ℂ R S (KaehlerDifferential.D ℂ R r)) = _
    simp only [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
    exact (Derivation.liftKaehlerDifferential_comp_D (y.compAlgebraMap R) r).symm
  exact LinearMap.congr_fun h α

private theorem lift_differentialMap (y : Derivation ℂ S C) (α : KaehlerDifferential ℂ R) :
    y.liftKaehlerDifferential (differentialMap (hom R S) α) = (y.compAlgebraMap R).liftKaehlerDifferential α := by
  have hα : α ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℂ R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hα using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r,rfl⟩ := hz
    rw [differentialMap_D, Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [differentialMap_smul, map_smul, map_smul, hx]
    exact IsScalarTower.algebraMap_smul S r _

variable (f : KaehlerDifferential ℂ R →ₛₗ[(hom R S).toRingHom] S) (k : Derivation ℂ R C)
    (hk : ∀ r, algebraMap S C (f (KaehlerDifferential.D ℂ R r)) = k r)

include hk

omit [IsScalarTower ℂ S C] in
private theorem lift_covector (α : KaehlerDifferential ℂ R) :
    algebraMap S C (f α) = k.liftKaehlerDifferential α := by
  have hα : α ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℂ R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hα using Submodule.span_induction with
  | mem z hz => obtain ⟨r,rfl⟩ := hz; rw [Derivation.liftKaehlerDifferential_comp_D, hk]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smulₛₗ, smul_eq_mul, map_mul, hx, map_smul, Algebra.smul_def]
    rw [IsScalarTower.algebraMap_apply R S C]
    rfl

/-- Laplace expansion in the first argument computes evaluation of the actual interior product. -/
theorem evaluate_along {n : ℕ} (d : Fin n → Derivation ℂ S C) (ω : Forms R (n+1)) :
    evaluate d (along n (hom R S) f ω) =
      evaluate (Fin.cons k (fun j => (d j).compAlgebraMap R)) ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [along_wedge, map_sum, evaluate_wedge, Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, map_smulₛₗ, evaluate_wedge, ← Int.cast_smul_eq_zsmul C, Int.cast_pow,
      Int.cast_neg, Int.cast_one, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    congr 1
    · rw [lift_covector f k hk]
      rfl
    · apply congrArg Matrix.det
      ext a b
      exact lift_differentialMap (d b) (m (j.succAbove a))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hx, IsScalarTower.algebraMap_apply R S C]
    rfl

end Towers

section LastArgument

variable {Q C : Type} [CommRing Q] [CommRing C] [Algebra ℂ Q] [Algebra ℂ C]
  [Algebra Q C] [IsScalarTower ℂ Q C]

theorem evaluate_contractRestrict (v : Derivation ℂ Q C) (y : Derivation ℂ C C) (ω : Forms Q 2) :
    y.liftKaehlerDifferential (contractRestrict v ω) = evaluate ![v,y.compAlgebraMap Q] ω := by
  have hω : ω ∈ Submodule.span Q (Set.range (exteriorPower.ιMulti Q 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    have hm : m = ![m 0,m 1] := by funext i; fin_cases i <;> rfl
    rw [hm, contractRestrict_wedge, map_sub, map_smul, map_smul, lift_map, lift_map,
      evaluate_wedge, Matrix.det_fin_two]
    change _ = _ * _ - _ * _
    simp only [smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smul, ← IsScalarTower.algebraMap_smul C, map_smul, hx, map_smulₛₗ]

end LastArgument

/-- Projectivity of the actual Kähler module makes all curve derivations jointly detect one-forms. -/
theorem curve_form_ext {C : Type} [CommRing C] [Algebra ℂ C] [Module.Projective C (KaehlerDifferential ℂ C)]
    {α β : KaehlerDifferential ℂ C} (h : ∀ y : Derivation ℂ C C,
      y.liftKaehlerDifferential α = y.liftKaehlerDifferential β) : α = β := by
  apply Module.eval_apply_injective C
  apply LinearMap.ext
  intro g
  let y := (KaehlerDifferential.linearMapEquivDerivation ℂ C) g
  have hy : y.liftKaehlerDifferential = g :=
    (KaehlerDifferential.linearMapEquivDerivation ℂ C).symm_apply_apply g
  exact (congrArg (fun z => z α) hy.symm).trans ((h y).trans (congrArg (fun z => z β) hy))

end CycleQ2ThreefoldCurveEvaluation
end

#print axioms CycleQ2ThreefoldCurveEvaluation.evaluate_along
#print axioms CycleQ2ThreefoldCurveEvaluation.evaluate_contractRestrict
#print axioms CycleQ2ThreefoldCurveEvaluation.curve_form_ext
