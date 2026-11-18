import Proposal.GeometricThreefoldCurveEvaluation
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# Mixed contraction to genuine curve differentials

Two independent ambient vectors along a curve and the ordinary Kähler map
define a one-form from each ambient three-form. A vector transverse to the
surface enters before the final projection to the ordinary curve differentials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedCurveForm

open Module CycleQ2GeometricExteriorSheaf CycleQ2LiteralThreefoldResidueContraction
  CycleQ2ThreefoldCurveEvaluation CycleQ2ThreefoldContractionAlongMap
  CycleQ2LiteralThreefoldSurfaceAdjunction CycleQ2LiteralAbelJacobiContraction

section Exterior

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

private abbrev pair (n : ℕ) := exteriorPower.alternatingMapToDual R M n

private theorem pair_interior {n : ℕ} (d : Fin n → Module.Dual R M) (v : Module.Dual R M)
    (ω : ⋀[R]^(n+1) M) : pair n d (interior n v ω) = pair (n+1) (Fin.cons v d) ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [interior_wedge, map_sum, exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, map_smul, exteriorPower.alternatingMapToDual_apply_ιMulti, ← Int.cast_smul_eq_zsmul R,
      Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

private theorem pair_one (v : Module.Dual R M) (ω : ⋀[R]^1 M) :
    v (exteriorPower.oneEquiv R M ω) = pair 1 ![v] ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 1)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [exteriorPower.oneEquiv_ιMulti, exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_unique]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

end Exterior

section Mixed

variable {T C : Type} [CommRing T] [CommRing C] [Algebra ℂ T] [Algebra ℂ C]
  [Algebra T C] [IsScalarTower ℂ T C]

private abbrev E (C : Type) [CommRing C] [Algebra ℂ C] := C × (C × KaehlerDifferential ℂ C)
private abbrev p₀ (C : Type) [CommRing C] [Algebra ℂ C] : E C →ₗ[C] C := LinearMap.fst C C _
private abbrev p₁ (C : Type) [CommRing C] [Algebra ℂ C] : E C →ₗ[C] C :=
  (LinearMap.fst C C _).comp (LinearMap.snd C C _)
private abbrev form (C : Type) [CommRing C] [Algebra ℂ C] : E C →ₗ[C] KaehlerDifferential ℂ C :=
  (LinearMap.snd C C _).comp (LinearMap.snd C C _)

variable (k v : Derivation ℂ T C)

private def graph : KaehlerDifferential ℂ T →ₛₗ[algebraMap T C] E C where
  toFun α := (k.liftKaehlerDifferential α, v.liftKaehlerDifferential α, KaehlerDifferential.map ℂ ℂ T C α)
  map_add' x y := Prod.ext (map_add _ x y) (Prod.ext (map_add _ x y) (map_add _ x y))
  map_smul' r x := Prod.ext
    ((map_smul _ r x).trans (Algebra.smul_def _ _))
    (Prod.ext ((map_smul _ r x).trans (Algebra.smul_def _ _))
      ((map_smul _ r x).trans (IsScalarTower.algebraMap_smul C r _).symm))

/-- First insert the two independently supplied ambient vectors along the same
map, in order, and then project the surviving differential to the curve. -/
def mixed : (⋀[T]^3 (KaehlerDifferential ℂ T)) →ₛₗ[algebraMap T C] KaehlerDifferential ℂ C :=
  (form C).comp <| (exteriorPower.oneEquiv C (E C)).toLinearMap.comp <| (interior 1 (p₁ C)).comp <|
    (interior 2 (p₀ C)).comp <| exteriorMap (algebraMap T C) (graph k v) 3

theorem evaluate_mixed (y : Derivation ℂ C C) (ω : Forms T 3) :
    y.liftKaehlerDifferential (mixed k v ω) = evaluate ![k,v,y.compAlgebraMap T] ω := by
  let e := y.liftKaehlerDifferential.comp (form C)
  let g := exteriorMap (algebraMap T C) (graph k v) 3
  change e (exteriorPower.oneEquiv C (E C) (interior 1 (p₁ C) (interior 2 (p₀ C) (g ω)))) = _
  rw [pair_one, pair_interior, pair_interior]
  have hω : ω ∈ Submodule.span T (Set.range (exteriorPower.ιMulti T 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [show g (exteriorPower.ιMulti T 3 m) = _ from exteriorMap_wedge _ _ _ m,
      exteriorPower.alternatingMapToDual_apply_ιMulti, evaluate_wedge]
    apply congrArg Matrix.det
    ext i j
    fin_cases j
    · rfl
    · rfl
    · exact lift_map y (m i)
  | zero => simp only [map_zero]
  | add x z _ _ hx hz => simp only [map_add, hx, hz]
  | smul r x _ hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]

private theorem evaluate_add_first (k' y : Derivation ℂ T C) (ω : Forms T 3) :
    evaluate ![k + k',v,y] ω = evaluate ![k,v,y] ω + evaluate ![k',v,y] ω := by
  have hω : ω ∈ Submodule.span T (Set.range (exteriorPower.ιMulti T 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    have hl : (k+k').liftKaehlerDifferential = k.liftKaehlerDifferential + k'.liftKaehlerDifferential :=
      (KaehlerDifferential.linearMapEquivDerivation ℂ T (M := C)).symm.map_add k k'
    simp only [evaluate_wedge, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hl, LinearMap.add_apply]
    ring
  | zero => simp only [map_zero, add_zero]
  | add x z _ _ hx hz => simp only [map_add, hx, hz]; abel
  | smul r x _ hx => simp only [map_smulₛₗ, hx, smul_add]

/-- A change of the first ambient vector acts additively on the curve form. -/
theorem mixed_add_left [Module.Projective C (KaehlerDifferential ℂ C)] (k' : Derivation ℂ T C) (ω : Forms T 3) :
    mixed (k+k') v ω = mixed k v ω + mixed k' v ω := by
  apply curve_form_ext
  intro y
  rw [map_add, evaluate_mixed, evaluate_mixed, evaluate_mixed, evaluate_add_first]

theorem mixed_sub_left [Module.Projective C (KaehlerDifferential ℂ C)] (k' : Derivation ℂ T C) (ω : Forms T 3) :
    mixed (k-k') v ω = mixed k v ω - mixed k' v ω := by
  apply eq_sub_iff_add_eq.mpr
  rw [← mixed_add_left, sub_add_cancel]

theorem mixed_swap [Module.Projective C (KaehlerDifferential ℂ C)] (ω : Forms T 3) :
    mixed v k ω = -mixed k v ω := by
  apply curve_form_ext
  intro y
  rw [evaluate_mixed, map_neg, evaluate_mixed, evaluate_swap k]

end Mixed

section Naturality

variable {T C D : Type} [CommRing T] [CommRing C] [CommRing D]
  [Algebra ℂ T] [Algebra ℂ C] [Algebra ℂ D] [Algebra T C] [Algebra T D]
  [IsScalarTower ℂ T C] [IsScalarTower ℂ T D]

private def graphChange (g : C →ₐ[ℂ] D) : E C →ₛₗ[g.toRingHom] E D where
  toFun e := (g e.1, g e.2.1, CycleQ2GeometricAffineOverlap.differentialMap g e.2.2)
  map_add' e e' := Prod.ext (map_add g e.1 e'.1)
    (Prod.ext (map_add g e.2.1 e'.2.1) (map_add _ e.2.2 e'.2.2))
  map_smul' c e := Prod.ext (map_mul g c e.1)
    (Prod.ext (map_mul g c e.2.1) (CycleQ2GeometricAffineOverlap.differentialMap_smul g c e.2.2))

private theorem graph_natural (g : C →ₐ[ℂ] D) (hf : ∀ r : T, g (algebraMap T C r) = algebraMap T D r)
    (k v : Derivation ℂ T C) (k' v' : Derivation ℂ T D)
    (hk : ∀ r, g (k r) = k' r) (hv : ∀ r, g (v r) = v' r) (α : KaehlerDifferential ℂ T) :
    graphChange g (graph k v α) = graph k' v' α := by
  have hα : α ∈ Submodule.span T (Set.range (KaehlerDifferential.D ℂ T)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hα using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r,rfl⟩ := hz
    change (g (k.liftKaehlerDifferential _), g (v.liftKaehlerDifferential _),
      CycleQ2GeometricAffineOverlap.differentialMap g (KaehlerDifferential.map ℂ ℂ T C _)) = _
    simp only [graph, LinearMap.coe_mk, AddHom.coe_mk, Derivation.liftKaehlerDifferential_comp_D,
      KaehlerDifferential.map_D, CycleQ2GeometricAffineOverlap.differentialMap_D, hk, hv, hf]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, hx, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hf]

private theorem one_equiv_change {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (φ : R →+* S) (f : M →ₛₗ[φ] N) (ω : ⋀[R]^1 M) :
    exteriorPower.oneEquiv S N (exteriorMap φ f 1 ω) = f (exteriorPower.oneEquiv R M ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 1)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m,rfl⟩ := hz
    rw [exteriorMap_wedge, exteriorPower.oneEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]

/-- Mixed curve forms restrict along any map of coefficient algebras whenever
both ambient vectors restrict on functions. No smoothness of either ring is required. -/
theorem mixed_natural (g : C →ₐ[ℂ] D) (hf : ∀ r : T, g (algebraMap T C r) = algebraMap T D r)
    (k v : Derivation ℂ T C) (k' v' : Derivation ℂ T D)
    (hk : ∀ r, g (k r) = k' r) (hv : ∀ r, g (v r) = v' r) (ω : Forms T 3) :
    CycleQ2GeometricAffineOverlap.differentialMap g (mixed k v ω) = mixed k' v' ω := by
  have he := exteriorMap_composition (algebraMap T C) g.toRingHom (algebraMap T D)
    (graph k v) (graphChange g) (graph k' v') (fun r => (hf r).symm)
    (fun α => (graph_natural g hf k v k' v' hk hv α).symm) 3 ω
  change CycleQ2GeometricAffineOverlap.differentialMap g ((form C) (exteriorPower.oneEquiv C (E C)
    (interior 1 (p₁ C) (interior 2 (p₀ C) (exteriorMap (algebraMap T C) (graph k v) 3 ω))))) =
      (form D) (exteriorPower.oneEquiv D (E D)
        (interior 1 (p₁ D) (interior 2 (p₀ D) (exteriorMap (algebraMap T D) (graph k' v') 3 ω))))
  rw [he, interior_natural g.toRingHom (graphChange g) (p₀ C) (p₀ D) (fun _ => rfl),
    interior_natural g.toRingHom (graphChange g) (p₁ C) (p₁ D) (fun _ => rfl),
    one_equiv_change]
  rfl

end Naturality

section Tower

variable {T U C : Type} [CommRing T] [CommRing U] [CommRing C]
  [Algebra ℂ T] [Algebra ℂ U] [Algebra ℂ C] [Algebra T U] [Algebra T C] [Algebra U C]
  [IsScalarTower ℂ T U] [IsScalarTower ℂ T C] [IsScalarTower ℂ U C] [IsScalarTower T U C]

theorem comp_tower (y : Derivation ℂ C C) :
    (y.compAlgebraMap U).compAlgebraMap T = y.compAlgebraMap T := by
  ext p
  exact congrArg y (IsScalarTower.algebraMap_apply T U C p).symm

/-- The ambient two-form is contracted against the genuine moving vector
before its surviving slot is restricted to the curve. -/
theorem two_step_eq_mixed [Module.Projective C (KaehlerDifferential ℂ C)]
    (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U)
    (k : Derivation ℂ T C) (hk : ∀ r, algebraMap U C (f (KaehlerDifferential.D ℂ T r)) = k r)
    (v : Derivation ℂ U C) (ω : Forms T 3) :
    contractRestrict v (along 2 (IsScalarTower.toAlgHom ℂ T U) f ω) = mixed k (v.compAlgebraMap T) ω := by
  apply curve_form_ext
  intro y
  rw [evaluate_contractRestrict, evaluate_along f k hk, evaluate_mixed]
  apply congrArg (fun d => evaluate d ω)
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact comp_tower y

/-- Restriction of an ambient covector's scalar values down the coefficient ring
map, retaining every ambient slot on the threefold. -/
def covectorAlong (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U) :
    Derivation ℂ T C :=
  ({ toFun := fun α => algebraMap U C (f α)
     map_add' := fun α β => by rw [map_add, map_add]
     map_smul' := fun r α => by
       rw [map_smulₛₗ, smul_eq_mul, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply T U C]
       rfl } : KaehlerDifferential ℂ T →ₗ[T] C).compDer (KaehlerDifferential.D ℂ T)

omit [IsScalarTower ℂ U C] in
@[simp] theorem covectorAlong_apply
    (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U) (r : T) :
    covectorAlong (C := C) f r = algebraMap U C (f (KaehlerDifferential.D ℂ T r)) := rfl

omit [IsScalarTower ℂ U C] in
theorem covectorAlong_add
    (f g : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U) :
    covectorAlong (C := C) (f+g) = covectorAlong f + covectorAlong g := by
  ext r
  change algebraMap U C ((f+g) _) = algebraMap U C (f _) + algebraMap U C (g _)
  rw [LinearMap.add_apply, map_add]

theorem two_step_covector [Module.Projective C (KaehlerDifferential ℂ C)]
    (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U)
    (v : Derivation ℂ U C) (ω : Forms T 3) :
    contractRestrict v (along 2 (IsScalarTower.toAlgHom ℂ T U) f ω) =
      mixed (covectorAlong f) (v.compAlgebraMap T) ω :=
  two_step_eq_mixed f (covectorAlong f) (fun _ => rfl) v ω

end Tower

end CycleQ2ThreefoldMixedCurveForm
end

#print axioms CycleQ2ThreefoldMixedCurveForm.evaluate_mixed
#print axioms CycleQ2ThreefoldMixedCurveForm.two_step_eq_mixed
#print axioms CycleQ2ThreefoldMixedCurveForm.mixed_add_left
#print axioms CycleQ2ThreefoldMixedCurveForm.two_step_covector
#print axioms CycleQ2ThreefoldMixedCurveForm.mixed_natural
