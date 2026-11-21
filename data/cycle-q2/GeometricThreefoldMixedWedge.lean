import Proposal.GeometricThreefoldMixedCurveForm

/-!
# Mixed contraction on exterior generators

Inserting the first ambient vector leaves a sum of wedges of pairs. Inserting
the second vector gives a difference of ordinary curve differentials in each
summand. This formula applies over any coefficient algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedWedge

open CycleQ2GeometricExteriorSheaf CycleQ2LiteralThreefoldResidueContraction
  CycleQ2ThreefoldContractionAlongMap CycleQ2ThreefoldMixedCurveForm
  CycleQ2ThreefoldCurveEvaluation CycleQ2LiteralAbelJacobiContraction

section Mixed
variable {T C : Type} [CommRing T] [CommRing C] [Algebra ℂ T] [Algebra ℂ C]
  [Algebra T C] [IsScalarTower ℂ T C]

/-- The binary contraction of the two slots surviving the first insertion. -/
def pairValue (v : Derivation ℂ T C) (m : Fin 2 → KaehlerDifferential ℂ T) :
    KaehlerDifferential ℂ C :=
  v.liftKaehlerDifferential (m 0) • KaehlerDifferential.map ℂ ℂ T C (m 1) -
    v.liftKaehlerDifferential (m 1) • KaehlerDifferential.map ℂ ℂ T C (m 0)

private theorem pairValue_sum (v : Derivation ℂ T C) (a : Fin 2 → KaehlerDifferential ℂ T) :
    (∑ l : Fin 2, (-1 : ℤ)^l.val • (v.liftKaehlerDifferential (a l) •
      KaehlerDifferential.map ℂ ℂ T C (l.removeNth a 0))) = pairValue v a := by
  rw [Fin.sum_univ_two]
  change (-1 : ℤ)^0 • (v.liftKaehlerDifferential (a 0) • KaehlerDifferential.map ℂ ℂ T C (a 1)) +
      (-1 : ℤ)^1 • (v.liftKaehlerDifferential (a 1) • KaehlerDifferential.map ℂ ℂ T C (a 0)) = _
  simp [pairValue, sub_eq_add_neg]

theorem mixed_wedge (k v : Derivation ℂ T C) (m : Fin 3 → KaehlerDifferential ℂ T) :
    mixed k v (exteriorPower.ιMulti T 3 m) =
      ∑ j : Fin 3, (-1 : ℤ)^j.val • (k.liftKaehlerDifferential (m j) •
        pairValue v (j.removeNth m)) := by
  simp only [mixed, LinearMap.comp_apply, exteriorMap_wedge, interior_wedge,
    map_sum, map_zsmul, map_smul, LinearEquiv.coe_coe,
    exteriorPower.oneEquiv_ιMulti]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x : KaehlerDifferential ℂ C => (-1 : ℤ)^j.val •
    (k.liftKaehlerDifferential (m j) • x)) (pairValue_sum v (j.removeNth m))

/-- Additivity in the first ambient vector for an arbitrary coefficient algebra. -/
theorem mixed_add_left (k v k' : Derivation ℂ T C) (ω : Forms T 3) :
    mixed (k + k') v ω = mixed k v ω + mixed k' v ω := by
  have h : mixed (k + k') v = mixed k v + mixed k' v := by
    apply LinearMap.ext_on_range (exteriorPower.ιMulti_span T 3 (KaehlerDifferential ℂ T))
    intro m
    have he := (KaehlerDifferential.linearMapEquivDerivation ℂ T (M := C)).symm.map_add k k'
    change (k+k').liftKaehlerDifferential = k.liftKaehlerDifferential + k'.liftKaehlerDifferential at he
    simp only [LinearMap.add_apply, mixed_wedge, he, add_smul, smul_add, Finset.sum_add_distrib]
  exact LinearMap.congr_fun h ω

theorem mixed_sub_left (k v k' : Derivation ℂ T C) (ω : Forms T 3) :
    mixed (k-k') v ω = mixed k v ω - mixed k' v ω := by
  apply eq_sub_iff_add_eq.mpr
  rw [← mixed_add_left, sub_add_cancel]

end Mixed

section Tower
variable {T U C : Type} [CommRing T] [CommRing U] [CommRing C]
  [Algebra ℂ T] [Algebra ℂ U] [Algebra ℂ C] [Algebra T U] [Algebra T C] [Algebra U C]
  [IsScalarTower ℂ T U] [IsScalarTower ℂ T C] [IsScalarTower ℂ U C] [IsScalarTower T U C]

open CycleQ2GeometricAffineOverlap CycleQ2EtaleExteriorMapBinding

private theorem contract_pair (v : Derivation ℂ U C) (m : Fin 2 → KaehlerDifferential ℂ T) :
    contractRestrict v (exteriorPower.ιMulti U 2
      (fun i => differentialMap (IsScalarTower.toAlgHom ℂ T U) (m i))) =
        pairValue (v.compAlgebraMap T) m := by
  let g := differentialMap (IsScalarTower.toAlgHom ℂ T U)
  have he : (fun i => g (m i)) = ![g (m 0), g (m 1)] := by
    funext i
    fin_cases i <;> rfl
  change contractRestrict v (exteriorPower.ιMulti U 2 (fun i => g (m i))) = _
  rw [he, contractRestrict_wedge]
  have hx (α : KaehlerDifferential ℂ T) : KaehlerDifferential.map ℂ ℂ U C (g α) =
      KaehlerDifferential.map ℂ ℂ T C α := by
    change KaehlerDifferential.map ℂ ℂ U C (differentialMap (IsScalarTower.toAlgHom ℂ T U) α) = _
    rw [differentialMap_algebraMap]
    exact CycleQ2NormalAdjunctionNaturality.differentialRestriction_tower T U C α
  rw [hx, hx]
  simp only [g, differentialMap_algebraMap, lift_map, pairValue]

/-- Two-step contraction and direct mixed contraction give the same ordinary
one-form over arbitrary coefficient rings. -/
theorem two_step_eq_mixed (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U)
    (k : Derivation ℂ T C) (hk : ∀ r, algebraMap U C (f (KaehlerDifferential.D ℂ T r)) = k r)
    (v : Derivation ℂ U C) (ω : Forms T 3) :
    contractRestrict v (along 2 (IsScalarTower.toAlgHom ℂ T U) f ω) = mixed k (v.compAlgebraMap T) ω := by
  have hf (α : KaehlerDifferential ℂ T) : algebraMap U C (f α) = k.liftKaehlerDifferential α := by
    have hα : α ∈ Submodule.span T (Set.range (KaehlerDifferential.D ℂ T)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hα using Submodule.span_induction with
    | mem z hz => obtain ⟨r,rfl⟩ := hz; rw [Derivation.liftKaehlerDifferential_comp_D, hk]
    | zero => simp only [map_zero]
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | smul r x _ hx =>
      rw [f.map_smulₛₗ, smul_eq_mul, map_mul, hx, map_smul, Algebra.smul_def,
        IsScalarTower.algebraMap_apply T U C]
      rfl
  have hω : ω ∈ Submodule.span T (Set.range (exteriorPower.ιMulti T 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m,rfl⟩ := hz
      rw [along_wedge, mixed_wedge, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_zsmul, map_smul, contract_pair v (j.removeNth m)]
      rw [← IsScalarTower.algebraMap_smul C (f (m j)), hf]
  | zero => simp only [map_zero]
  | add x z _ _ hx hz => simp only [map_add, hx, hz]
  | smul r x _ hx =>
      rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, hx]
      change (algebraMap T U r) • _ = (algebraMap T C r) • _
      rw [← IsScalarTower.algebraMap_smul C, ← IsScalarTower.algebraMap_apply T U C]

theorem two_step_covector (f : KaehlerDifferential ℂ T →ₛₗ[(IsScalarTower.toAlgHom ℂ T U).toRingHom] U)
    (v : Derivation ℂ U C) (ω : Forms T 3) :
    contractRestrict v (along 2 (IsScalarTower.toAlgHom ℂ T U) f ω) =
      mixed (covectorAlong f) (v.compAlgebraMap T) ω :=
  two_step_eq_mixed f (covectorAlong f) (fun _ => rfl) v ω

end Tower

end CycleQ2ThreefoldMixedWedge
end

#print axioms CycleQ2ThreefoldMixedWedge.mixed_wedge
#print axioms CycleQ2ThreefoldMixedWedge.mixed_add_left
#print axioms CycleQ2ThreefoldMixedWedge.two_step_eq_mixed
