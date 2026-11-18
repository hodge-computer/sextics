import Proposal.GeometricLiteralThreefoldChartVolume

/-!
# The regular residue frames the affine sextic chart

The four coordinate differentials generate the cotangent module. Their ordered
triple wedges are the signed gradient multiples of the regular residue.
Restriction to the four gradient opens detects equality of coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldChartVolumeFrame

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldChartVolume CycleQ2GeometricExteriorSheaf
  CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap

attribute [local irreducible] seedF chartVolume

variable (i : Fin 4)

private abbrev forms := coordinateForm i (AlgHom.id ℂ (T i))

/-- The coordinate differentials generate the module of differentials on the hypersurface chart. -/
theorem coordinateForms_span :
    Submodule.span (T i) (Set.range (coordinateForm i (AlgHom.id ℂ (T i)))) = ⊤ := by
  change Submodule.span (T i) (Set.range (forms i)) = ⊤
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation ℂ (T i), Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
  change KaehlerDifferential.D ℂ (T i) (mk p) ∈ _
  rw [differential_polynomial mk]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨coordIndex.symm j, ?_⟩
  simp only [forms, coordinateForm, AlgHom.id_apply, coord, Equiv.apply_symm_apply]
  rfl

private theorem omitted_coordinate (s : Set.powersetCard (Fin 4) 3) :
    ∃ j : Fin 4, Set.powersetCard.ofFinEmbEquiv.symm s = Fin.succAboveOrderEmb j := by
  obtain ⟨s, hs⟩ := s
  change s.card = 3 at hs
  have hcard : sᶜ.card = 1 := by simp [Finset.card_compl, hs]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have heq : s = {j}ᶜ := by rw [← hj, compl_compl]
  subst s
  exact ⟨j, Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb j⟩

private theorem unsigned_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (j : ℕ) (a : R) (v w : M) (h : a • v = (-1 : R)^j • w) :
    ((-1 : R)^j * a) • v = w := by
  rw [mul_smul, h, ← mul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]

private theorem wedge_coefficient (s : Set.powersetCard (Fin 4) 3) :
    ∃ c : T i, c • chartVolume i = exteriorPower.ιMulti_family (T i) 3 (forms i) s := by
  obtain ⟨j, hj⟩ := omitted_coordinate s
  refine ⟨(-1 : T i)^j.val * gradient i j, ?_⟩
  let idAlg := AlgHom.id ℂ (T i)
  have he : exteriorDifferentialMap idAlg 3 (chartVolume i) = chartVolume i :=
    exteriorMap_identity idAlg.toRingHom (differentialSemilinearMap idAlg)
      (fun _ => rfl) (fun ω => differentialMap_id ω) 3 (chartVolume i)
  have hw := gradient_smul_chartVolume i (AlgHom.id ℂ (T i)) j
  rw [he] at hw
  change gradient i j • chartVolume i = signedOmitted (T i) (forms i) j at hw
  rw [exteriorPower.ιMulti_family, hj]
  exact unsigned_wedge j.val (gradient i j) (chartVolume i)
    (exteriorPower.ιMulti (T i) 3 (forms i ∘ j.succAbove)) hw

private theorem volume_surjective :
    Function.Surjective (fun c : T i => c • chartVolume i) := by
  let m := LinearMap.toSpanSingleton (T i) (⋀[T i]^3 (KaehlerDifferential ℂ (T i))) (chartVolume i)
  have hle : Submodule.span (T i) (Set.range (exteriorPower.ιMulti_family (T i) 3 (forms i))) ≤
      LinearMap.range m := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact wedge_coefficient i s
  have htop := exteriorPower.ιMulti_family_span_of_span (n := 3) (T i) (coordinateForms_span i)
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (htop ▸ hle) : LinearMap.range m = ⊤)

private theorem volume_injective :
    Function.Injective (fun c : T i => c • chartVolume i) := by
  intro c d h
  obtain ⟨v, hv⟩ := chartBezout i
  have hs : Ideal.span (Set.range (gradient i)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_range_iff_exists_fun.mpr ⟨v, hv⟩)
  apply Localization.algebraMap_injective_of_span_eq_top _ hs
  funext a
  obtain ⟨a, ⟨j, rfl⟩⟩ := a
  have hp := (Function.bijective_iff_existsUnique _).mpr (patchResidue_frame i j)
  simp only [Pi.algebraMap_apply]
  apply hp.injective
  have eq := congrArg (exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) 3) h
  simp only [map_smulₛₗ] at eq
  rw [chartVolume_on_patch i j] at eq
  simpa only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom] using eq

/-- Every chart three-form has a unique coefficient in the regular residue frame. -/
theorem chartVolume_bijective :
    Function.Bijective (fun c : T i => c • chartVolume i) :=
  ⟨volume_injective i, volume_surjective i⟩

/-- Trivialization of the canonical module of the original affine threefold chart. -/
def chartVolumeEquiv : (T i) ≃ₗ[T i] (⋀[T i]^3 (KaehlerDifferential ℂ (T i))) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (T i) _ (chartVolume i)) (chartVolume_bijective i)

end CycleQ2LiteralThreefoldChartVolumeFrame
end

#print axioms CycleQ2LiteralThreefoldChartVolumeFrame.chartVolume_bijective
#print axioms CycleQ2LiteralThreefoldChartVolumeFrame.chartVolumeEquiv
