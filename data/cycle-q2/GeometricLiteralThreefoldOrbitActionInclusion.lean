import Proposal.GeometricLiteralThreefoldOrbitActionCharts
import Proposal.GeometricLiteralAbelJacobiQChartTarget

/-! The triangular chart substitution is the restriction of the projective
threefold automorphism on each of its four fixed coordinate charts.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitAction

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
  CycleQ2SeedCyclicAction CycleQ2LiteralOrbitAction CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceFamilyContainment CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCylinder CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiQCoordinates
  CycleQ2LiteralAbelJacobiQChartTarget

private abbrev q := Ideal.Quotient.mk (sexticIdeal point)
private abbrev G := sexticGrade point

private theorem char_mul (z w : ℂ) (j : Fin 5) : char (z*w) j = char z j * char w j := by
  fin_cases j <;> simp [char, mul_pow]

private theorem polynomialAction_comp (z w : ℂ) :
    (polynomialAction z).comp (polynomialAction w) = polynomialAction (z*w) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, action_X, map_mul, polynomialAction_C, char_mul]
  ring

theorem nativeGradedAction_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (nativeGradedAction z hz).comp (nativeGradedAction w hw) =
      nativeGradedAction (z*w) (cubeRoot_mul hz hw) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg q (AlgHom.congr_fun (polynomialAction_comp z w) p)

theorem nativeAction_hom_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (nativeAction z hz).hom ≫ (nativeAction w hw).hom =
      (nativeAction (z*w) (cubeRoot_mul hz hw)).hom := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  simp only [nativeGradedAction_comp]

theorem threefoldAction_hom_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (threefoldAction z hz).hom ≫ (threefoldAction w hw).hom =
      (threefoldAction (z*w) (cubeRoot_mul hz hw)).hom := by
  simp only [threefoldAction, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (nativeAction z hz).hom, nativeAction_hom_comp]

theorem threefoldAction_hom_one : (threefoldAction 1 (one_pow 3)).hom = 𝟙 _ := by
  apply (cancel_epi (threefoldAction 1 (one_pow 3)).hom).mp
  simpa only [mul_one, Category.comp_id] using
    threefoldAction_hom_comp 1 1 (one_pow 3) (one_pow 3)

private theorem coefficient_mem (c : ℂ) : q (C c) ∈ G 0 :=
  ⟨C c, isWeightedHomogeneous_C geometricWeight c, rfl⟩

theorem denominator_action (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    nativeGradedAction z hz (sexticX point i) = sexticX point i * q (C (char z i.castSucc)) := by
  change q (polynomialAction z (X i.castSucc)) = _
  rw [action_X, map_mul, mul_comm]
  rfl

private theorem denominator_recovery (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    sexticX point i = nativeGradedAction z hz (sexticX point i) * q (C (baseScale z i)) := by
  rw [denominator_action, mul_assoc, ← map_mul, ← map_mul, baseScale,
    mul_inv_cancel₀ (char_ne_zero z hz _), map_one, map_one, mul_one]

private theorem native_preimage_basic (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    (nativeAction z hz).hom ⁻¹ᵁ Proj.basicOpen G (sexticX point i) =
      Proj.basicOpen G (sexticX point i) :=
  le_antisymm (Proj.basicOpen_mono G _ _ ⟨_, denominator_action z hz i⟩)
    (Proj.basicOpen_mono G _ _ ⟨_, denominator_recovery z hz i⟩)

private theorem native_preimage_fixed (i : Fin 4) :
    nativeToIncidence.hom ⁻¹ᵁ fixedOpen i = Proj.basicOpen G (sexticX point i) := by
  unfold fixedOpen
  rw [← Scheme.Hom.comp_preimage, nativeToIncidence_snd]
  change Proj.basicOpen G (Ideal.Quotient.mk (sexticIdeal point) (MvPolynomial.map cubicEval (X i.castSucc))) = _
  rw [MvPolynomial.map_X]
  rfl

theorem fixedOpen_preimage (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    (threefoldAction z hz).hom ⁻¹ᵁ fixedOpen i = fixedOpen i := by
  change nativeToIncidence.inv ⁻¹ᵁ ((nativeAction z hz).hom ⁻¹ᵁ
    (nativeToIncidence.hom ⁻¹ᵁ fixedOpen i)) = _
  have he : (nativeAction z hz).hom ⁻¹ᵁ (nativeToIncidence.hom ⁻¹ᵁ fixedOpen i) =
      nativeToIncidence.hom ⁻¹ᵁ fixedOpen i := by
    rw [native_preimage_fixed, native_preimage_basic]
  rw [he, ← Scheme.Hom.comp_preimage nativeToIncidence.inv nativeToIncidence.hom (fixedOpen i),
    Iso.inv_hom_id, Scheme.Hom.id_preimage]

private abbrev nativeChartAction (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :=
  (awayMap G (coefficient_mem _) (denominator_recovery z hz i)).comp
    (Away.map (nativeGradedAction z hz) (sexticX point i))

private theorem nativeChartAction_toT (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    (nativeToT i).comp (nativeChartAction z hz i) = (chartAction z hz i).toRingHom.comp (nativeToT i) := by
  apply RingHom.ext
  intro x
  obtain ⟨n,p,hp,rfl⟩ := sexticFraction_surjective point i x
  let b := baseScale z i
  let v := C (b^n) * polynomialAction z p
  have hv : v.IsWeightedHomogeneous geometricWeight n := by
    simpa only [zero_add] using
      (isWeightedHomogeneous_C geometricWeight (b^n)).mul (polynomialAction_weighted z hp)
  have hx : nativeChartAction z hz i (sexticFraction point i n p hp) = sexticFraction point i n v hv := by
    apply HomogeneousLocalization.val_injective
    simp only [nativeChartAction, RingHom.comp_apply, sexticFraction, Away.map_mk, awayMap_mk, Away.val_mk]
    have he : (nativeGradedAction z hz (q p)) * q (C (baseScale z i)) ^ n = q v := by
      change q (polynomialAction z p) * q (C b) ^ n = q v
      simp only [v, map_mul, map_pow, mul_comm]
    rw [he]
  change nativeToT i (nativeChartAction z hz i _) = chartAction z hz i (nativeToT i _)
  rw [hx, nativeToT_fraction, nativeToT_fraction, chartAction_mk, chartPolynomialAction_homogeneous z hz i hp]
  simp only [v, b, map_mul, dehomogenize, aeval_C, MvPolynomial.algebraMap_eq]

/-- Restrict a graded morphism to the same weight-one chart when its
denominator admits a homogeneous degree-zero inverse factor. -/
private theorem gradedAway_equivariant {A σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (a : A) (ha : a ∈ 𝒜 1) (b : A) (hb : b ∈ 𝒜 0) (hab : a = f a * b) :
    Proj.awayι 𝒜 a ha (by decide) ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom ((awayMap 𝒜 hb hab).comp (Away.map f a))) ≫
        Proj.awayι 𝒜 a ha (by decide) := by
  let m := awayMap 𝒜 hb hab
  have he := Proj.SpecMap_awayMap_awayι 𝒜 (f.map_mem ha) (by decide) hb hab
  calc
    _ = (Spec.map (CommRingCat.ofHom m) ≫ Proj.awayι 𝒜 (f a) (f.map_mem ha) (by decide)) ≫
        Proj.map f hf := congrArg (fun g => g ≫ Proj.map f hf) he.symm
    _ = Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom (Away.map f a)) ≫
        Proj.awayι 𝒜 a ha (by decide) := by
      rw [Category.assoc, Proj.awayι_comp_map]
    _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl

set_option maxHeartbeats 800000 in
private theorem nativeAway_equivariant (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    Proj.awayι G (sexticX point i) (sexticX_mem point i) (by decide) ≫ (nativeAction z hz).hom =
      Spec.map (CommRingCat.ofHom (nativeChartAction z hz i)) ≫
        Proj.awayι G (sexticX point i) (sexticX_mem point i) (by decide) :=
  gradedAway_equivariant G (nativeGradedAction z hz)
    (cyclic_irrelevant_le_map _ (nativeGradedAction_cube z hz)) _
    (sexticX_mem point i) _ (coefficient_mem _) (denominator_recovery z hz i)

theorem chartInclusion_equivariant (z : ℂ) (hz : z^3 = 1) (i : Fin 4) :
    chartInclusion i ≫ (threefoldAction z hz).hom =
      Spec.map (CommRingCat.ofHom (chartAction z hz i).toRingHom) ≫ chartInclusion i := by
  rw [← nativeChartInclusion_toIncidence]
  simp only [threefoldAction, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  suffices h : nativeChartInclusion i ≫ (nativeAction z hz).hom =
      Spec.map (CommRingCat.ofHom (chartAction z hz i).toRingHom) ≫ nativeChartInclusion i by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ nativeToIncidence.hom) h
  unfold nativeChartInclusion
  rw [Category.assoc, nativeAway_equivariant, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((nativeToT i).comp (nativeChartAction z hz i))) ≫ _ =
    Spec.map (CommRingCat.ofHom ((chartAction z hz i).toRingHom.comp (nativeToT i))) ≫ _
  rw [nativeChartAction_toT]

end CycleQ2LiteralThreefoldOrbitAction
end

#print axioms CycleQ2LiteralThreefoldOrbitAction.chartInclusion_equivariant
