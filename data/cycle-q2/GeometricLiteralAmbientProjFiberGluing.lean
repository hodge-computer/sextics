import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Recognizing a graded projective specialization as a scheme fiber

The base change of a degree-zero localization can be checked on a chosen
family of positive-degree homogeneous elements. If those opens cover the
scheme fiber, the canonical map from the specialized Proj is an isomorphism.
The affine squares use the ring maps on the degree-zero localizations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientProjFiberGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open scoped AlgebraicGeometry

variable {A B σ τ : Type} [CommRing A] [CommRing B]
  [SetLike σ A] [SetLike τ B] [AddSubgroupClass σ A] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable {S T : Scheme} (b : T ⟶ S) (π : Proj 𝒜 ⟶ S) (ν : Proj ℬ ⟶ T)
variable (w : ν ≫ b = Proj.map f hf ≫ π)

/-- Canonical comparison with the scheme-theoretic base change. -/
def comparison : Proj ℬ ⟶ pullback b π := pullback.lift ν (Proj.map f hf) w

private abbrev fiberOpen (s : A) : (pullback b π).Opens :=
  pullback.snd b π ⁻¹ᵁ Proj.basicOpen 𝒜 s

theorem comparison_preimage (s : A) :
    comparison f hf b π ν w ⁻¹ᵁ fiberOpen b π s = Proj.basicOpen ℬ (f s) := by
  rw [fiberOpen, ← Scheme.Hom.comp_preimage, comparison, pullback.lift_snd,
    Proj.map_preimage_basicOpen]

variable {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d)

private abbrev awayA :=
  Proj.awayι 𝒜 s hs hd

private abbrev awayB :=
  Proj.awayι ℬ (f s) (f.2 hs) hd

/-- The affine Cartesian-square condition uses the actual map on
homogeneous fractions. -/
abbrev AwaySquare : Prop :=
  IsPullback (awayB f s hs hd ≫ ν)
    (Spec.map (CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s))))
    b (awayA s hs hd ≫ π)

private def chartPullbackIso :
    pullback b (awayA s hs hd ≫ π) ≅ (fiberOpen b π s).toScheme :=
  asIso (pullback.map b (awayA s hs hd ≫ π)
    b ((Proj.basicOpen 𝒜 s).ι ≫ π) (𝟙 T) (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv
    (𝟙 S) (by simp) (by simp [awayA, Proj.awayι])) ≪≫
    (pullbackLeftPullbackSndIso b π (Proj.basicOpen 𝒜 s).ι).symm ≪≫
    pullbackRestrictIsoRestrict (pullback.snd b π) (Proj.basicOpen 𝒜 s)

@[reassoc] private theorem chartPullbackIso_fst :
    (chartPullbackIso b π s hs hd).hom ≫ (fiberOpen b π s).ι ≫ pullback.fst b π =
      pullback.fst b (awayA s hs hd ≫ π) := by
  simp only [chartPullbackIso, fiberOpen, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackLeftPullbackSndIso_inv_fst,
    asIso_hom, pullback.lift_fst, Category.comp_id]

@[reassoc] private theorem chartPullbackIso_snd :
    (chartPullbackIso b π s hs hd).hom ≫ (fiberOpen b π s).ι ≫ pullback.snd b π =
      pullback.snd b (awayA s hs hd ≫ π) ≫ awayA s hs hd := by
  simp only [chartPullbackIso, fiberOpen, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
    asIso_hom, pullback.lift_snd_assoc, awayA, Proj.awayι]

variable (h : AwaySquare f b π ν s hs hd)

private def localIso :
    (comparison f hf b π ν w ⁻¹ᵁ fiberOpen b π s).toScheme ≅ (fiberOpen b π s).toScheme :=
  (Proj ℬ).isoOfEq (comparison_preimage f hf b π ν w s) ≪≫
    Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hd ≪≫ h.isoPullback ≪≫ chartPullbackIso b π s hs hd

private theorem comparison_restrict :
    (comparison f hf b π ν w ∣_ fiberOpen b π s) = (localIso f hf b π ν w s hs hd h).hom := by
  apply (cancel_mono (fiberOpen b π s).ι).mp
  rw [morphismRestrict_ι]
  apply pullback.hom_ext
  · simp only [Category.assoc, comparison, pullback.lift_fst, localIso, Iso.trans_hom,
      chartPullbackIso_fst, IsPullback.isoPullback_hom_fst, awayB, Proj.awayι,
      Iso.hom_inv_id_assoc, Scheme.isoOfEq_hom_ι_assoc]
  · simp only [Category.assoc, comparison, pullback.lift_snd, localIso, Iso.trans_hom,
      chartPullbackIso_snd, IsPullback.isoPullback_hom_snd_assoc]
    rw [← Proj.awayι_comp_map f hf hd s hs]
    simp only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc, Scheme.isoOfEq_hom_ι_assoc]

/-- Affine Cartesian squares on a cover of the fiber identify the native
specialized Proj with the entire scheme-theoretic fiber. -/
theorem comparison_isIso_of_away {ι : Type*} (s : ι → A) (d : ι → ℕ)
    (hs : ∀ i, s i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i)
    (hc : (⨆ i, pullback.snd b π ⁻¹ᵁ Proj.basicOpen 𝒜 (s i)) = ⊤)
    (h : ∀ i, AwaySquare f b π ν (s i) (hs i) (hd i)) :
    IsIso (comparison f hf b π ν w) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i => fiberOpen b π (s i)) hc
  intro i
  change IsIso (comparison f hf b π ν w ∣_ fiberOpen b π (s i))
  rw [comparison_restrict f hf b π ν w (s i) (hs i) (hd i) (h i)]
  infer_instance

include w in
theorem isPullback_of_away {ι : Type*} (s : ι → A) (d : ι → ℕ)
    (hs : ∀ i, s i ∈ 𝒜 (d i)) (hd : ∀ i, 0 < d i)
    (hc : (⨆ i, pullback.snd b π ⁻¹ᵁ Proj.basicOpen 𝒜 (s i)) = ⊤)
    (h : ∀ i, AwaySquare f b π ν (s i) (hs i) (hd i)) :
    IsPullback ν (Proj.map f hf) b π := by
  let := comparison_isIso_of_away f hf b π ν w s d hs hd hc h
  exact .of_iso_pullback ⟨w⟩ (asIso (comparison f hf b π ν w))
    (by simp [comparison]) (by simp [comparison])

/-- All standard affine Proj opens suffice. The local squares imply the global
commuting-square equation as well as its Cartesian property. -/
theorem isPullback_of_all_away
    (h : ∀ (n : ℕ) (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n),
      AwaySquare f b π ν a ha hn) :
    IsPullback ν (Proj.map f hf) b π := by
  have comm : ν ≫ b = Proj.map f hf ≫ π := by
    refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun j => ?_
    simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
    calc
      _ = (awayB f (j.2 : A) j.2.2 j.1.2 ≫ ν) ≫ b := (Category.assoc _ _ _).symm
      _ = _ := (h j.1 j.1.2 j.2 j.2.2).w
      _ = _ := (Proj.awayι_comp_map_assoc f hf j.1.2 (j.2 : A) j.2.2 π).symm
  let a (j : Σ n : PNat, 𝒜 n) : A := j.2
  apply isPullback_of_away f hf b π ν comm a (fun j => (j.1 : ℕ))
    (fun j => j.2.2) (fun j => j.1.2)
  · have hc := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
    change (⨆ j : Σ n : PNat, 𝒜 n,
      (Proj.awayι 𝒜 (a j) j.2.2 j.1.2).opensRange) = ⊤ at hc
    simp only [Proj.opensRange_awayι] at hc
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · exact fun j => h j.1 j.1.2 j.2 j.2.2

open scoped TensorProduct

private theorem affine_isPullback_of_tensorEquiv
    {R K U V : Type} [CommRing R] [CommRing K] [CommRing U] [CommRing V]
    [Algebra R K] [Algebra R U] [Algebra K V] (g : U →+* V)
    (e : K ⊗[R] U ≃ₐ[K] V) (he : ∀ u, e (1 ⊗ₜ[R] u) = g u) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap K V)))
      (Spec.map (CommRingCat.ofHom g)) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R U))) := by
  let E := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso R K U).symm
  have h₁ : E.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap K V)) := by
    change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (pullbackSpecIso R K U).inv) ≫ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.commutes))
  have h₂ : E.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g) := by
    change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (pullbackSpecIso R K U).inv) ≫ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext he))
  apply IsPullback.of_iso_pullback _ E h₁ h₂
  constructor
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]

variable {R K : Type} [CommRing R] [CommRing K]
variable (α : R →+* K) (cA : R →+* 𝒜 0) (cB : K →+* ℬ 0)

/-- Tensor-product comparison on a degree-zero localization, with the
algebras induced by the original coefficients in degree zero. -/
def TensorChart (a : A) : Prop :=
  letI := α.toAlgebra
  letI := ((fromZeroRingHom 𝒜 (Submonoid.powers a)).comp cA).toAlgebra
  letI := ((fromZeroRingHom ℬ (Submonoid.powers (f a))).comp cB).toAlgebra
  ∃ e : K ⊗[R] Away 𝒜 a ≃ₐ[K] Away ℬ (f a),
    ∀ z, e (1 ⊗ₜ[R] z) = Away.map f a z

/-- Degree-zero tensor comparisons on the standard positive homogeneous
charts make the specialized Proj a scheme-theoretic base change. -/
theorem projective_isPullback_of_tensorCharts
    (h : ∀ (n : ℕ) (_ : 0 < n) (a : A), a ∈ 𝒜 n → TensorChart f α cA cB a) :
    IsPullback (Proj.map f hf) (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom cB))
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom cA)) (Spec.map (CommRingCat.ofHom α)) := by
  apply IsPullback.flip
  apply isPullback_of_all_away
  intro n hn a ha
  letI := α.toAlgebra
  letI := ((fromZeroRingHom 𝒜 (Submonoid.powers a)).comp cA).toAlgebra
  letI := ((fromZeroRingHom ℬ (Submonoid.powers (f a))).comp cB).toAlgebra
  obtain ⟨e, he⟩ := h n hn a ha
  unfold AwaySquare awayA awayB
  rw [Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact affine_isPullback_of_tensorEquiv (R := R) (K := K) (Away.map f a) e he

end CycleQ2LiteralAmbientProjFiberGluing
end

#print axioms CycleQ2LiteralAmbientProjFiberGluing.comparison_isIso_of_away
#print axioms CycleQ2LiteralAmbientProjFiberGluing.projective_isPullback_of_tensorCharts
