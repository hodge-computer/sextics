import Proposal.GeometricLiteralThreefoldOverlapAtlas

/-! The weighted transition map localizes the destination chart at Xi/Xj.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldOverlapLocalization

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralAmbientChartOverlap
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldOverlapAtlas

/-- An affine open immersion onto the principal open D(x) has the original
algebra map as the localization map at x. -/
private theorem localization_of_range {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (h : (Spec.map (CommRingCat.ofHom f)).opensRange = PrimeSpectrum.basicOpen x) :
    letI := f.toAlgebra
    IsLocalization.Away x S := by
  let L := Localization.Away x
  let g := Spec.map (CommRingCat.ofHom (algebraMap R L))
  let : IsOpenImmersion g := IsOpenImmersion.of_isLocalization x
  have hr : Set.range (Spec.map (CommRingCat.ofHom f)) = Set.range g := by
    exact (congrArg (fun U : (Spec (CommRingCat.of R)).Opens =>
      (U : Set (Spec (CommRingCat.of R)))) h).trans
      (PrimeSpectrum.localization_away_comap_range L x).symm
  let e := IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom f)) g hr
  let E : CommRingCat.of L ≅ CommRingCat.of S :=
    { hom := Spec.preimage e.hom
      inv := Spec.preimage e.inv
      hom_inv_id := by rw [← Spec.preimage_comp, e.inv_hom_id, Spec.preimage_id]
      inv_hom_id := by rw [← Spec.preimage_comp, e.hom_inv_id, Spec.preimage_id] }
  have he : e.hom ≫ g = Spec.map (CommRingCat.ofHom f) :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have H := congrArg Spec.preimage he
  simp only [Spec.preimage_comp, g, Spec.preimage_map] at H
  let := f.toAlgebra
  let eA : L ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := E.commRingCatIsoToRingEquiv)
    (fun z => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom H) z)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x) eA

private theorem factor_open {X Y Z : Scheme} (f : X ⟶ Y) (h : Y ⟶ Z) [IsOpenImmersion h]
    (U V : Z.Opens) (e : X ≅ (U ⊓ V).toScheme)
    (he : f ≫ h = e.hom ≫ (U ⊓ V).ι) : IsOpenImmersion f := by
  have : IsOpenImmersion (f ≫ h) := he.symm ▸ inferInstance
  exact IsOpenImmersion.of_comp f h

private theorem factor_range {X Y Z : Scheme} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion h]
    (U V : Z.Opens) (e : X ≅ (U ⊓ V).toScheme)
    (he : f ≫ h = e.hom ≫ (U ⊓ V).ι) (hv : h.opensRange = V) :
    f.opensRange = h ⁻¹ᵁ U := by
  have H : (f ≫ h).opensRange = U ⊓ V := by
    simp only [he, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  rw [← h.preimage_image_eq f.opensRange, ← Scheme.Hom.opensRange_comp, H, ← hv]
  change (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ h.opensRange) = _
  rw [h.preimage_opensRange, inf_top_eq]

/-- In coordinates on chart j, the old source axis is Xi/Xj. -/
abbrev sourceAxis (i : Fin 4) (k : Fin 3) : T (i.succAbove k) :=
  Ideal.Quotient.mk (fixedIdeal (i.succAbove k)) (linearCoordinate (i.succAbove k) i)

/-- The algebra structure in this assertion is induced by the weighted
substitution from the destination chart. -/
theorem fixedTargetMap_isLocalization (i : Fin 4) (k : Fin 3) :
    letI := (fixedTargetMap i k).toRingHom.toAlgebra
    IsLocalization.Away (sourceAxis i k) (FixedOverlap i k) := by
  let j := i.succAbove k
  let f := Spec.map (CommRingCat.ofHom (fixedTargetMap i k).toRingHom)
  have he : f ≫ chartInclusion j = (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen j).ι :=
    (overlapIso_hom_ι_target i k).symm
  let : IsOpenImmersion f :=
    factor_open f (chartInclusion j) (fixedOpen i) (fixedOpen j) _ he
  apply localization_of_range
  have hr : (chartInclusion j).opensRange = fixedOpen j := by
    change ((fixedChart j).hom ≫ (fixedOpen j).ι).opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  exact (factor_range f (chartInclusion j) (fixedOpen i) (fixedOpen j) _ he hr).trans
    (chartInclusion_preimage_fixedOpen j i)

end CycleQ2LiteralThreefoldOverlapLocalization

#print axioms CycleQ2LiteralThreefoldOverlapLocalization.fixedTargetMap_isLocalization
