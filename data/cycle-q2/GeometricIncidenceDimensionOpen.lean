import Proposal.GeometricIncidenceChartMinorCover

/-!
# An actual relative-dimension-two open containing the original good open

The spectra of the genuine four-variable Jacobian patches map by open
immersions into the original surface. Their union is smooth of relative
dimension two over the unchanged coefficient base. The comparison of
Jacobian ideals proves that every point of the previous normalized
cone-minor open belongs to this dimension-two open.

All assertions hold for an arbitrary coefficient algebra and incidence
point. No covering premise or fiber-smoothness premise is assumed.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceDimensionOpen

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2IncidenceUniversalChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceSmoothSchemeOpens CycleQ2IncidenceChartDimension
  CycleQ2IncidenceChartMinorCover

variable {S : Type} [CommRing S] [Algebra ℂ S]

def jacobianOpen (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 ↪ Option (Fin 3)) : (surface y).Opens :=
  (patchToSurface y i q q.injective).opensRange

theorem jacobianOpen_eq_image (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 ↪ Option (Fin 3)) :
    jacobianOpen y i q =
      affineChartToSurface y i ''ᵁ PrimeSpectrum.basicOpen (chartMinor y i q) := by
  change (patchToAffine y i q q.injective ≫ affineChartToSurface y i).opensRange = _
  rw [Scheme.Hom.opensRange_comp, patchToAffine,
    Scheme.Hom.opensRange_localizationAway, prePresentation_jacobian]

theorem affineChartToSurface_preimage_jacobianOpen (y : ParameterIndex → S)
    (i : Fin 4) (q : Fin 2 ↪ Option (Fin 3)) :
    affineChartToSurface y i ⁻¹ᵁ jacobianOpen y i q =
      PrimeSpectrum.basicOpen (chartMinor y i q) := by
  rw [jacobianOpen_eq_image, Scheme.Hom.preimage_image_eq]

theorem jacobianOpen_smoothOfRelativeDimension (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 ↪ Option (Fin 3)) :
    AlgebraicGeometry.SmoothOfRelativeDimension 2
      ((jacobianOpen y i q).ι ≫ surfaceToBase y) := by
  let f := patchToSurface y i q q.injective
  have hr : Set.range f = Set.range f.opensRange.ι :=
    congrArg Opens.carrier f.opensRange.opensRange_ι.symm
  let e := IsOpenImmersion.isoOfRangeEq f f.opensRange.ι hr
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension 2) e.hom
    ((jacobianOpen y i q).ι ≫ surfaceToBase y)).mp
  have he : e.hom ≫ f.opensRange.ι = f :=
    IsOpenImmersion.isoOfRangeEq_hom_fac f f.opensRange.ι hr
  change AlgebraicGeometry.SmoothOfRelativeDimension 2
    (e.hom ≫ f.opensRange.ι ≫ surfaceToBase y)
  rw [← Category.assoc, he]
  exact patchToSurface_smoothOfRelativeDimension y i q q.injective

abbrev ChartMinorIndex := Fin 4 × (Fin 2 ↪ Option (Fin 3))

def dimensionOpen (y : ParameterIndex → S) : (surface y).Opens :=
  ⨆ q : ChartMinorIndex, jacobianOpen y q.1 q.2

theorem jacobianOpen_le_dimensionOpen (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 ↪ Option (Fin 3)) : jacobianOpen y i q ≤ dimensionOpen y :=
  le_iSup_of_le (i, q) le_rfl

/-- Relative dimension two holds on the actual union, with the original
surface structure map. -/
theorem dimensionOpen_smoothOfRelativeDimension (y : ParameterIndex → S) :
    AlgebraicGeometry.SmoothOfRelativeDimension 2
      ((dimensionOpen y).ι ≫ surfaceToBase y) := by
  let V : ChartMinorIndex → (dimensionOpen y).toScheme.Opens := fun q =>
    (dimensionOpen y).ι ⁻¹ᵁ jacobianOpen y q.1 q.2
  have hV : (⨆ q : ChartMinorIndex, V q) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x.1 ∈ dimensionOpen y := x.2
    obtain ⟨q, hq⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨q, hq⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension 2) V hV
  intro q
  let U := jacobianOpen y q.1 q.2
  let g : (V q).toScheme ⟶ surface y := (V q).ι ≫ (dimensionOpen y).ι
  have hr : Set.range g ⊆ Set.range U.ι := by
    rintro x ⟨a, rfl⟩
    exact ⟨⟨g a, a.2⟩, rfl⟩
  let gLift := IsOpenImmersion.lift U.ι g hr
  have he : gLift ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  rw [← Category.assoc]
  change AlgebraicGeometry.SmoothOfRelativeDimension 2 (g ≫ surfaceToBase y)
  rw [← he, Category.assoc]
  exact IsZariskiLocalAtSource.comp
    (jacobianOpen_smoothOfRelativeDimension y q.1 q.2) gLift

/-- The old normalized-cone-minor open is contained in the actual
four-variable Jacobian open. This comparison is uniform in the base. -/
theorem goodOpen_le_dimensionOpen (y : ParameterIndex → S) :
    goodOpen y ≤ dimensionOpen y := by
  intro x hx
  obtain ⟨i, p, hp⟩ := (mem_goodOpen_iff y x).mp hx
  obtain ⟨b, hb⟩ := (mem_minorOpen y i (p 0) (p 1) x).mp hp
  let a := minorToAffine y i (p 0) (p 1) b
  have ha : a ∈ affineChartToSurface y i ⁻¹ᵁ minorOpen y i (p 0) (p 1) := by
    exact ⟨b, rfl⟩
  rw [affineChartToSurface_preimage_minorOpen] at ha
  change normalizedMinor y i (p 0) (p 1) ∉ a.asIdeal at ha
  obtain ⟨q, hq, hminor⟩ := exists_chartMinor_not_mem y i a.asIdeal (p 0) (p 1) ha
  let q' : Fin 2 ↪ Option (Fin 3) := ⟨q, hq⟩
  have haq : a ∈ PrimeSpectrum.basicOpen (chartMinor y i q') := hminor
  rw [← affineChartToSurface_preimage_jacobianOpen] at haq
  apply jacobianOpen_le_dimensionOpen y i q'
  rw [← hb]
  exact haq

end CycleQ2IncidenceDimensionOpen

end

#print axioms CycleQ2IncidenceDimensionOpen.jacobianOpen_smoothOfRelativeDimension
#print axioms CycleQ2IncidenceDimensionOpen.dimensionOpen_smoothOfRelativeDimension
#print axioms CycleQ2IncidenceDimensionOpen.goodOpen_le_dimensionOpen
