import Proposal.GeometricIncidenceChartSmooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual smooth scheme opens of the original incidence surface family

The spectrum of each normalized-minor chart localization maps into the
original projective surface through its existing affine chart. This map
is an open immersion, and its composition with surfaceToBase is exactly
the spectrum map of the original coefficient algebra. The established
relative ring smoothness therefore gives smoothness and flatness of
this actual scheme morphism, and of the inclusion of its open image.

The preimage of that image in the affine chart is the literal principal
open of the normalized minor. The union goodOpen uses all weight-one
charts and all injective pairs of geometric columns; Zariski locality
proves this union smooth and flat over the original coefficient base. No
seed-fiber covering or proper base-neighborhood claim is made here.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceSmoothSchemeOpens

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2IncidenceUniversalChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceLocalizedChart CycleQ2IncidenceChartSmooth

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The existing affine coordinate chart, as a map into the actual surface. -/
def affineChartToSurface (y : ParameterIndex → S) (i : Fin 4) :
    Spec (CommRingCat.of (DehomogenizedRing y i)) ⟶ surface y :=
  (familyCoordinateAffineChart y i).inv ≫ (familyCoordinatePatch y i).ι

instance affineChartToSurface_isOpenImmersion (y : ParameterIndex → S) (i : Fin 4) :
    IsOpenImmersion (affineChartToSurface y i) := by
  dsimp only [affineChartToSurface]
  infer_instance

theorem affineChartToSurface_overBase (y : ParameterIndex → S) (i : Fin 4) :
    affineChartToSurface y i ≫ surfaceToBase y =
      Spec.map (CommRingCat.ofHom (algebraMap S (DehomogenizedRing y i))) := by
  simpa only [affineChartToSurface, Category.assoc] using
    familyCoordinateAffineChart_overBase y i

def minorToAffine (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    Spec (CommRingCat.of (LocalizedChartRing y i j k)) ⟶
      Spec (CommRingCat.of (DehomogenizedRing y i)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (DehomogenizedRing y i) (LocalizedChartRing y i j k)))

instance minorToAffine_isOpenImmersion (y : ParameterIndex → S)
    (i : Fin 4) (j k : Fin 5) : IsOpenImmersion (minorToAffine y i j k) :=
  IsOpenImmersion.of_isLocalization (normalizedMinor y i j k)

/-- The spectrum of the actual localized chart maps into the original surface. -/
def minorToSurface (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    Spec (CommRingCat.of (LocalizedChartRing y i j k)) ⟶ surface y :=
  minorToAffine y i j k ≫ affineChartToSurface y i

instance minorToSurface_isOpenImmersion (y : ParameterIndex → S)
    (i : Fin 4) (j k : Fin 5) : IsOpenImmersion (minorToSurface y i j k) := by
  dsimp only [minorToSurface]
  infer_instance

def minorOpen (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    (surface y).Opens :=
  (minorToSurface y i j k).opensRange

@[simp] theorem mem_minorOpen (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5)
    (x : surface y) :
    x ∈ minorOpen y i j k ↔
      ∃ a : Spec (CommRingCat.of (LocalizedChartRing y i j k)),
        minorToSurface y i j k a = x := Iff.rfl

theorem minorOpen_eq_image (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    minorOpen y i j k =
      affineChartToSurface y i ''ᵁ PrimeSpectrum.basicOpen (normalizedMinor y i j k) := by
  change (minorToAffine y i j k ≫ affineChartToSurface y i).opensRange = _
  have hminor : (minorToAffine y i j k).opensRange =
      PrimeSpectrum.basicOpen (normalizedMinor y i j k) :=
    Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of (DehomogenizedRing y i)) (normalizedMinor y i j k)
  rw [Scheme.Hom.opensRange_comp]
  rw [hminor]

/-- Its preimage is the native principal open of the original normalized minor. -/
theorem affineChartToSurface_preimage_minorOpen (y : ParameterIndex → S)
    (i : Fin 4) (j k : Fin 5) :
    affineChartToSurface y i ⁻¹ᵁ minorOpen y i j k =
      PrimeSpectrum.basicOpen (normalizedMinor y i j k) := by
  rw [minorOpen_eq_image, Scheme.Hom.preimage_image_eq]

theorem minorOpen_isAffineOpen (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    IsAffineOpen (minorOpen y i j k) :=
  isAffineOpen_opensRange (minorToSurface y i j k)

/-- The morphism to the base is exactly the canonical coefficient map. -/
theorem minorToSurface_overBase (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    minorToSurface y i j k ≫ surfaceToBase y =
      Spec.map (CommRingCat.ofHom (algebraMap S (LocalizedChartRing y i j k))) := by
  rw [minorToSurface, Category.assoc, affineChartToSurface_overBase,
    minorToAffine, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply S (DehomogenizedRing y i)
    (LocalizedChartRing y i j k) c).symm

theorem minorToSurface_smooth (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    AlgebraicGeometry.Smooth (minorToSurface y i (p 0) (p 1) ≫ surfaceToBase y) := by
  rw [minorToSurface_overBase]
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (normalizedMinor_smooth y i p hp)

theorem minorToSurface_flat (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    AlgebraicGeometry.Flat (minorToSurface y i (p 0) (p 1) ≫ surfaceToBase y) := by
  letI := minorToSurface_smooth y i p hp
  infer_instance

/-- Smoothness on the actual open subscheme, with its original base map. -/
theorem minorOpen_smooth (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    AlgebraicGeometry.Smooth ((minorOpen y i (p 0) (p 1)).ι ≫ surfaceToBase y) := by
  let f := minorToSurface y i (p 0) (p 1)
  have hr : Set.range f = Set.range f.opensRange.ι :=
    congrArg Opens.carrier f.opensRange.opensRange_ι.symm
  let e := IsOpenImmersion.isoOfRangeEq f f.opensRange.ι hr
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.Smooth) e.hom
    ((minorOpen y i (p 0) (p 1)).ι ≫ surfaceToBase y)).mp
  have he : e.hom ≫ f.opensRange.ι = f :=
    IsOpenImmersion.isoOfRangeEq_hom_fac f f.opensRange.ι hr
  change AlgebraicGeometry.Smooth (e.hom ≫ f.opensRange.ι ≫ surfaceToBase y)
  rw [← Category.assoc, he]
  exact minorToSurface_smooth y i p hp

theorem minorOpen_flat (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    AlgebraicGeometry.Flat ((minorOpen y i (p 0) (p 1)).ι ≫ surfaceToBase y) := by
  letI := minorOpen_smooth y i p hp
  infer_instance

abbrev MinorIndex := Fin 4 × (Fin 2 ↪ Fin 5)

/-- The explicit union of all these actual smooth principal chart opens. -/
def goodOpen (y : ParameterIndex → S) : (surface y).Opens :=
  ⨆ q : MinorIndex, minorOpen y q.1 (q.2 0) (q.2 1)

theorem minorOpen_le_goodOpen (y : ParameterIndex → S) (i : Fin 4)
    (p : Fin 2 ↪ Fin 5) :
    minorOpen y i (p 0) (p 1) ≤ goodOpen y :=
  le_iSup_of_le (i, p) le_rfl

theorem mem_goodOpen_iff (y : ParameterIndex → S) (x : surface y) :
    x ∈ goodOpen y ↔
      ∃ (i : Fin 4) (p : Fin 2 ↪ Fin 5), x ∈ minorOpen y i (p 0) (p 1) := by
  constructor
  · intro h
    obtain ⟨⟨i, p⟩, hp⟩ := Opens.mem_iSup.mp h
    exact ⟨i, p, hp⟩
  · rintro ⟨i, p, hp⟩
    exact Opens.mem_iSup.mpr ⟨(i, p), hp⟩

/-- The explicit union itself is smooth over the unchanged coefficient base. -/
theorem goodOpen_smooth (y : ParameterIndex → S) :
    AlgebraicGeometry.Smooth ((goodOpen y).ι ≫ surfaceToBase y) := by
  let V : MinorIndex → (goodOpen y).toScheme.Opens := fun q =>
    (goodOpen y).ι ⁻¹ᵁ minorOpen y q.1 (q.2 0) (q.2 1)
  have hV : (⨆ q : MinorIndex, V q) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x.1 ∈ goodOpen y := x.2
    obtain ⟨q, hq⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨q, hq⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.Smooth) V hV
  intro q
  let U := minorOpen y q.1 (q.2 0) (q.2 1)
  let g : (V q).toScheme ⟶ surface y := (V q).ι ≫ (goodOpen y).ι
  have hr : Set.range g ⊆ Set.range U.ι := by
    rintro x ⟨a, rfl⟩
    exact ⟨⟨g a, a.2⟩, rfl⟩
  let gLift := IsOpenImmersion.lift U.ι g hr
  have he : gLift ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  rw [← Category.assoc]
  change AlgebraicGeometry.Smooth (g ≫ surfaceToBase y)
  rw [← he, Category.assoc]
  exact IsZariskiLocalAtSource.comp
    (minorOpen_smooth y q.1 q.2 q.2.injective) gLift

theorem goodOpen_flat (y : ParameterIndex → S) :
    AlgebraicGeometry.Flat ((goodOpen y).ι ≫ surfaceToBase y) := by
  letI := goodOpen_smooth y
  infer_instance

end CycleQ2IncidenceSmoothSchemeOpens

end

#print axioms CycleQ2IncidenceSmoothSchemeOpens.minorToSurface_overBase
#print axioms CycleQ2IncidenceSmoothSchemeOpens.affineChartToSurface_preimage_minorOpen
#print axioms CycleQ2IncidenceSmoothSchemeOpens.minorToSurface_smooth
#print axioms CycleQ2IncidenceSmoothSchemeOpens.minorOpen_smooth
#print axioms CycleQ2IncidenceSmoothSchemeOpens.goodOpen_smooth
#print axioms CycleQ2IncidenceSmoothSchemeOpens.goodOpen_flat
