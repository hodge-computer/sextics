import Proposal.GeometricSeedFermatCone

/-!
# Smoothness of the actual punctured zero-cubic seed cone

The punctured cone is the open subscheme of the literal seed quotient
where at least one of its five coordinates is invertible. The canonical
basic-open/localization isomorphisms identify its coordinate opens with
the previously constructed smooth affine patches. Smoothness is local
on the source, so these five proved patch statements give smoothness of
the actual punctured-cone structural morphism.

This construction does not assert smoothness of a weighted projective
quotient or of a family over the cubic parameter space.

Prepared for fqlx with OpenAI ChatGPT assistance, following
the geometric seed in Ben Diamond's surface-section argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedPuncturedCone

open CategoryTheory TopologicalSpace AlgebraicGeometry
open CycleQ2SeedFermatCone

/-- The affine scheme of the literal zero-cubic seed quotient. -/
def Cone (r : ℂ) : Scheme := Spec (CommRingCat.of (ConeRing r))

/-- Its structural morphism over the original coefficient field. -/
def coneToComplex (r : ℂ) : Cone r ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (ConeRing r)))

/-- The actual basic open of one of the five original coordinates. -/
def coordinateOpen (r : ℂ) (j : Fin 5) : (Cone r).Opens :=
  PrimeSpectrum.basicOpen (coordinateClass r j)

/-- The localization map into the actual affine cone. -/
def coordinatePatchToCone (r : ℂ) (j : Fin 5) :
    coordinatePatch r j ⟶ Cone r :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ConeRing r) (CoordinateRing r j)))

theorem coordinatePatchToCone_comp_toComplex (r : ℂ) (j : Fin 5) :
    coordinatePatchToCone r j ≫ coneToComplex r = toComplex r j := by
  unfold coordinatePatchToCone coneToComplex toComplex
  rw [← Spec.map_comp]
  congr 1

/-- The canonical geometric identification with the proved affine patch. -/
def coordinateOpenIsoPatch (r : ℂ) (j : Fin 5) :
    (coordinateOpen r j).toScheme ≅ coordinatePatch r j :=
  basicOpenIsoSpecAway (R := CommRingCat.of (ConeRing r)) (coordinateClass r j)

theorem coordinateOpenIsoPatch_hom_toCone (r : ℂ) (j : Fin 5) :
    (coordinateOpenIsoPatch r j).hom ≫ coordinatePatchToCone r j =
      (coordinateOpen r j).ι :=
  basicOpenIsoSpecAway_hom_SpecMap
    (R := CommRingCat.of (ConeRing r)) (coordinateClass r j)

theorem coordinateOpen_toComplex_eq (r : ℂ) (j : Fin 5) :
    (coordinateOpen r j).ι ≫ coneToComplex r =
      (coordinateOpenIsoPatch r j).hom ≫ toComplex r j := by
  rw [← coordinateOpenIsoPatch_hom_toCone r j, Category.assoc,
    coordinatePatchToCone_comp_toComplex]

/-- Smoothness of the actual coordinate open, with no smoothness premise. -/
theorem coordinateOpen_smooth (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    Smooth ((coordinateOpen r j).ι ≫ coneToComplex r) := by
  rw [coordinateOpen_toComplex_eq]
  exact IsZariskiLocalAtSource.comp (P := @Smooth)
    (coordinatePatch_smooth r hr j) (coordinateOpenIsoPatch r j).hom

/-- Remove the common zero locus of the five original coordinates. -/
def puncturedOpen (r : ℂ) : (Cone r).Opens :=
  ⨆ j : Fin 5, coordinateOpen r j

/-- The actual open subscheme, rather than a new abstract smooth scheme. -/
def puncturedCone (r : ℂ) : Scheme := (puncturedOpen r).toScheme

def puncturedToComplex (r : ℂ) :
    puncturedCone r ⟶ Spec (CommRingCat.of ℂ) :=
  (puncturedOpen r).ι ≫ coneToComplex r

/-- Pull the coordinate opens back to the actual punctured cone. -/
def coordinateOpenInPunctured (r : ℂ) (j : Fin 5) : (puncturedCone r).Opens :=
  (puncturedOpen r).ι ⁻¹ᵁ coordinateOpen r j

theorem iSup_coordinateOpenInPunctured (r : ℂ) :
    (⨆ j : Fin 5, coordinateOpenInPunctured r j) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x.1 ∈ (⨆ j : Fin 5, coordinateOpen r j) := x.2
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  refine Opens.mem_iSup.mpr ⟨j, ?_⟩
  change x.1 ∈ coordinateOpen r j
  exact hj

/-- The five previously proved local smoothness statements establish
smoothness of the structural morphism of the entire punctured cone. -/
theorem puncturedCone_smooth (r : ℂ) (hr : r ^ 3 = 2) :
    Smooth (puncturedToComplex r) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun j : Fin 5 => coordinateOpenInPunctured r j)
    (iSup_coordinateOpenInPunctured r)
  intro j
  haveI : IsOpenImmersion
      ((puncturedOpen r).ι ∣_ coordinateOpen r j) := by
    dsimp [morphismRestrict]
    infer_instance
  have h := IsZariskiLocalAtSource.comp (P := @Smooth)
    (coordinateOpen_smooth r hr j)
    ((puncturedOpen r).ι ∣_ coordinateOpen r j)
  simpa only [coordinateOpenInPunctured, puncturedToComplex,
    morphismRestrict_ι_assoc] using h

#print axioms coordinateOpen_smooth
#print axioms iSup_coordinateOpenInPunctured
#print axioms puncturedCone_smooth

end CycleQ2SeedPuncturedCone

end
