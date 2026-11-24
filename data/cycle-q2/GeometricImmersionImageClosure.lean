import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Open restrictions of the scheme-theoretic closure

The image of a quasi-compact morphism commutes with open base change. Thus
an immersion into a proper ambient scheme admits a proper closure, and an
open on which the given family is already closed recovers that family as a
scheme.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2ImmersionImageClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y X' Y' S : Scheme.{u}}

/-- Compactify a quasi-compact immersion into a scheme proper over the base
by its scheme-theoretic image. -/
theorem proper_image_closure (f : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion f] [QuasiCompact f] [IsProper p] :
    IsOpenImmersion f.toImage ∧ IsDominant f.toImage ∧
      IsProper (f.imageι ≫ p) ∧ f.toImage ≫ f.imageι = f :=
  ⟨inferInstance, inferInstance, inferInstance, f.toImage_imageι⟩

variable {f : X ⟶ Y} {g : X' ⟶ Y'} {i : X' ⟶ X} {j : Y' ⟶ Y}
  [QuasiCompact f] [IsOpenImmersion j] (H : IsPullback g i j f)

include H

/-- The defining ideal of the scheme-theoretic image commutes with open base change. -/
theorem imageKer_baseChange : g.ker = f.ker.comap j := by
  ext W : 2
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f g i j H W,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- The canonical map on scheme-theoretic images over the open immersion. -/
def imageBaseChangeMap : g.image ⟶ f.image :=
  g.ker.subschemeMap f.ker j
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (imageKer_baseChange H).ge)

@[reassoc (attr := simp)]
theorem imageBaseChangeMap_imageι : imageBaseChangeMap H ≫ f.imageι = g.imageι ≫ j :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Open base change recovers the scheme-theoretic image, with its closed embedding. -/
theorem imageBaseChange_isPullback :
    IsPullback g.imageι (imageBaseChangeMap H) j f.imageι := by
  apply isPullback_of_isClosedImmersion
  · exact (imageBaseChangeMap_imageι H).symm
  · simpa only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι] using
      (imageKer_baseChange H).symm

/-- If the given family is closed on the open part, that same family is
the restriction of the closure. -/
theorem imageBaseChange_of_closed [IsClosedImmersion g] :
    IsPullback g (i ≫ f.toImage) j f.imageι := by
  apply isPullback_of_isClosedImmersion
  · simpa using H.w
  · simpa only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι] using
      (imageKer_baseChange H).symm

omit H in
/-- The image of a restriction is canonically the corresponding open of the image. -/
def imageRestrictIso (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).image ≅ (f.imageι ⁻¹ᵁ U).toScheme :=
  (imageBaseChange_isPullback (isPullback_morphismRestrict f U)).isoIsPullback _ _
    (isPullback_morphismRestrict f.imageι U)

omit H in
/-- A closed family inside an open ambient scheme is recovered exactly by
pulling its closure back along the open immersion. -/
theorem closed_in_open_pullback (g : X ⟶ Y') (j : Y' ⟶ Y) [IsClosedImmersion g]
    [IsOpenImmersion j] [QuasiCompact (g ≫ j)] :
    IsPullback g (g ≫ j).toImage j (g ≫ j).imageι := by
  have h : IsPullback g (𝟙 X) j (g ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using imageBaseChange_of_closed h

#print axioms proper_image_closure
#print axioms imageBaseChange_isPullback
#print axioms imageBaseChange_of_closed
#print axioms closed_in_open_pullback

end CycleQ2ImmersionImageClosure
