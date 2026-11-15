import Proposal.GeometricSeedSectionSheafSections

/-!
# The prescribed ideal twist in the actual projective section rings

The kernel source has its transition relation as an equality of genuine
sheaf morphisms.  This file reads that equality in the original structure
sheaf on every common subopen.  Multiplication is transported through the
actual open-immersion section map and its top-section isomorphism; it is
not replaced by an unrelated scalar action on a chart model.

The resulting source-coordinate equation is independent of the curve
parameter and retains the negative fourth-power transition of I_E(-4).
Source-only draft: no Lean elaboration or kernel replay has been run.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafTwist

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections

section OpenSections

variable {X : Scheme.{0}}

/-- The actual top-section identification commutes with restriction to
any subopen, followed by the original open immersion. -/
theorem topIso_restrict (U V : X.Opens) (hV : V ≤ U) :
    U.topIso.hom ≫ X.presheaf.map (homOfLE hV).op ≫ U.ι.app V =
      U.toScheme.presheaf.map
        (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op := by
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_app,
    Scheme.Opens.toScheme_presheaf_map, ← X.presheaf.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

theorem topIso_inv_restrict (U V : X.Opens) (hV : V ≤ U)
    (a : Γ(X, U)) :
    U.toScheme.presheaf.map
        (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op (U.topIso.inv a) =
      U.ι.app V (X.presheaf.map (homOfLE hV).op a) := by
  have h := ConcreteCategory.congr_hom (topIso_restrict U V hV) (U.topIso.inv a)
  change U.ι.app V
      (X.presheaf.map (homOfLE hV).op (U.topIso.hom (U.topIso.inv a))) =
    U.toScheme.presheaf.map
      (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op (U.topIso.inv a) at h
  have hc : U.topIso.hom (U.topIso.inv a) = a :=
    ConcreteCategory.congr_hom U.topIso.inv_hom_id a
  rw [hc] at h
  exact h.symm

end OpenSections

/-- The actual pushed-forward multiplication by a section on a patch. -/
def patchScalar (U : Surface.Opens) (a : Γ(Surface, U)) :
    patchStructure U ⟶ patchStructure U :=
  (Scheme.Modules.pushforward U.ι).map
    (structureScalar U.toScheme (U.topIso.inv a))

/-- In the original projective section ring this is multiplication by
the restriction of the same original section. -/
theorem patchSectionsEquiv_scalar (U V : Surface.Opens) (hV : V ≤ U)
    (a : Γ(Surface, U)) (y : Γ(patchStructure U, V)) :
    patchSectionsEquiv U V hV ((patchScalar U a).app V y) =
      Surface.presheaf.map (homOfLE hV).op a * patchSectionsEquiv U V hV y := by
  rw [patchScalar, Scheme.Modules.pushforward_map_app, structureScalar_app,
    topIso_inv_restrict U V hV a, map_mul]
  change patchSectionsEquiv U V hV
      ((patchSectionsEquiv U V hV).symm
        (Surface.presheaf.map (homOfLE hV).op a)) * _ = _
  rw [RingEquiv.apply_symm_apply]

/-- The pair-overlap twist uses the fourth power of the actual coordinate
ratio after restriction to any common subopen. -/
theorem pairTwist_coordinate (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j)
    (y : Γ(patchStructure (PairPatch i j), V)) :
    patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)
        ((pairTwist i j).app V y) =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 *
        patchSectionsEquiv (PairPatch i j) V (le_inf hi hj) y := by
  change patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)
      ((patchScalar (PairPatch i j)
        ((transitionUnit i j (PairPatch i j) inf_le_left inf_le_right :
          Γ(Surface, PairPatch i j)) ^ 4)).app V y) = _
  rw [patchSectionsEquiv_scalar, map_pow]
  have hu := congrArg (fun u : Γ(Surface, V)ˣ => (u : Γ(Surface, V)))
    (transitionUnit_restrict i j (PairPatch i j) V
      (le_inf hi hj) inf_le_left inf_le_right)
  change Surface.presheaf.map (homOfLE (le_inf hi hj)).op
      (transitionUnit i j (PairPatch i j) inf_le_left inf_le_right :
        Γ(Surface, PairPatch i j)) =
    (transitionUnit i j V hi hj : Γ(Surface, V)) at hu
  rw [hu]

/-- Every section of the independently constructed global source has the
original negative-fourth-power coordinate transition. -/
theorem sourceCoordinate_transition (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (s : Γ(twistedIdeal, V)) :
    sourceCoordinate i V hi s =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 *
        sourceCoordinate j V hj s := by
  have h := congrArg
    (fun f : twistedIdeal ⟶ patchStructure (PairPatch i j) => f.app V s)
    (chartProjection_compatibility i j)
  have hc := congrArg (patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)) h
  change patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)
      ((patchStructureRestriction (show PairPatch i j ≤ Patch i from inf_le_left)).app V
        ((idealPatchInclusion i).app V ((chartProjection i).app V s))) =
    patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)
      ((pairTwist i j).app V
        ((patchStructureRestriction (show PairPatch i j ≤ Patch j from inf_le_right)).app V
          ((idealPatchInclusion j).app V ((chartProjection j).app V s)))) at hc
  rw [patchSectionsEquiv_patchRestriction, pairTwist_coordinate,
    patchSectionsEquiv_patchRestriction] at hc
  exact hc

end CycleQ2SeedSectionSheafTwist

end

#print axioms CycleQ2SeedSectionSheafTwist.patchSectionsEquiv_scalar
#print axioms CycleQ2SeedSectionSheafTwist.pairTwist_coordinate
#print axioms CycleQ2SeedSectionSheafTwist.sourceCoordinate_transition
