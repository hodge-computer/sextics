import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass

/-!
# Lifting sections on intersections of principal opens

The two-open intersections in the principal cover of an affine scheme are
principal. Their affine charts and the structure sheaf frame give vanishing
of ambient first cohomology, hence sectionwise surjectivity in the first
injective presentation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffinePairLifts

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open CycleQ2GeometricAffineCohomology CycleQ2GeometricProjectiveHOne
open CycleQ2CechTwoToDerived

local instance affineHasExt (A : Type) [CommRing A] : HasExt.{1} (AbSheaf A) :=
  HasExt.standard _

theorem pair_hOne (A : Type) [CommRing A] (f g : A) :
    Subsingleton ((additiveStructureSheaf A).H' 1
      (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g)) := by
  rw [← PrimeSpectrum.basicOpen_mul]
  exact affineFrameHOne_subsingleton
    (basicOpenIsoSpecAway (R := CommRingCat.of A) (f * g))
    (structureAdditiveSheaf (Spec (CommRingCat.of A))) (Iso.refl _)

theorem pair_lift (A : Type) [CommRing A] (f g : A) :
    Function.Surjective (app (presentation (additiveStructureSheaf A)).g
      (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g)) :=
  sections_surjective_of_H_one_subsingleton
    (presentation_shortExact (additiveStructureSheaf A)) _ (pair_hOne A f g)

#print axioms pair_lift

end CycleQ2AffinePairLifts
