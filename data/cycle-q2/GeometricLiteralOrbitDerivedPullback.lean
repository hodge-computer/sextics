import Proposal.GeometricAutomorphismCohomology
import Proposal.GeometricLiteralOrbitChernPullback
import Proposal.GeometricCotangentPairAction

/-!
# The automorphism action on the actual derived Chern classes

Exact functorial transport on Ext sends the original Cartier class to the
first translated class. A second application sends it to the class of the
square of the same literal projective automorphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitDerivedPullback

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralSheafOneClasses CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitChern
  CycleQ2LiteralOrbitChernPullback CycleQ2LiteralOrbitBoundary
  CycleQ2AutomorphismCohomology

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (z : ℂ) (hz : z ^ 3 = 1)

private abbrev e := closedProjectiveAction z hz

private abbrev pullMap := differentialAddMap (e z hz).hom
  (coefficient_of_overComplex (e z hz).hom _ (surfaceAction_overComplex z hz))

/-- Pullback on H¹ by the literal projective scheme automorphism and its
canonical sheaf differential. -/
def chernPull : differentialAddSheaf.H' 1 ⊤ →+ differentialAddSheaf.H' 1 ⊤ :=
  pullH (Scheme.forgetToTop.mapIso (e z hz)) (pullMap z hz) 1

theorem chernPull_original :
    chernPull z hz chernDerivedClass = translatedClass (e z hz).hom := by
  unfold chernPull chernDerivedClass
  exact (pullH_cechOneClass (Scheme.forgetToTop.mapIso (e z hz)) cover cover_covers
    (translatedCover_top (e z hz).hom) (pullMap z hz) chernOne chernOne_closed).trans
      (class_pullOne_chern (e z hz).hom (coefficient_of_overComplex (e z hz).hom _ (surfaceAction_overComplex z hz)))

theorem chernPull_translated (f : Surface ⟶ Surface) :
    chernPull z hz (translatedClass f) = translatedClass ((e z hz).hom ≫ f) := by
  unfold chernPull
  change pullH _ _ 1 (CycleQ2FiniteCechHOne.cechOneClass (translatedCover f)
    (translatedCover_top f) (translatedOne f _ id _) _) = _
  exact (pullH_cechOneClass (Scheme.forgetToTop.mapIso (e z hz)) (translatedCover f)
    (translatedCover_top f) (translatedCover_top ((e z hz).hom ≫ f)) (pullMap z hz)
    (translatedOne f _ id (fun _ => le_rfl)) (translatedOne_closed f _ id (fun _ => le_rfl))).trans
      (class_pullOne_translated (e z hz).hom (coefficient_of_overComplex (e z hz).hom _ (surfaceAction_overComplex z hz)) f)

theorem orbitDerivedClass_eq_derived_orbit :
    orbitDerivedClass z hz =
      chernDerivedClass + chernPull z hz chernDerivedClass +
        chernPull z hz (chernPull z hz chernDerivedClass) := by
  rw [chernPull_original, chernPull_translated, orbitDerivedClass_eq_sum]

end CycleQ2LiteralOrbitDerivedPullback

end

#print axioms CycleQ2LiteralOrbitDerivedPullback.orbitDerivedClass_eq_derived_orbit
