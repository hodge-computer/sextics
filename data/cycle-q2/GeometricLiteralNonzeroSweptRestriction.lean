import Proposal.GeometricLiteralThreefoldCurvePairing
import Proposal.GeometricLiteralCompletedHodgePullback
import Proposal.GeometricLiteralThreefoldOrbitCylinderTest
import Proposal.GeometricLiteralProperSweptSupport

/-!
# Nonzero two-form cohomology on the original swept surface

On a marked curve the evaluation of the pulled ambient test is the negative
of the intrinsic curve class. Its trace detects the ambient class on the
threefold, its proper correspondence and the scheme-theoretic swept image.
The same test detects the normalized sum of the three translated projections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralNonzeroSweptRestriction

open CategoryTheory AlgebraicGeometry Set
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2LiteralThreefoldTestClass (ambientTestClass)
open CycleQ2LiteralAbelJacobiEvaluationDerived (timeHodge)
open CycleQ2LiteralAbelJacobiQPullbackDerived (qHodge)
open CycleQ2LiteralMovingCurveDifferentialNonzero (curveClass_ne_zero)
open CycleQ2LiteralCompletedHodgePullback
open CycleQ2LiteralThreefoldOrbitCylinderTest (averagedCylinderPull primitiveAverage_test)
open CycleQ2LinkageComponentAlgebra (complexRoot complexRoot_cube)
open CycleQ2LiteralProperSweptSupport
open CycleQ2LiteralTimeCorrespondenceCompletion (fixedProjection)
open CycleQ2LiteralAbelJacobiTimeFamily (exists_smooth_time_family)

local instance (X : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from X)) :=
  HasExt.standard _

variable (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) (ht : ∀ i, ChartRegular t i)
  (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

include hi ht hV in
/-- The original projection detects the ambient test on every marked parameter open. -/
theorem pull_nonzero : qHodge V t ambientTestClass ≠ 0 := by
  intro hz
  have h := CycleQ2LiteralThreefoldCurvePairing.signed_class t hi V hV
  rw [hz, map_zero] at h
  exact (neg_ne_zero.mpr (curveClass_ne_zero t ht)) h.symm

include hi ht hV in
/-- Both proper geometric models detect the same test as the original time family. -/
theorem proper_restrictions_nonzero :
    pullToModel (completionMap V t) ambientTestClass ≠ 0 ∧
    pullToModel (sweptMap V t) ambientTestClass ≠ 0 := by
  obtain ⟨hc, hs⟩ := ambientTest_factorizations V t
  have hn := pull_nonzero t hi ht V hV
  constructor
  · intro h
    apply hn
    simpa only [h, map_zero] using hc.symm
  · intro h
    apply hn
    simpa only [h, map_zero] using hs.symm

include hi ht hV in
/-- The normalized orbit detects the test on the family through the original point. -/
theorem average_nonzero :
    averagedCylinderPull complexRoot complexRoot_cube V t ambientTestClass ≠ 0 := by
  rw [primitiveAverage_test, ← CycleQ2LiteralAbelJacobiQTest.qHodge_ambientTestClass]
  exact pull_nonzero t hi ht V hV

/-- The marked ambient class is nonzero in ordinary two-form cohomology of the fixed threefold. -/
theorem ambient_nonzero : ambientTestClass ≠ 0 := by
  obtain ⟨t, hi, ht, V, hV, _⟩ := exists_smooth_time_family
  intro h
  apply pull_nonzero t hi ht V hV
  rw [h, map_zero]

/-- One proper correspondence whose strict swept image detects the fixed ambient class. -/
theorem exists_strict_swept_restriction :
    ∃ (t : Fin 3 → ℂ) (V : parameterScheme.Opens),
      range (fixedProjection V t) ≠ univ ∧
      IsProper (toSweptImage V t) ∧ Function.Surjective (toSweptImage V t) ∧
      pullToModel (completionMap V t) ambientTestClass ≠ 0 ∧
      pullToModel (sweptMap V t) ambientTestClass ≠ 0 ∧
      averagedCylinderPull complexRoot complexRoot_cube V t ambientTestClass ≠ 0 := by
  obtain ⟨t, hi, ht, _⟩ := exists_smooth_time_family
  obtain ⟨V, hV, _, _, _, _, hproper, hsurj, _, _, hstrict⟩ :=
    proper_correspondence_of_independent t hi
  obtain ⟨hc, hs⟩ := proper_restrictions_nonzero t hi ht V hV
  exact ⟨t, V, hstrict, hproper, hsurj, hc, hs, average_nonzero t hi ht V hV⟩

end CycleQ2LiteralNonzeroSweptRestriction
end

#print axioms CycleQ2LiteralNonzeroSweptRestriction.ambient_nonzero
#print axioms CycleQ2LiteralNonzeroSweptRestriction.exists_strict_swept_restriction
