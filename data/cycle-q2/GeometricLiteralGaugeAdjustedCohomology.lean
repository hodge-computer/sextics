import Proposal.GeometricLiteralNativeGaugeSections

/-!
# Actual refined scalar cohomology and the explicit gauge coboundary

The original projected cup is restricted to the actual twelve-open cover
using the existing finite-cover Cech-to-derived comparison. Subtracting
the constructed alternating gauge boundary preserves the same genuine
derived scalar class. Identification of its increasing face values with
the actual native contraction is a separate representative binding.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralGaugeAdjustedCohomology

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2CartierProjectiveCover CycleQ2LiteralCartierProjectedCup
  CycleQ2LiteralNativeGaugeSections

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

def oldFiniteCup : Two coefficientSheaf (coverFamily 57 1) :=
  CycleQ2FourToFiniteCech.extendTwo (coverFamily 57 1) projectedCup

theorem oldFiniteCup_normalized : NormalizedTwo coefficientSheaf (coverFamily 57 1) oldFiniteCup :=
  CycleQ2FourToFiniteCech.extendTwo_normalized (coverFamily 57 1) projectedCup

theorem oldFiniteCup_closed : IsTwoCocycle coefficientSheaf (coverFamily 57 1) oldFiniteCup :=
  CycleQ2FourToFiniteCech.extendTwo_closed (coverFamily 57 1)
    CycleQ2ProjectiveCartierIntersections.literal_cover projectedCup projectedCup_closed

def refinedOriginalCup : Two coefficientSheaf cover :=
  CycleQ2FiniteCechRefinement.restrictTwo (coverFamily 57 1) cover Prod.fst cover_first oldFiniteCup

theorem refinedOriginalCup_normalized : NormalizedTwo coefficientSheaf cover refinedOriginalCup :=
  CycleQ2FiniteCechRefinement.restrictTwo_normalized (coverFamily 57 1) cover Prod.fst cover_first
    oldFiniteCup oldFiniteCup_normalized

theorem refinedOriginalCup_closed : IsTwoCocycle coefficientSheaf cover refinedOriginalCup :=
  CycleQ2FiniteCechRefinement.restrictTwo_closed (coverFamily 57 1) cover Prod.fst cover_first
    oldFiniteCup oldFiniteCup_closed

theorem refinedOriginalCup_class :
    cechTwoClass cover cover_covers refinedOriginalCup refinedOriginalCup_normalized refinedOriginalCup_closed =
      projectedDerivedClass := by
  calc
    _ = cechTwoClass (coverFamily 57 1) CycleQ2ProjectiveCartierIntersections.literal_cover
        oldFiniteCup oldFiniteCup_normalized oldFiniteCup_closed :=
      CycleQ2FiniteCechRefinement.cechTwoClass_refinement (coverFamily 57 1) cover Prod.fst cover_first
        CycleQ2ProjectiveCartierIntersections.literal_cover cover_covers oldFiniteCup oldFiniteCup_normalized oldFiniteCup_closed
    _ = projectedDerivedClass := CycleQ2FourToFiniteCech.finiteClass_eq_fourClass (coverFamily 57 1)
      CycleQ2ProjectiveCartierIntersections.literal_cover projectedCup projectedCup_closed

def gaugeAdjustedCup : Two coefficientSheaf cover := refinedOriginalCup - gaugeBoundary

theorem faceValue_sub (c d : Two coefficientSheaf cover)
    (u v w : CycleQ2LiteralProjectiveIntersections.Vertex) (W : Opens (projectiveSurface 57 1))
    (hu : W ≤ cover u) (hv : W ≤ cover v) (hw : W ≤ cover w) :
    faceValue coefficientSheaf cover (c - d) u v w W hu hv hw =
      faceValue coefficientSheaf cover c u v w W hu hv hw -
        faceValue coefficientSheaf cover d u v w W hu hv hw := map_sub _ _ _

theorem gaugeAdjustedCup_normalized : NormalizedTwo coefficientSheaf cover gaugeAdjustedCup where
  repeat12 u w W hu hw := by
    rw [gaugeAdjustedCup, faceValue_sub, refinedOriginalCup_normalized.repeat12,
      gaugeBoundary_normalized.repeat12, sub_self]
  repeat23 u v W hu hv := by
    rw [gaugeAdjustedCup, faceValue_sub, refinedOriginalCup_normalized.repeat23,
      gaugeBoundary_normalized.repeat23, sub_self]
  swap12 u v w W hu hv hw := by
    rw [gaugeAdjustedCup, faceValue_sub, faceValue_sub, refinedOriginalCup_normalized.swap12,
      gaugeBoundary_normalized.swap12]
    abel
  swap23 u v w W hu hv hw := by
    rw [gaugeAdjustedCup, faceValue_sub, faceValue_sub, refinedOriginalCup_normalized.swap23,
      gaugeBoundary_normalized.swap23]
    abel

theorem gaugeAdjustedCup_closed : IsTwoCocycle coefficientSheaf cover gaugeAdjustedCup := by
  intro u v w z W hu hv hw hz
  have h0 := refinedOriginalCup_closed u v w z W hu hv hw hz
  have h1 := gaugeBoundary_closed u v w z W hu hv hw hz
  change faceValue coefficientSheaf cover (refinedOriginalCup - gaugeBoundary) v w z W hv hw hz -
    faceValue coefficientSheaf cover (refinedOriginalCup - gaugeBoundary) u w z W hu hw hz +
    faceValue coefficientSheaf cover (refinedOriginalCup - gaugeBoundary) u v z W hu hv hz -
    faceValue coefficientSheaf cover (refinedOriginalCup - gaugeBoundary) u v w W hu hv hw = 0
  simp only [faceValue_sub]
  linear_combination (norm := abel) h0 - h1

theorem gaugeAdjustedCup_class :
    cechTwoClass cover cover_covers gaugeAdjustedCup gaugeAdjustedCup_normalized gaugeAdjustedCup_closed =
      projectedDerivedClass := by
  rw [← refinedOriginalCup_class]
  apply cechTwoClass_eq_of_difference_boundary cover cover_covers gaugeAdjustedCup refinedOriginalCup
    gaugeAdjustedCup_normalized refinedOriginalCup_normalized gaugeAdjustedCup_closed refinedOriginalCup_closed (-gaugeOne)
  intro u v w W hu hv hw
  have hb := faceValue_gaugeBoundary u v w W hu hv hw
  change boundaryValue coefficientSheaf cover (-gaugeOne) u v w W hu hv hw =
    faceValue coefficientSheaf cover (gaugeAdjustedCup - refinedOriginalCup) u v w W hu hv hw
  rw [faceValue_sub, gaugeAdjustedCup, faceValue_sub]
  unfold boundaryValue edgeValue at *
  simp only [Pi.neg_apply, map_neg] at *
  linear_combination (norm := abel) hb

def gaugeAdjustedClass : coefficientSheaf.H' 2 ⊤ :=
  cechTwoClass cover cover_covers gaugeAdjustedCup gaugeAdjustedCup_normalized gaugeAdjustedCup_closed

theorem gaugeAdjustedClass_eq_original : gaugeAdjustedClass = projectedDerivedClass := gaugeAdjustedCup_class

theorem gaugeAdjustedClass_ne_zero : gaugeAdjustedClass ≠ 0 := by
  rw [gaugeAdjustedClass_eq_original]
  exact projectedDerivedClass_ne_zero

end CycleQ2LiteralGaugeAdjustedCohomology

end

#print axioms CycleQ2LiteralGaugeAdjustedCohomology.refinedOriginalCup_class
#print axioms CycleQ2LiteralGaugeAdjustedCohomology.gaugeAdjustedCup_class
#print axioms CycleQ2LiteralGaugeAdjustedCohomology.gaugeAdjustedClass_ne_zero
