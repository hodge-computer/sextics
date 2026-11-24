import Proposal.GeometricIncidenceFirstOrderCanonicalH2
import Proposal.GeometricSeedConeSection

/-!
# The retained tangent cubic is nonzero on the seed surface

The map from the seed surface to the original trace curve carries the
polynomial to the cubic already detected by its paired Čech class. If
its image were zero, the literal fraction representing that class
would have zero numerator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAbelJacobiCubicNonzeroSeed

open CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricLiteralSurface
  CycleQ2IncidenceFirstOrderTrace CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2GeometricSurfaceCoordinates CycleQ2NormalConnecting

/-- The actual tangent polynomial does not vanish on the original trace curve. -/
theorem curve_cubic_ne_zero :
    curveMap 57 1 (substitute firstOrderWeightedCubic.val) ≠ 0 := by
  rw [firstOrderWeightedCubic_substitute]
  intro h
  apply firstOrder_pairedClass_ne_zero
  let p := -derivativeNumerator (cubicDeformation firstOrderCubicDirection)
  have hp : p.IsHomogeneous 9 := (derivativeNumerator_homogeneous firstOrderCubicDirection).neg
  have hn : curveMap 57 1 p = 0 := by
    simp only [p, derivativeNumerator, map_neg, map_mul, h, mul_zero, neg_zero]
  have hz : degreeNineRepresentative 57 1 p hp = 0 := by
    apply Subtype.ext
    change awayFraction 57 1 (curveG1 57 1 * curveG2 57 1) 1 (curveMap 57 1 p) = 0
    rw [hn]
    exact Localization.mk_zero _
  change (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) (degreeNineRepresentative 57 1 p hp) = 0
  rw [hz, map_zero]

/-- The same weighted cubic has nonzero class in the literal seed cone ring. -/
theorem seed_cubic_ne_zero :
    CycleQ2SeedConeSection.quotient firstOrderWeightedCubic.val ≠ 0 := by
  intro h
  have hs : quotientMap 57 1 firstOrderWeightedCubic.val = 0 := by
    apply (seedRingEquiv 57).injective
    rw [seedRingEquiv_quotient, map_zero]
    exact h
  apply curve_cubic_ne_zero
  change curveGradedMap 57 1 (quotientMap 57 1 firstOrderWeightedCubic.val) = 0
  rw [hs, map_zero]

end CycleQ2LiteralAbelJacobiCubicNonzeroSeed

#print axioms CycleQ2LiteralAbelJacobiCubicNonzeroSeed.seed_cubic_ne_zero
