/-
Audit entry point for the pinned external openai/math foundation closure.

This file is not a proof of GF and has NOT been compiled in the target's
Lean 4.33.1 environment. The upstream sources use Lean 4.34.1 and the mathlib
revision specified in minimal-foundations-lakefile.lean. Its purpose is to
give a reproducible next kernel-audit target without introducing any axiom
or assumption that would imply the requested rational primitive.
-/
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage
import OAI.Analysis.HodgeTheory.Decomposition.Constructions
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement

#print axioms OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism.smoothProjective_smoothDeRhamBettiMap_isIso
#print axioms OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage.Integration.projective_algebraicFiltration_image_iff
#print axioms OAI.Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration
#print axioms OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology.smooth_algebraicHypercohomologyCechResolutionEquiv
#print axioms OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.poincareDuality
#print axioms OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction.Constructions.relativeGenerator_restrict_away
#print axioms OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement.Constructions.globalGysinIso_enlargement
