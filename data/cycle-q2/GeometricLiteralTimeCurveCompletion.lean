import Proposal.GeometricLiteralTimeCurveAffineEmbedding
import Proposal.GeometricAffineProjectiveCompletionChart
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Projective closure of the actual smooth fixed-sextic parameter open

Embed the affine parameter curve by a finite set of its regular functions.
For every open in this curve take its scheme-theoretic closure in projective
space. The chosen open embeds densely and its original seed tangent retains
its nonzero value on the proper base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveCompletion

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2LiteralIncidenceTimeCurve
open CycleQ2LiteralTimeCurveAffineEmbedding (variableCount embedding embedding_over)
open CycleQ2AffineProjectiveCompletionChart

abbrev Axes := Fin variableCount

instance curveNoetherian : NoetherianSpace Curve := by
  let := CycleQ2LiteralTimeCurveAffineEmbedding.coordinate_finiteType
  let := Algebra.FiniteType.isNoetherianRing ℂ
    CycleQ2LiteralTimeCurveAffineEmbedding.CoordinateRing
  exact noetherianSpace_of_isAffine (X := Curve)

def intoProjective (U : Curve.Opens) : U.toScheme ⟶ projectiveSpace Axes :=
  U.ι ≫ embedding ≫ affineChart Axes

instance (U : Curve.Opens) : IsImmersion (intoProjective U) := by
  unfold intoProjective
  infer_instance

instance (U : Curve.Opens) : QuasiCompact (intoProjective U) := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set Curve)
  infer_instance

abbrev Completion (U : Curve.Opens) := (intoProjective U).image

def inclusion (U : Curve.Opens) : U.toScheme ⟶ Completion U := (intoProjective U).toImage

def toProjective (U : Curve.Opens) : Completion U ⟶ projectiveSpace Axes :=
  (intoProjective U).imageι

def structureMap (U : Curve.Opens) : Completion U ⟶ Spec (CommRingCat.of ℂ) :=
  toProjective U ≫ projectiveToComplex Axes

instance (U : Curve.Opens) : IsClosedImmersion (toProjective U) :=
  inferInstanceAs (IsClosedImmersion (intoProjective U).imageι)

instance (U : Curve.Opens) : IsOpenImmersion (inclusion U) :=
  inferInstanceAs (IsOpenImmersion (intoProjective U).toImage)

instance (U : Curve.Opens) : QuasiCompact (inclusion U) :=
  inferInstanceAs (QuasiCompact (intoProjective U).toImage)

instance (U : Curve.Opens) : IsDominant (inclusion U) :=
  inferInstanceAs (IsDominant (intoProjective U).toImage)

instance proper (U : Curve.Opens) : IsProper (structureMap U) := by
  let := projectiveToComplex_proper Axes
  unfold structureMap
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_over (U : Curve.Opens) :
    inclusion U ≫ structureMap U = U.ι ≫ toComplex := by
  rw [structureMap, inclusion, toProjective, ← Category.assoc, Scheme.Hom.toImage_imageι,
    intoProjective, Category.assoc, Category.assoc, affineChart_over]
  exact congrArg (fun g => U.ι ≫ g) embedding_over

end CycleQ2LiteralTimeCurveCompletion

#print axioms CycleQ2LiteralTimeCurveCompletion.inclusion_over
#print axioms CycleQ2LiteralTimeCurveCompletion.proper
