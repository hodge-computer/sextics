import Proposal.GeometricLiteralAbelJacobiEvaluationFiberSections
import Proposal.GeometricLiteralAbelJacobiTimeContraction
import Proposal.GeometricLiteralAbelJacobiBertiniMinor

/-!
# Vanishing of two-forms on the actual seed sections

Above any affine open of the moving germ the seed section ring is the section
ring of a smooth complex curve. Its two-forms vanish, including on affine
opens contained in several projective charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction

open CategoryTheory AlgebraicGeometry CycleQ2LiteralAbelJacobiEvaluationFiberSections
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SpecializedProjectiveCurve CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiTimeContraction

attribute [local instance] CycleQ2LiteralAbelJacobiEvaluationFiberSections.sourceComplexAlgebra
  CycleQ2LiteralAbelJacobiEvaluationFiberSections.targetComplexAlgebra

private theorem exterior_two_of_affine_open {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension 1 p] (V : X.Opens) (hV : IsAffineOpen V) :
    letI := (baseCoefficient p V).toAlgebra
    Subsingleton (⋀[Γ(X,V)]^2 (KaehlerDifferential ℂ Γ(X,V))) := by
  letI := (baseCoefficient p V).toAlgebra
  have h : SmoothOfRelativeDimension 1 (hV.fromSpec ≫ p) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  rw [fromSpec_baseCoefficient p hV] at h
  exact exteriorTwo_subsingleton_of_curve
    ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)
      (φ := CommRingCat.ofHom (baseCoefficient p V))).mp h)

variable (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens)

private abbrev seedPt := seedPoint (57 : ℂ) Complex.I

theorem seed_sections_exterior_two (hW : IsAffineOpen W) (ht : AlgebraicIndependent ℚ t) :
    Subsingleton (⋀[Target t W]^2 (KaehlerDifferential ℂ (Target t W))) := by
  haveI : SmoothOfRelativeDimension 1 (specializedCurveToBase seedPt t) :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t ht)
  exact exterior_two_of_affine_open (specializedCurveToBase seedPt t)
    (seedCurveToFirstOrderCurve t ⁻¹ᵁ W) (hW.preimage (seedCurveToFirstOrderCurve t))

end CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationFiberSectionsContraction.seed_sections_exterior_two
