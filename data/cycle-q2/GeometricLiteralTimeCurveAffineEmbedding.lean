import Proposal.GeometricLiteralIncidenceTimeCurve
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A finite affine embedding of the fixed-sextic time curve

The actual pullback curve is affine. Its smooth structure morphism to
the complex point makes its global coordinate algebra finitely generated.
A choice of finitely many generators embeds this curve as a closed
subscheme of the corresponding affine space over the complex numbers.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveAffineEmbedding

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2LiteralIncidenceTimeCurve

abbrev ComplexRing := CommRingCat.of ℂ
abbrev CoordinateRing := Γ(Curve, ⊤)

instance curveAffine : IsAffine Curve := by
  let : IsAffine CycleQ2IncidenceEtaleParameter.parameterScheme :=
    inferInstanceAs (IsAffine (Spec _))
  let : IsAffine CycleQ2IncidenceTimeCurve.sexticBase :=
    inferInstanceAs (IsAffine (Spec _))
  exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine seedSextic
    CycleQ2IncidenceTimeCurve.parameterToSextics

/-- The coefficient map defined by the actual projection to the complex point. -/
def coefficients : ComplexRing ⟶ CoordinateRing :=
  (Scheme.ΓSpecIso ComplexRing).inv ≫ toComplex.appTop

instance coordinateAlgebra : Algebra ℂ CoordinateRing := coefficients.hom.toAlgebra

/-- Pulling constants back along the projection yields the finite-type algebra structure. -/
theorem coordinate_finiteType : Algebra.FiniteType ℂ CoordinateRing := by
  have : SmoothOfRelativeDimension 1 toComplex := smooth_parameter_curve
  have : Smooth toComplex := SmoothOfRelativeDimension.smooth 1 _
  have h : toComplex.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType toComplex inferInstance
  exact h.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso ComplexRing).commRingCatIsoToRingEquiv.symm.surjective)

private theorem exists_presentation :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateRing), Function.Surjective φ :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp coordinate_finiteType

def variableCount : ℕ := exists_presentation.choose

abbrev Poly := MvPolynomial (Fin variableCount) ℂ

def presentation : Poly →ₐ[ℂ] CoordinateRing := exists_presentation.choose_spec.choose

theorem presentation_surjective : Function.Surjective presentation :=
  exists_presentation.choose_spec.choose_spec

abbrev affineSpace := Spec (CommRingCat.of Poly)

def projection : affineSpace ⟶ Spec ComplexRing :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ Poly))

/-- The polynomial quotient presentation as a closed immersion of schemes. -/
def embedding : Curve ⟶ affineSpace :=
  Curve.toSpecΓ ≫ Spec.map (CommRingCat.ofHom presentation.toRingHom)

instance embedding_isClosedImmersion : IsClosedImmersion embedding := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom presentation.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ presentation_surjective
  dsimp only [embedding]
  infer_instance

theorem embedding_over : embedding ≫ projection = toComplex := by
  have h : (CommRingCat.ofHom (algebraMap ℂ Poly)) ≫
      (CommRingCat.ofHom presentation.toRingHom) = coefficients := by
    apply CommRingCat.hom_ext
    exact presentation.comp_algebraMap
  rw [embedding, projection, Category.assoc, ← Spec.map_comp, h, coefficients,
    Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end CycleQ2LiteralTimeCurveAffineEmbedding
end

#print axioms CycleQ2LiteralTimeCurveAffineEmbedding.presentation_surjective
#print axioms CycleQ2LiteralTimeCurveAffineEmbedding.embedding_isClosedImmersion
#print axioms CycleQ2LiteralTimeCurveAffineEmbedding.embedding_over
