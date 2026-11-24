import Proposal.GeometricLiteralAbelJacobiQPullback

/-!
# The cylinder projection on the ordinary pair-ring two-forms

On the inverse image of any subopen of an original pair of charts, the
pulled two-form is induced by the composite from the native overlap ring
through the original regular functions and the actual projection on rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQPullbackSections

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2GeometricAffineChartSections
  CycleQ2ExteriorSectionNaturality CycleQ2LiteralAbelJacobiQPullback

section NativePull
variable {X Y : Scheme.{0}} (j : X ⟶ Y)
  (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤))
  (hc : ∀ U z, j.app U (coefficientOn Y.sheaf cY U z) = coefficientOn X.sheaf cX (j ⁻¹ᵁ U) z)
  {R : Type} [CommRing R] [Algebra ℂ R] (U : Y.Opens) (f : R →+* Γ(Y,U))
  (hf : ∀ z, f (algebraMap ℂ R z) = coefficientOn Y.sheaf cY U z)

/-- On every native affine exterior form the sheafified pullback agrees
with application of the composite homomorphism of rings of functions. -/
theorem exteriorPull_sectionLift (n : ℕ) (x : ⋀[R]^n (KaehlerDifferential ℂ R)) :
    (exteriorPull j (schemeDifferentialMap j cX cY hc) n).val.app (op U)
      (exteriorSectionLift Y.sheaf cY (differentialSheaf Y.sheaf cY)
        (universalDifferential Y.sheaf cY) U f hf n x) =
      exteriorSectionLift X.sheaf cX (differentialSheaf X.sheaf cX)
        (universalDifferential X.sheaf cX) (j ⁻¹ᵁ U) ((j.app U).hom.comp f)
        (pulledSection_complex j cX cY hc U f hf) n x := by
  let k := schemeDifferentialMap j cX cY hc
  let y := sectionLiftSemilinear Y.sheaf cY _ (universalDifferential Y.sheaf cY) U f hf
  let z := sectionLiftSemilinear X.sheaf cX _ (universalDifferential X.sheaf cX) (j ⁻¹ᵁ U)
    ((j.app U).hom.comp f) (pulledSection_complex j cX cY hc U f hf)
  change (exteriorPull j k n).val.app (op U) (exteriorSection _ _ n U (exteriorMap f y n x)) =
    exteriorSection X.sheaf _ n _ (exteriorMap _ z n x)
  rw [exteriorPull_section]
  apply congrArg
  exact (exteriorMap_composition f (j.app U).hom _ y (onSections j k U) z (fun _ => rfl)
    (fun a => (schemeDifferentialMap_sectionLift j cX cY hc U f hf a).symm) n x).symm

end NativePull

open CycleQ2IncidenceEtaleParameter CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldOverlapAtlas

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)
  (W : Threefold.Opens) (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))

/-- The actual composite from the native pair ring to the moving family on the inverse-image open. -/
def overlapRingMap : FixedOverlap i k →+* Γ(family V t, (toThreefold V t) ⁻¹ᵁ W) :=
  ((toThreefold V t).app W).hom.comp (overlapAlgebraMap i k W h).toRingHom

private theorem compatible (U : Threefold.Opens) (z : ℂ) :
    (toThreefold V t).app U (coefficientOn Threefold.sheaf coefficients U z) =
      coefficientOn (family V t).sheaf (familyCoefficient V t) ((toThreefold V t) ⁻¹ᵁ U) z := by
  rw [coefficientOn_app, toThreefold_overComplex]

theorem overlapRingMap_complex (z : ℂ) :
    overlapRingMap V t i k W h (algebraMap ℂ _ z) =
      coefficientOn (family V t).sheaf (familyCoefficient V t) ((toThreefold V t) ⁻¹ᵁ W) z :=
  pulledSection_complex _ _ _ (compatible V t) W (overlapAlgebraMap i k W h).toRingHom
    (overlapAlgebraMap i k W h).commutes z

set_option maxHeartbeats 750000 in
/-- Pullback of every true native overlap form is given by the actual q on its coefficients. -/
theorem qForms_overlapSection (ω : NativeForms i k) :
    (qForms V t).val.app (op W) (overlapSection i k W h ω) =
      exteriorSectionLift (family V t).sheaf (familyCoefficient V t) (familyDifferentials V t)
        (universalDifferential (family V t).sheaf (familyCoefficient V t)) ((toThreefold V t) ⁻¹ᵁ W)
        (overlapRingMap V t i k W h) (overlapRingMap_complex V t i k W h) 2 ω :=
  exteriorPull_sectionLift (toThreefold V t) (familyCoefficient V t) coefficients (compatible V t) W (overlapAlgebraMap i k W h).toRingHom
    (overlapAlgebraMap i k W h).commutes 2 ω

end CycleQ2LiteralAbelJacobiQPullbackSections
end

#print axioms CycleQ2LiteralAbelJacobiQPullbackSections.qForms_overlapSection
