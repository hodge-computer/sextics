import Proposal.GeometricLiteralAbelJacobiQPullback
import Proposal.GeometricChartSectionPullback

/-!
# Pullback of a native Kähler exterior form on compatible subopens

The exterior power of the scheme differential carries the exterior section
of an affine form through the same map of chart rings as the underlying
scheme morphism. The formula includes restriction to a subopen of the
inverse image.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitHodgePullback
open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeDifferentialMap
  CycleQ2GeometricSectionDifferentials CycleQ2ExteriorSectionNaturality CycleQ2ChartExteriorBinding
  CycleQ2LiteralAbelJacobiQPullback CycleQ2FiniteCechOrbitPullback

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤))
  (hc : ∀ (U : Y.Opens) (c : ℂ), j.app U (coefficientOn Y.sheaf cY U c) =
    coefficientOn X.sheaf cX (j ⁻¹ᵁ U) c) (n : ℕ)

def formsMap := exteriorPull j (schemeDifferentialMap j cX cY hc) n

def formsAdd := (SheafOfModules.toSheaf Y.ringCatSheaf).map (formsMap j cX cY hc n)

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  (U : Y.Opens) (f : A →+* Γ(Y,U)) (hf : ∀ c : ℂ, f (algebraMap ℂ A c) = coefficientOn Y.sheaf cY U c)

/-- Naturality on the full inverse image, before restriction. -/
theorem formsMap_sectionLift (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (formsMap j cX cY hc n).val.app (op U)
      (exteriorSectionLift Y.sheaf cY _ (universalDifferential Y.sheaf cY) U f hf n ω) =
    exteriorSectionLift X.sheaf cX _ (universalDifferential X.sheaf cX) (j ⁻¹ᵁ U)
      ((j.app U).hom.comp f) (pulledSection_complex j cX cY hc U f hf) n ω := by
  unfold formsMap exteriorSectionLift
  change (exteriorPull j _ n).val.app (op U) (exteriorSection _ _ n U _) = exteriorSection _ _ n _ _
  rw [exteriorPull_section]
  apply congrArg (exteriorSection X.sheaf (differentialSheaf X.sheaf cX).val n (j ⁻¹ᵁ U))
  exact (exteriorMap_composition f (j.app U).hom ((j.app U).hom.comp f)
    (sectionLiftSemilinear Y.sheaf cY _ (universalDifferential Y.sheaf cY) U f hf)
    (onSections j (schemeDifferentialMap j cX cY hc) U)
    (sectionLiftSemilinear X.sheaf cX _ (universalDifferential X.sheaf cX) (j ⁻¹ᵁ U)
      ((j.app U).hom.comp f) (pulledSection_complex j cX cY hc U f hf))
    (fun _ => rfl) (fun η => (schemeDifferentialMap_sectionLift j cX cY hc U f hf η).symm) n ω).symm

/-- The pullback of an affine section on a subopen realizes the differential of
the chart ring map from the commuting chart square. -/
theorem formsMap_sectionLift_restrict (V : X.Opens) (hV : V ≤ j ⁻¹ᵁ U)
    (g : B →+* Γ(X,V)) (hg : ∀ c : ℂ, g (algebraMap ℂ B c) = coefficientOn X.sheaf cX V c)
    (φ : A →ₐ[ℂ] B) (hfg : ∀ a : A, j.appLE U V hV (f a) = g (φ a))
    (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf cX).val n).val.map (homOfLE hV).op
      ((formsMap j cX cY hc n).val.app (op U)
        (exteriorSectionLift Y.sheaf cY _ (universalDifferential Y.sheaf cY) U f hf n ω)) =
    exteriorSectionLift X.sheaf cX _ (universalDifferential X.sheaf cX) V g hg n
      (exteriorDifferentialMap φ n ω) := by
  rw [formsMap_sectionLift]
  exact exteriorSectionLift_restriction X.sheaf cX _ (universalDifferential X.sheaf cX)
    (j ⁻¹ᵁ U) ((j.app U).hom.comp f) (pulledSection_complex j cX cY hc U f hf) V hV g hg φ hfg n ω

end CycleQ2LiteralThreefoldOrbitHodgePullback
end

#print axioms CycleQ2LiteralThreefoldOrbitHodgePullback.formsMap_sectionLift_restrict
