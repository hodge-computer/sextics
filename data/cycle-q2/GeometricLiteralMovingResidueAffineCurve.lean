import Proposal.GeometricLiteralMovingResidueAdjunction

/-!
# Adjunction on ordinary differentials of the actual moving affine curve

On an affine surface chart, the closed immersion identifies the section ring
of its inverse image with the quotient by the row equation. Transporting the
conormal wedge through that identification gives the local residue map.
Every one-form of the affine curve comes from a surface one-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueAdjunction

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CycleQ2GeometricAffineOverlap CycleQ2LiteralNativeDifferentialSections
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafCurveBinding CycleQ2GeometricSectionDifferentials
  CycleQ2LiteralMovingResidueFaces CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralMovingResiduePole
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open AffineFrame

attribute [local instance] AffineFrame.surfaceAlgebra AffineFrame.curveAlgebra

variable {W : Surface.Opens} (hW : IsAffineOpen W) (t : Fin 3 → ℂ)
  (ht : ∀ i, ChartRegular t i) (j : FrameData W)

/-- Ordinary Kähler one-forms on the actual affine curve determine sections of
the quotient of the genuine pole sheaf by regular forms. -/
def curveAdjunction : KaehlerDifferential ℂ (CurveRing t W) →+ (residueQuotient t).obj.obj (op W) :=
  (numeratorToResidue t ht j).comp ((chartAdjunction t j).toAddMonoidHom.comp
    ((differentialEquiv (curveQuotientAlgEquiv hW t ht j)).symm.toLinearMap.toAddMonoidHom))

/-- The algebra homomorphism of the actual curve immersion over its complex base. -/
def curveAppHom (t : Fin 3 → ℂ) (W : Surface.Opens) : Γ(Surface,W) →ₐ[ℂ] CurveRing t W where
  toRingHom := ((curveToSurface t).app W).hom
  commutes' := curveMap_constants t

/-- On an affine framed open all curve one-forms are obtained from surface
one-forms. Both functions and scalars of the curve lift on this open. -/
theorem pullback_surjective (hW : IsAffineOpen W) :
    Function.Surjective (differentialMap (curveAppHom t W)) := by
  let φ := curveAppHom t W
  have hf : Function.Surjective φ := (curveToSurface t).app_surjective W hW
  intro β
  have hβ : β ∈ Submodule.span (CurveRing t W) (Set.range (KaehlerDifferential.D ℂ (CurveRing t W))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hβ using Submodule.span_induction with
  | mem _ hm =>
    obtain ⟨x,rfl⟩ := hm
    obtain ⟨a,rfl⟩ := hf x
    exact ⟨KaehlerDifferential.D ℂ _ a, differentialMap_D φ a⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b,map_add _ _ _⟩
  | smul r x _ hx =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨c,rfl⟩ := hf r
    exact ⟨c • a, differentialMap_smul φ c a⟩

private theorem inverse_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (e : B ≃ₐ[ℂ] C)
    (f : A →ₐ[ℂ] B) (g : A →ₐ[ℂ] C) (h : e.toAlgHom.comp f = g) (ω : KaehlerDifferential ℂ A) :
    (differentialEquiv e).symm (differentialMap g ω) = differentialMap f ω := by
  have he := (differentialMap_comp f e.toAlgHom ω).trans (congrArg (fun φ => differentialMap φ ω) h)
  exact (congrArg (differentialEquiv e).symm he.symm).trans ((differentialEquiv e).symm_apply_apply _)

private abbrev equationQuotientMap := Ideal.Quotient.mkₐ ℂ (Ideal.span {equation t j})

private theorem curve_quotient_comp :
    (curveQuotientAlgEquiv hW t ht j).toAlgHom.comp (equationQuotientMap t j) = curveAppHom t W := by
  ext x
  exact curveQuotientEquiv_mk hW t ht j x

private theorem curve_inverse_pullback (ω : KaehlerDifferential ℂ Γ(Surface,W)) :
    (differentialEquiv (curveQuotientAlgEquiv hW t ht j)).symm (differentialMap (curveAppHom t W) ω) =
      differentialMap (equationQuotientMap t j) ω :=
  inverse_comp _ _ _ (curve_quotient_comp hW t ht j) ω

private theorem chart_pullback_mk (ω : KaehlerDifferential ℂ Γ(Surface,W)) :
    numeratorToResidue t ht j (chartAdjunction t j (differentialMap (equationQuotientMap t j) ω)) =
      (cokernel.π (regularInclusion t)).hom.app (op W)
        (poleOfNumerator t ht j (poleNumerator t j (toSheaf Surface.sheaf globalCoefficient W ω))) := by
  exact (congrArg (numeratorToResidue t ht j) (chartAdjunction_map t j ω)).trans
    (numeratorToResidue_mk t ht j _)

theorem curveAdjunction_pullback (ω : KaehlerDifferential ℂ Γ(Surface,W)) :
    curveAdjunction hW t ht j (differentialMap (curveAppHom t W) ω) =
      (cokernel.π (regularInclusion t)).hom.app (op W)
        (poleOfNumerator t ht j (poleNumerator t j (toSheaf Surface.sheaf globalCoefficient W ω))) :=
  (congrArg (fun y => numeratorToResidue t ht j (chartAdjunction t j y))
    (curve_inverse_pullback hW t ht j ω)).trans (chart_pullback_mk t ht j ω)

end CycleQ2LiteralMovingResidueAdjunction
end

#print axioms CycleQ2LiteralMovingResidueAdjunction.curveAdjunction_pullback
#print axioms CycleQ2LiteralMovingResidueAdjunction.pullback_surjective
