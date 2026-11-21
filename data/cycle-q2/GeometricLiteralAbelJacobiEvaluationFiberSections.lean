import Proposal.GeometricLiteralAbelJacobiEvaluationFiber
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual seed section ring on every affine open of the germ

For each affine open of the infinitesimal moving curve, the functions on the
inverse image in the seed are obtained by quotienting its functions by the
pullback of epsilon. The isomorphism takes a lifted function to its restriction
along the given projective curve inclusion.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationFiberSections

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2IncidenceFirstOrder
  CycleQ2SpecializedProjectiveCurve CycleQ2IncidencePolynomialJacobianBinding
open scoped DualNumber

/-- Restrict a coefficient of the original affine base to the indicated open. -/
def baseCoefficient {X : Scheme.{0}} {K : CommRingCat.{0}} (p : X ⟶ Spec K) (W : X.Opens) :
    K →+* Γ(X,W) :=
  ((Scheme.ΓSpecIso K).inv ≫ p.appTop ≫ X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom

theorem fromSpec_baseCoefficient {X : Scheme.{0}} {K : CommRingCat.{0}} (p : X ⟶ Spec K)
    {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (baseCoefficient p W)) := by
  change _ = Spec.map ((Scheme.ΓSpecIso K).inv ≫ p.appTop ≫ _)
  rw [Spec.map_comp, Spec.map_comp, ← hW.fromSpec_toSpecΓ]
  simp only [Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private abbrev seedPt := seedPoint (57 : ℂ) Complex.I
abbrev Source (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens) := Γ(firstOrderCurve t,W)
abbrev Target (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens) :=
  Γ(specializedCurve seedPt t,seedCurveToFirstOrderCurve t ⁻¹ᵁ W)

variable (t : Fin 3 → ℂ) (W : (firstOrderCurve t).Opens)

abbrev dualCoefficient : ℂ[ε] →+* Source t W := baseCoefficient (firstOrderCurveToBase t) W
abbrev seedCoefficient : ℂ →+* Target t W :=
  baseCoefficient (specializedCurveToBase seedPt t) (seedCurveToFirstOrderCurve t ⁻¹ᵁ W)
abbrev restriction : Source t W →+* Target t W := ((seedCurveToFirstOrderCurve t).app W).hom
abbrev epsilonSection : Source t W := dualCoefficient t W ε

/-- The section square is the base change along the actual dual-number point. -/
theorem section_square (hW : IsAffineOpen W) :
    IsPullback (Spec.map (CommRingCat.ofHom (restriction t W)))
      (Spec.map (CommRingCat.ofHom (seedCoefficient t W)))
      (Spec.map (CommRingCat.ofHom (dualCoefficient t W))) firstOrderClosedPoint := by
  let j := seedCurveToFirstOrderCurve t
  have hc : IsAffineOpen (j ⁻¹ᵁ W) := hW.preimage j
  have hchart : IsPullback (Spec.map (j.app W)) hc.fromSpec hW.fromSpec j := by
    apply IsOpenImmersion.isPullback
    · simpa only [Scheme.Hom.appLE_eq_app] using
        (IsAffineOpen.SpecMap_appLE_fromSpec j hW hc le_rfl).symm
    · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]
  have hseed : IsPullback (specializedCurveToBase seedPt t) j firstOrderClosedPoint (firstOrderCurveToBase t) :=
    IsPullback.of_iso_pullback ⟨(seedCurveToFirstOrderCurve_overBase t).symm⟩ (firstOrderCurveSeedFiberIso t)
      (firstOrderCurveSeedFiberIso_hom_fst t) (firstOrderCurveSeedFiberIso_hom_snd t)
  exact (fromSpec_baseCoefficient (specializedCurveToBase seedPt t) hc) ▸
    (fromSpec_baseCoefficient (firstOrderCurveToBase t) hW) ▸ hchart.paste_vert hseed.flip

private abbrev residue := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

private theorem ring_square {S C : Type} [CommRing S] [CommRing C] (a : ℂ[ε] →+* S)
    (b : ℂ →+* C) (u : S →+* C)
    (h : IsPullback (Spec.map (CommRingCat.ofHom u)) (Spec.map (CommRingCat.ofHom b))
      (Spec.map (CommRingCat.ofHom a)) firstOrderClosedPoint) :
    u.comp a = b.comp residue := by
  have e := h.w
  rw [firstOrderClosedPoint, ← Spec.map_comp, ← Spec.map_comp] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp e)

private theorem kernel_of_dual_fiber {S C : Type} [CommRing S] [CommRing C]
    (a : ℂ[ε] →+* S) (b : ℂ →+* C) (u : S →+* C)
    (h : IsPullback (Spec.map (CommRingCat.ofHom u)) (Spec.map (CommRingCat.ofHom b))
      (Spec.map (CommRingCat.ofHom a)) firstOrderClosedPoint) :
    RingHom.ker u = Ideal.span {a ε} := by
  let J : Ideal S := Ideal.span {a ε}
  let q := Ideal.Quotient.mk J
  let c := q.comp (a.comp (algebraMap ℂ ℂ[ε]))
  have hq : q.comp a = c.comp residue := by
    apply RingHom.ext
    intro x
    have he : x = algebraMap ℂ ℂ[ε] x.fst + algebraMap ℂ ℂ[ε] x.snd * ε := by
      apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    change q (a x) = q (a (algebraMap ℂ ℂ[ε] x.fst))
    conv_lhs => rw [he]
    rw [map_add, map_mul, map_add, map_mul, show q (a ε) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), mul_zero, add_zero]
  have hs : Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom c) ≫ firstOrderClosedPoint := by
    rw [firstOrderClosedPoint, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hq)
  obtain ⟨l,hl⟩ := Spec.map_surjective (h.lift _ _ hs)
  have hx := h.lift_fst _ _ hs
  rw [← hl, ← Spec.map_comp] at hx
  have hlq : l.hom.comp u = q := congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hx)
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (RingHom.congr_fun hlq x).symm.trans ((congrArg l.hom hx).trans (map_zero _))
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact (RingHom.congr_fun (ring_square a b u h) ε).trans (map_zero b)

/-- The kernel of the sheaf restriction map on any affine open is generated by epsilon there. -/
theorem restriction_kernel (hW : IsAffineOpen W) : RingHom.ker (restriction t W) = Ideal.span {epsilonSection t W} :=
  kernel_of_dual_fiber _ _ _ (section_square t W hW)

theorem restriction_surjective (hW : IsAffineOpen W) : Function.Surjective (restriction t W) :=
  (seedCurveToFirstOrderCurve t).app_surjective W hW

local instance sourceComplexAlgebra : Algebra ℂ (Source t W) :=
  ((dualCoefficient t W).comp (algebraMap ℂ ℂ[ε])).toAlgebra

local instance targetComplexAlgebra : Algebra ℂ (Target t W) := (seedCoefficient t W).toAlgebra

/-- Reduction of functions on the actual open as a complex-algebra map. -/
def restrictionHom (hW : IsAffineOpen W) : Source t W →ₐ[ℂ] Target t W where
  toRingHom := restriction t W
  commutes' z := RingHom.congr_fun (ring_square _ _ _ (section_square t W hW)) (algebraMap ℂ ℂ[ε] z)

def quotientEquiv (hW : IsAffineOpen W) :
    (Source t W ⧸ Ideal.span {epsilonSection t W}) ≃ₐ[ℂ] Target t W :=
  (Ideal.quotientEquivAlgOfEq ℂ (restriction_kernel t W hW).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := restrictionHom t W hW) (restriction_surjective t W hW))

@[simp] theorem quotientEquiv_mk (hW : IsAffineOpen W) (s : Source t W) :
    quotientEquiv t W hW (Ideal.Quotient.mk _ s) = restriction t W s := rfl

end CycleQ2LiteralAbelJacobiEvaluationFiberSections
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationFiberSections.restriction_kernel
#print axioms CycleQ2LiteralAbelJacobiEvaluationFiberSections.quotientEquiv_mk
