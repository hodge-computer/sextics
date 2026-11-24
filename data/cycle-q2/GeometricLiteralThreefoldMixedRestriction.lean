import Proposal.GeometricLiteralThreefoldMixedGauge
import Proposal.GeometricLiteralThreefoldLiftTransition

/-!
# Restriction of the actual infinitesimal vertex one-form

A change of ambient test lift and a transverse velocity define an ordinary
one-form on the curve. Its restriction agrees with the one-form of the
restricted lifts and velocity on every smaller curve open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldMixedRestriction

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralThreefoldChartVolume

variable {i : Fin 4} {C D : Type} [CommRing C] [Algebra ℂ C] [CommRing D] [Algebra ℂ D]

theorem mapped_liesOver {f : T i →ₐ[ℂ] C} (g : C →ₐ[ℂ] D) (x : Lift i C)
    (hx : LiesOver x f) : LiesOver (mapLift g x) (g.comp f) :=
  fun a => congrArg g (hx a)

theorem mapLift_comp {R : Type} [CommRing R] [Algebra ℂ R] (f : R →ₐ[ℂ] C)
    (g : C →ₐ[ℂ] D) (x : Lift i R) : mapLift g (mapLift f x) = mapLift (g.comp f) x := by
  apply lift_ext
  rfl

private theorem eval_map (g : C →ₐ[ℂ] D) (x : Lift i C) (p : MvPolynomial (Option (Fin 3)) ℂ) :
    aeval (mapLift g x).x p = jetMap g (aeval x.x p) := by
  have h : aeval (mapLift g x).x = (jetMap g).comp (aeval x.x) := by
    apply MvPolynomial.algHom_ext
    intro a
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    rfl
  exact AlgHom.congr_fun h p

/-- The vertex form uses a transverse ambient velocity even when its test
lifts exist only on the closed curve or surface. -/
def vertexForm (f : T i →ₐ[ℂ] C) (x y : Lift i C) (hx : LiesOver x f) (hy : LiesOver y f) :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    Derivation ℂ (T i) C → KaehlerDifferential ℂ C := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  exact fun v => mixed (tangent x y hx hy) v ((-1 : T i)^i.val • chartVolume i)

/-- Restriction of a mixed vertex commutes with every compatible restriction
of its transverse vector, including those on non-affine curve opens. -/
theorem vertexForm_restrict (f : T i →ₐ[ℂ] C) (g : C →ₐ[ℂ] D)
    (x y : Lift i C) (hx : LiesOver x f) (hy : LiesOver y f) :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    letI := (g.comp f).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (g.comp f)
    ∀ (v : Derivation ℂ (T i) C) (v' : Derivation ℂ (T i) D),
      (∀ p, g (v p) = v' p) →
      CycleQ2GeometricAffineOverlap.differentialMap g (vertexForm f x y hx hy v) =
        vertexForm (g.comp f) (mapLift g x) (mapLift g y) (mapped_liesOver g x hx)
          (mapped_liesOver g y hy) v' := by
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom f
  let := (g.comp f).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (g.comp f)
  intro v v' hv
  apply mixed_natural g (fun _ => rfl) _ _ _ _ _ hv
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  change g (tangent x y hx hy (q i p)) = tangent _ _ _ _ (q i p)
  rw [tangent_mk, tangent_mk, eval_map, eval_map, map_sub]
  rfl

end CycleQ2LiteralThreefoldMixedRestriction
end

#print axioms CycleQ2LiteralThreefoldMixedRestriction.vertexForm_restrict
