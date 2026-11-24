import Proposal.GeometricLiteralThreefoldMixedLiftChange
import Proposal.GeometricLiteralThreefoldMixedRestriction
import Proposal.GeometricThreefoldMixedNormalIndependence

/-!
# The overlap and curve presentations of a vertex form

A vertex on the fixed overlap and the same vertex on the curve give
the same ordinary one-form when their ambient velocity agrees on
functions. This identifies both coefficient presentations explicitly.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldMixedVertexBinding

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldMixedLiftChange
  CycleQ2LiteralThreefoldMixedRestriction CycleQ2LiteralThreefoldSurfaceNormal CycleQ2ThreefoldMixedCurveForm

variable {C U : Type} [CommRing C] [Algebra ℂ C] [CommRing U] [Algebra ℂ U]
  [Algebra U C] [IsScalarTower ℂ U C]

theorem vertexMixed_eq_vertexForm {i : Fin 4} (a : T i →ₐ[ℂ] U) (b : T i →ₐ[ℂ] C)
    (h : (IsScalarTower.toAlgHom ℂ U C).comp a = b) (x y : Lift i C)
    (hx : LiesOver x ((IsScalarTower.toAlgHom ℂ U C).comp a)) (hy : LiesOver y ((IsScalarTower.toAlgHom ℂ U C).comp a))
    (hx' : LiesOver x b) (hy' : LiesOver y b) (ν : Derivation ℂ U C) :
    letI := b.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom b
    ∀ v : Derivation ℂ (T i) C, (∀ r, ν (a r) = v r) →
      vertexMixed a x y hx hy ν = vertexForm b x y hx' hy' v := by
  subst b
  let := a.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  let b := (IsScalarTower.toAlgHom ℂ U C).comp a
  let := b.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom b
  let : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  intro v hv
  have e : ν.compAlgebraMap (T i) = v := Derivation.ext hv
  exact congrArg (fun w => mixed (tangent x y hx hy) w (orientedVolume i)) e

/-- The two presentations may use time velocities differing by a tangent
of the smooth curve. The vertex one-form is still unchanged. -/
theorem vertexMixed_eq_mod_curve_tangent {i : Fin 4}
    [Module.Projective C (KaehlerDifferential ℂ C)]
    [Subsingleton (CycleQ2ThreefoldContractionAlongMap.Forms C 2)]
    (a : T i →ₐ[ℂ] U) (b : T i →ₐ[ℂ] C) (h : (IsScalarTower.toAlgHom ℂ U C).comp a = b)
    (x y : Lift i C) (hx : LiesOver x ((IsScalarTower.toAlgHom ℂ U C).comp a))
    (hy : LiesOver y ((IsScalarTower.toAlgHom ℂ U C).comp a))
    (hx' : LiesOver x b) (hy' : LiesOver y b) (ν : Derivation ℂ U C) (τ : Derivation ℂ C C) :
    letI := b.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom b
    ∀ v : Derivation ℂ (T i) C, (∀ r, ν (a r) - v r = τ (b r)) →
      vertexMixed a x y hx hy ν = vertexForm b x y hx' hy' v := by
  subst b
  let := a.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  let b := (IsScalarTower.toAlgHom ℂ U C).comp a
  let := b.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom b
  let : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  intro v hv
  apply CycleQ2ThreefoldMixedNormalIndependence.mixed_eq_of_tangent _ _ _ τ
  exact Derivation.ext hv

/-- Reindexing a projective chart or replacing either explicitly identified
lift preserves the same curve one-form. -/
theorem vertexForm_reindex {i j : Fin 4} (h : i = j) (f : T i →ₐ[ℂ] C) (g : T j →ₐ[ℂ] C)
    (he : ∀ p : MvPolynomial (Option (Fin 3)) ℂ, f (q i p) = g (q j p))
    (x y : Lift i C) (x' y' : Lift j C) (hx : LiesOver x f) (hy : LiesOver y f)
    (hx' : LiesOver x' g) (hy' : LiesOver y' g) (ex : x.x = x'.x) (ey : y.x = y'.x) :
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    letI := g.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom g
    ∀ (v : Derivation ℂ (T i) C) (w : Derivation ℂ (T j) C),
      (∀ p : MvPolynomial (Option (Fin 3)) ℂ, v (q i p) = w (q j p)) →
      vertexForm f x y hx hy v = vertexForm g x' y' hx' hy' w := by
  subst j
  have eg : f = g := by
    apply AlgHom.ext
    intro r
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
    exact he p
  subst g
  obtain rfl := CycleQ2LiteralThreefoldLiftTransition.lift_ext ex
  obtain rfl := CycleQ2LiteralThreefoldLiftTransition.lift_ext ey
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom f
  intro v w hw
  apply congrArg
  apply Derivation.ext
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  exact hw p

end CycleQ2LiteralThreefoldMixedVertexBinding
end

#print axioms CycleQ2LiteralThreefoldMixedVertexBinding.vertexMixed_eq_vertexForm
#print axioms CycleQ2LiteralThreefoldMixedVertexBinding.vertexForm_reindex
