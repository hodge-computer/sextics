import Proposal.GeometricLiteralThreefoldTangentCoordinates

/-!
# The differences of first-order coordinate lifts

Two normalized lifts of the same point of the fixed sextic differ by an
intrinsic tangent derivation. On three lifts in a common weight-one chart,
these derivations satisfy the additive overlap identity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldLiftDifference

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldTangentCoordinates

variable {i : Fin 4} {S : Type*} [CommRing S] [Algebra ℂ S]

/-- The first-order coordinates lie over the prescribed point of the fixed chart. -/
def LiesOver (x : Lift i S) (f : T i →ₐ[ℂ] S) : Prop :=
  ∀ a, (x.x a).fst = f (q i (X a))

theorem canonical_liesOver (i : Fin 4) (f : T i →ₐ[ℂ] S) : LiesOver (canonical i f) f :=
  canonical_fst i f

theorem eval_fst (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) (p : P) :
    (aeval x.x p).fst = f (q i p) := by
  have h : (TrivSqZeroExt.fstHom ℂ S S).comp (aeval x.x) = f.comp (q i) := by
    apply MvPolynomial.algHom_ext
    intro a
    simpa only [AlgHom.comp_apply, aeval_X, TrivSqZeroExt.fstHom_apply] using hx a
  exact AlgHom.congr_fun h p

/-- The infinitesimal coordinate of a dual point over a fixed complex algebra map. -/
def jetDerivation {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra A S]
    (v : A →ₐ[ℂ] Jet S) (hv : ∀ a, (v a).fst = algebraMap A S a) : Derivation ℂ A S where
  toFun a := (v a).snd
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    change algebraMap ℂ S c * (v a).snd + 0 * (v a).fst = c • (v a).snd
    rw [zero_mul, add_zero, Algebra.smul_def]
  map_one_eq_zero' := by
    change (v 1).snd = 0
    rw [map_one]
    rfl
  leibniz' a b := by
    change (v (a*b)).snd = a • (v b).snd + b • (v a).snd
    rw [map_mul v]
    change (v a).fst * (v b).snd + (v a).snd * (v b).fst = a • (v b).snd + b • (v a).snd
    rw [hv, hv, Algebra.smul_def, Algebra.smul_def]
    ring

section AlongPoint

variable [Algebra (T i) S] [IsScalarTower ℂ (T i) S]

abbrev point : T i →ₐ[ℂ] S := IsScalarTower.toAlgHom ℂ (T i) S

/-- The difference is a tangent vector along the map to the fixed threefold. -/
def tangent (x y : Lift i S) (hx : LiesOver x point) (hy : LiesOver y point) :
    Derivation ℂ (T i) S :=
  jetDerivation (tangentPoint x y (fun a => (hx a).trans (hy a).symm)) (by
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    change (tangentPoint x y _ (q i p)).fst = _
    rw [tangentPoint_mk]
    exact eval_fst x point hx p)

theorem tangent_mk (x y : Lift i S) (hx : LiesOver x point) (hy : LiesOver y point) (p : P) :
    tangent x y hx hy (q i p) = (aeval x.x p).snd - (aeval y.x p).snd :=
  congrArg TrivSqZeroExt.snd (tangentPoint_mk x y (fun a => (hx a).trans (hy a).symm) p)

theorem tangent_cocycle (x y z : Lift i S)
    (hx : LiesOver x point) (hy : LiesOver y point) (hz : LiesOver z point) :
    tangent x z hx hz = tangent x y hx hy + tangent y z hy hz := by
  ext a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  change tangent x z hx hz (q i p) = tangent x y hx hy (q i p) + tangent y z hy hz (q i p)
  simp only [tangent_mk]
  abel

end AlongPoint
end CycleQ2LiteralThreefoldLiftDifference
end

#print axioms CycleQ2LiteralThreefoldLiftDifference.tangent_mk
#print axioms CycleQ2LiteralThreefoldLiftDifference.tangent_cocycle
