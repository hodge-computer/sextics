import Proposal.GeometricLiteralThreefoldLiftDifference

/-!
# A cotangent functional from an ordinary dual-number point

Its value on a differential is the infinitesimal component of the given
point. Addition of tangent components over a common point gives addition
of the resulting cotangent functionals.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2TangentPointDifferential

open CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

/-- The semilinear functional on differentials along an explicit affine point. -/
def covector (f : R →ₐ[ℂ] S) (v : R →ₐ[ℂ] Jet S) (hv : ∀ r, (v r).fst = f r) :
    KaehlerDifferential ℂ R →ₛₗ[f.toRingHom] S := by
  letI := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algHom f
  let d := (jetDerivation v hv).liftKaehlerDifferential
  exact
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun r x => (d.map_smul r x).trans (Algebra.smul_def r (d x)) }

@[simp] theorem covector_D (f : R →ₐ[ℂ] S) (v : R →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) (r : R) :
    covector f v hv (KaehlerDifferential.D ℂ R r) = (v r).snd := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algHom f
  exact Derivation.liftKaehlerDifferential_comp_D (jetDerivation v hv) r

theorem covector_add (f : R →ₐ[ℂ] S) (v w z : R →ₐ[ℂ] Jet S)
    (hv : ∀ r, (v r).fst = f r) (hw : ∀ r, (w r).fst = f r) (hz : ∀ r, (z r).fst = f r)
    (h : ∀ r, (z r).snd = (v r).snd + (w r).snd) :
    covector f z hz = covector f v hv + covector f w hw := by
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ R)
  intro r
  exact (covector_D _ _ _ _).trans ((h r).trans
    (congrArg₂ (· + ·) (covector_D _ _ _ _).symm (covector_D _ _ _ _).symm))

end CycleQ2TangentPointDifferential
end

#print axioms CycleQ2TangentPointDifferential.covector_D
#print axioms CycleQ2TangentPointDifferential.covector_add
