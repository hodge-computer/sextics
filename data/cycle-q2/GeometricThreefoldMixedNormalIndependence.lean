import Proposal.GeometricThreefoldMixedCurveForm
import Proposal.GeometricCurveNormalContraction

/-!
# Dependence of the mixed one-form on the embedded curve normal

Changing the motion by a vector tangent to the curve leaves the one-form
unchanged. This holds for a test vector defined only along the curve.
On a quotient chart the mixed form therefore depends only on the original
conormal functional of its motion.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedNormalIndependence

open CycleQ2ThreefoldContractionAlongMap CycleQ2ThreefoldMixedCurveForm
  CycleQ2LiteralAbelJacobiContraction CycleQ2CurveNormalContraction

variable {T C : Type} [CommRing T] [CommRing C] [Algebra ℂ T] [Algebra ℂ C]
  [Algebra T C] [IsScalarTower ℂ T C]
  [Module.Projective C (KaehlerDifferential ℂ C)]
  [Subsingleton (Forms C 2)]

/-- The transverse slot kills vectors coming from the curve tangent. -/
theorem mixed_curve_tangent_zero (κ : Derivation ℂ T C) (τ : Derivation ℂ C C)
    (ω : Forms T 3) : mixed κ (τ.compAlgebraMap T) ω = 0 := by
  have h := two_step_eq_mixed (U := C) (alongCovector κ) κ (fun r => by
    rw [alongCovector_D, Algebra.algebraMap_self_apply]) τ ω
  rw [← h, Subsingleton.elim (along 2 _ (alongCovector κ) ω) 0, map_zero]

theorem mixed_eq_of_tangent (κ ν ν' : Derivation ℂ T C) (τ : Derivation ℂ C C)
    (h : ν - ν' = τ.compAlgebraMap T) (ω : Forms T 3) : mixed κ ν ω = mixed κ ν' ω := by
  have ht := mixed_curve_tangent_zero κ τ ω
  rw [← h, mixed_swap (ν-ν') κ, mixed_sub_left, neg_eq_zero] at ht
  rw [mixed_swap ν κ, mixed_swap ν' κ, sub_eq_zero.mp ht]

/-- Changing the representative of the original normal functional does not
change the one-form even if the first vector only exists along the curve. -/
theorem mixed_eq_of_normal (κ ν ν' : Derivation ℂ T C) (hs : Function.Surjective (algebraMap T C))
    (hn : normalComponent ν (RingHom.ker (algebraMap T C)) le_rfl =
      normalComponent ν' (RingHom.ker (algebraMap T C)) le_rfl) (ω : Forms T 3) :
    mixed κ ν ω = mixed κ ν' ω := by
  obtain ⟨τ,hτ⟩ := exists_tangent_derivation (ν-ν') hs (by
    intro r hr
    apply sub_eq_zero.mpr
    exact DFunLike.congr_fun hn ((RingHom.ker (algebraMap T C)).toCotangent ⟨r,hr⟩))
  apply mixed_eq_of_tangent κ ν ν' τ _ ω
  ext r
  exact (hτ r).symm

end CycleQ2ThreefoldMixedNormalIndependence
end

#print axioms CycleQ2ThreefoldMixedNormalIndependence.mixed_eq_of_normal
