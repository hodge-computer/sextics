import Proposal.GeometricThreefoldMixedNormalIndependence

/-!
# Changing the normalized first-order velocity in the mixed one-form

On a common affine open of the first-order family, two normalized time
velocities differ by a tangent of the closed curve. Their ambient mixed
one-forms agree for every test vector defined along that curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldMixedTimeVelocity

open CycleQ2ThreefoldMixedCurveForm CycleQ2ThreefoldMixedNormalIndependence
  CycleQ2ThreefoldContractionAlongMap CycleQ2CurveNormalContraction

variable {T B C : Type} [CommRing T] [CommRing B] [CommRing C]
  [Algebra ℂ T] [Algebra ℂ B] [Algebra ℂ C] [Algebra T B] [Algebra B C] [Algebra T C]
  [IsScalarTower ℂ T B] [IsScalarTower ℂ T C] [IsScalarTower ℂ B C] [IsScalarTower T B C]
  [Module.Projective C (KaehlerDifferential ℂ C)] [Subsingleton (Forms C 2)]

theorem mixed_eq_of_speed (e : B) (hs : Function.Surjective (algebraMap B C))
    (hk : RingHom.ker (algebraMap B C) = Ideal.span {e})
    (κ : Derivation ℂ T C) (v w : Derivation ℂ B C) (hvw : v e = w e) (ω : Forms T 3) :
    mixed κ (v.compAlgebraMap T) ω = mixed κ (w.compAlgebraMap T) ω := by
  obtain ⟨τ,hτ⟩ := exists_tangent_derivation (v-w) hs (by
    intro b hb
    have he : algebraMap B C e = 0 := (le_of_eq hk.symm) (Ideal.subset_span (Set.mem_singleton e))
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp ((le_of_eq hk) hb)
    change v b - w b = 0
    apply sub_eq_zero.mpr
    rw [ha, v.leibniz, w.leibniz, Algebra.smul_def e, Algebra.smul_def e, he, zero_mul, zero_mul, hvw])
  apply mixed_eq_of_tangent κ _ _ τ _ ω
  ext r
  change v (algebraMap T B r) - w (algebraMap T B r) = τ (algebraMap T C r)
  rw [IsScalarTower.algebraMap_apply T B C, hτ]
  rfl

end CycleQ2ThreefoldMixedTimeVelocity
end

#print axioms CycleQ2ThreefoldMixedTimeVelocity.mixed_eq_of_speed
