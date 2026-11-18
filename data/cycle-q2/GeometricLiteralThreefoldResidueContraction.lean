import Proposal.GeometricLiteralThreefoldKodairaSpencer
import Proposal.GeometricExteriorSheaf
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# The two-form associated to a threefold deformation

Contracting a three-form by the actual Jacobian-chart Kodaira–Spencer
differences gives two-forms satisfying the additive cocycle identity.
The construction uses interior multiplication on exterior powers and
commutes with semilinear restriction of the covector and the form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueContraction

open CycleQ2GeometricExteriorSheaf CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2GeometricSurfaceFirstOrder

section Exterior

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- Interior multiplication, with sign positive in the first slot. -/
def interior (n : ℕ) (v : M →ₗ[R] R) : (⋀[R]^(n+1) M) →ₗ[R] (⋀[R]^n M) :=
  exteriorPower.alternatingMapLinearEquiv <|
    AlternatingMap.alternatizeUncurryFin (v.smulRight (exteriorPower.ιMulti R n))

theorem interior_wedge (n : ℕ) (v : M →ₗ[R] R) (m : Fin (n+1) → M) :
    interior n v (exteriorPower.ιMulti R (n+1) m) =
      ∑ j : Fin (n+1), (-1 : ℤ) ^ (j : ℕ) •
        (v (m j) • exteriorPower.ιMulti R n (j.removeNth m)) := by
  simp [interior, AlternatingMap.alternatizeUncurryFin_apply]

theorem interior_add (n : ℕ) (v w : M →ₗ[R] R) :
    interior n (v+w) = interior n v + interior n w := by
  have h : (v + w).smulRight (exteriorPower.ιMulti R n (M := M)) =
      v.smulRight (exteriorPower.ιMulti R n (M := M)) + w.smulRight (exteriorPower.ιMulti R n (M := M)) := by
    apply LinearMap.ext
    intro x
    simp [add_smul]
  unfold interior
  rw [h, AlternatingMap.alternatizeUncurryFin_add, map_add]

variable {S N : Type} [CommRing S] [AddCommGroup N] [Module S N]

theorem interior_natural (φ : R →+* S) (f : M →ₛₗ[φ] N) (v : M →ₗ[R] R)
    (u : N →ₗ[S] S) (hvu : ∀ x, u (f x) = φ (v x)) (n : ℕ) (ω : ⋀[R]^(n+1) M) :
    interior n u (exteriorMap φ f (n+1) ω) = exteriorMap φ f n (interior n v ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [exteriorMap_wedge, interior_wedge, interior_wedge, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hvu, map_zsmul, map_smulₛₗ, exteriorMap_wedge]
      rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]

end Exterior

abbrev Chart (i : Fin 4) (s : Finset Index) := Closed (localF i s)
abbrev Forms (i : Fin 4) (s : Finset Index) (n : ℕ) := ⋀[Chart i s]^n (KaehlerDifferential ℂ (Chart i s))

/-- The two-form obtained from the normalized splitting difference on an
actual fixed-sextic Jacobian intersection and a three-form on that chart. -/
def twoForm (i : Fin 4) (s : Finset Index) (j k : Index) (hj : j ∈ s) (hk : k ∈ s)
    (ω : Forms i s 3) : Forms i s 2 :=
  interior 2 (tangent i s j k hj hk).liftKaehlerDifferential ω

private theorem lift_tangents_add {R : Type} [CommRing R] [Algebra ℂ R]
    (x y : Derivation ℂ R R) :
    (x+y).liftKaehlerDifferential = x.liftKaehlerDifferential + y.liftKaehlerDifferential :=
  (KaehlerDifferential.linearMapEquivDerivation ℂ R (M := R)).symm.map_add x y

private theorem interior_tangents_add {R : Type} [CommRing R] [Algebra ℂ R]
    (x y : Derivation ℂ R R) (ω : ⋀[R]^3 (KaehlerDifferential ℂ R)) :
    interior 2 (x+y).liftKaehlerDifferential ω =
      interior 2 x.liftKaehlerDifferential ω + interior 2 y.liftKaehlerDifferential ω := by
  rw [lift_tangents_add x y, interior_add]
  rfl

theorem twoForm_cocycle (i : Fin 4) (s : Finset Index) (j k l : Index)
    (hj : j ∈ s) (hk : k ∈ s) (hl : l ∈ s) (ω : Forms i s 3) :
    twoForm i s j l hj hl ω = twoForm i s j k hj hk ω + twoForm i s k l hk hl ω := by
  exact (congrArg (fun δ : Derivation ℂ (Chart i s) (Chart i s) =>
    interior 2 δ.liftKaehlerDifferential ω) (tangent_cocycle i s j k l hj hk hl)).trans
      (interior_tangents_add _ _ ω)

end CycleQ2LiteralThreefoldResidueContraction
end

#print axioms CycleQ2LiteralThreefoldResidueContraction.interior_natural
#print axioms CycleQ2LiteralThreefoldResidueContraction.twoForm_cocycle
