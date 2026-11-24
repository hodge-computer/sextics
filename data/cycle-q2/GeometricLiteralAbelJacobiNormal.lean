import Proposal.GeometricDualNumberRegularQuotient
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The embedded normal functional of a flat first-order curve chart

For a fixed ambient coordinate ring P mapping into a flat algebra B over
the dual numbers, the closed fibre has ideal I = ker(P → B/(ε)).
Evaluation of a member of I gives a multiple of ε in B. Its unique
coefficient in B/(ε) defines the normal functional on I/I². The
normalization uses the original parameter ε.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAbelJacobiNormal

open scoped DualNumber
open CycleQ2DualNumberRegularQuotient

variable {k : Type*} [Field k] (B : Type*) [CommRing B] [Algebra k[ε] B]

private abbrev e : B := algebraMap k[ε] B ε

private theorem e_mul_self : e (k := k) B * e (k := k) B = 0 := by
  rw [e, ← map_mul, DualNumber.eps_mul_eps, map_zero]

/-- Multiplication by ε on a lift of a closed-fibre function. -/
def epsilonTimes : (B ⧸ epsilonIdeal (k := k) B) →ₗ[B] epsilonIdeal (k := k) B :=
  (epsilonIdeal (k := k) B).liftQ
    ((LinearMap.mulLeft B (e (k := k) B)).codRestrict _ (fun b =>
      Ideal.mem_span_singleton.mpr ⟨b, rfl⟩)) (by
      intro b hb
      apply Subtype.ext
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      change e (k := k) B * b = 0
      rw [hc, ← mul_assoc, e_mul_self, zero_mul])

theorem epsilonTimes_mk (b : B) :
    ((epsilonTimes (k := k) B (Ideal.Quotient.mk _ b) : epsilonIdeal (k := k) B) : B) =
      algebraMap k[ε] B ε * b := rfl

/-- Flatness identifies the epsilon ideal with the actual closed-fibre ring. -/
def epsilonEquiv [Module.Flat k[ε] B] :
    (B ⧸ epsilonIdeal (k := k) B) ≃ₗ[B] epsilonIdeal (k := k) B :=
  LinearEquiv.ofBijective (epsilonTimes (k := k) B) (by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h : algebraMap k[ε] B ε * b = 0 := congrArg Subtype.val hx
      obtain ⟨c, hc⟩ := CycleQ2DualNumberFlatness.eps_smul_eq_zero_of_flat
        (k := k) (M := B) b (by simpa only [Algebra.smul_def] using h)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨c, by simpa only [Algebra.smul_def] using hc⟩)
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      exact ⟨Ideal.Quotient.mk _ c, Subtype.ext hc.symm⟩)

section Embedded

variable (P : Type*) [CommRing P] [Algebra P B]

abbrev closedIdeal := (epsilonIdeal (k := k) B).comap (algebraMap P B)

private def mapIdeal : closedIdeal (k := k) B P →ₗ[P] epsilonIdeal (k := k) B :=
  ((Algebra.linearMap P B).comp (closedIdeal (k := k) B P).subtype).codRestrict
    ((epsilonIdeal (k := k) B).restrictScalars P) (fun a => a.property)

private def evalIdeal [Module.Flat k[ε] B] :
    closedIdeal (k := k) B P →ₗ[P] B ⧸ epsilonIdeal (k := k) B :=
  ((epsilonEquiv (k := k) B).symm.toLinearMap.restrictScalars P).comp (mapIdeal (k := k) B P)

theorem evalIdeal_on_lift [Module.Flat k[ε] B] (x : closedIdeal (k := k) B P) (b : B)
    (hx : algebraMap P B (x : P) = algebraMap k[ε] B ε * b) :
    evalIdeal (k := k) B P x = Ideal.Quotient.mk _ b := by
  apply (epsilonEquiv (k := k) B).injective
  change (epsilonEquiv (k := k) B) ((epsilonEquiv (k := k) B).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext hx

private theorem evalIdeal_mul [Module.Flat k[ε] B] (x y : closedIdeal (k := k) B P) :
    evalIdeal (k := k) B P (x * y) = 0 := by
  have ⟨a, ha⟩ := Ideal.mem_span_singleton.mp x.property
  have ⟨b, hb⟩ := Ideal.mem_span_singleton.mp y.property
  have hz : algebraMap P B ((x * y : closedIdeal (k := k) B P) : P) = algebraMap k[ε] B ε * 0 := by
    change algebraMap P B ((x : P) * (y : P)) = _
    rw [map_mul, ha, hb, mul_zero]
    calc
      _ = (e (k := k) B * e (k := k) B) * (a * b) := by ring
      _ = 0 := by rw [e_mul_self, zero_mul]
  exact (evalIdeal_on_lift B P (x * y) 0 hz).trans (map_zero _)

/-- The functional on the conormal of the special fibre in the fixed ambient chart. -/
def normal [Module.Flat k[ε] B] :
    (closedIdeal (k := k) B P).Cotangent →ₗ[P] B ⧸ epsilonIdeal (k := k) B :=
  Ideal.Cotangent.lift (evalIdeal (k := k) B P) (evalIdeal_mul (k := k) B P)

theorem normal_on_lift [Module.Flat k[ε] B] (x : closedIdeal (k := k) B P) (b : B)
    (hx : algebraMap P B (x : P) = algebraMap k[ε] B ε * b) :
    normal (k := k) B P ((closedIdeal (k := k) B P).toCotangent x) = Ideal.Quotient.mk _ b :=
  evalIdeal_on_lift B P x b hx

end Embedded
end CycleQ2LiteralAbelJacobiNormal
end

#print axioms CycleQ2LiteralAbelJacobiNormal.normal_on_lift
