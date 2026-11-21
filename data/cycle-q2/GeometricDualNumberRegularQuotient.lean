import Proposal.GeometricDualNumberFlatness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A regular special-fiber equation gives a flat first-order quotient

Let B be flat over k[epsilon]. If the image of f is a nonzerodivisor
in B/(epsilon), then B/(f) is flat over k[epsilon]. The proof is the
elementary epsilon-kernel diagram chase, followed by the established
dual-number flatness criterion. It requires neither finiteness of B
as a module nor a pre-existing flatness assumption on the quotient.

This is a first-order statement. Binding a particular incidence tangent
algebra and its actual section specialization is a separate step; no
flatness over the full incidence parameter algebra is inferred here.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2DualNumberRegularQuotient

open scoped DualNumber
open CycleQ2DualNumberFlatness

variable {k B : Type*} [Field k] [CommRing B] [Algebra k[ε] B]

def epsilonIdeal (B : Type*) [CommRing B] [Algebra k[ε] B] : Ideal B :=
  Ideal.span {algebraMap k[ε] B ε}

theorem quotient_epsilon_zero :
    Ideal.Quotient.mk (epsilonIdeal (k := k) B) (algebraMap k[ε] B ε) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- A regular equation on the special fiber of a flat first-order
ambient algebra cuts out an actually flat first-order quotient. -/
theorem quotient_flat [Module.Flat k[ε] B] (f : B)
    (hreg : IsSMulRegular (B ⧸ epsilonIdeal (k := k) B)
      (Ideal.Quotient.mk (epsilonIdeal (k := k) B) f)) :
    Module.Flat k[ε] (B ⧸ Ideal.span {f}) := by
  let e : B := algebraMap k[ε] B ε
  let I : Ideal B := epsilonIdeal (k := k) B
  let J : Ideal B := Ideal.span {f}
  let q₀ : B →+* B ⧸ I := Ideal.Quotient.mk I
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  have he₀ : q₀ e = 0 := quotient_epsilon_zero (k := k) (B := B)
  have hf : q f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))
  have heq : q e = algebraMap k[ε] (B ⧸ J) ε :=
    (IsScalarTower.algebraMap_apply k[ε] B (B ⧸ J) ε).symm
  change Module.Flat k[ε] (B ⧸ J)
  apply flat_of_eps_smul
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hprod : q (e * b) = 0 := by
    rw [map_mul, heq]
    simpa only [Algebra.smul_def (R := k[ε]) (A := B ⧸ J), q] using hx
  have hmem : e * b ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hprod
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hc₀ : q₀ c = 0 := by
    apply hreg.right_eq_zero_of_smul
    change q₀ f * q₀ c = 0
    rw [← map_mul, ← hc, map_mul, he₀, zero_mul]
  have hcI : c ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hc₀
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hcI
  have hzero : e * (b - f * d) = 0 := by
    calc
      _ = e * b - f * c := by rw [hd]; ring
      _ = 0 := by rw [hc, sub_self]
  obtain ⟨v, hv⟩ := eps_smul_eq_zero_of_flat (k := k) (M := B) (b - f * d)
    (by simpa only [Algebra.smul_def] using hzero)
  refine ⟨q v, ?_⟩
  rw [Algebra.smul_def (R := k[ε]) (A := B ⧸ J)]
  change q b = algebraMap k[ε] (B ⧸ J) ε * q v
  rw [Algebra.smul_def] at hv
  have hquot := congrArg q hv
  simp only [map_sub, map_mul, hf, zero_mul, sub_zero] at hquot
  change q b = q e * q v at hquot
  rw [heq] at hquot
  exact hquot

end CycleQ2DualNumberRegularQuotient

end

#print axioms CycleQ2DualNumberRegularQuotient.quotient_epsilon_zero
#print axioms CycleQ2DualNumberRegularQuotient.quotient_flat
