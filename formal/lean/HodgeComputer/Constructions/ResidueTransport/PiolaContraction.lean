import HodgeComputer.Constructions.HoldoutCover.Piola

/-!
# Contraction under the Piola transform

For an arbitrary finite set of coordinates, the inverse-Jacobian chain
rule transports contraction by the same determinant factor as the Piola
divergence formula. The normal function and the input field are arbitrary.
Unlike the divergence formula, this calculation does not use mixed partial
compatibility or a separate nonzero-determinant hypothesis; the specified
inverse and chain rule suffice.

This completes the paired contraction/divergence interface of the shared
Piola calculus. Prepared for the symmetric-sextic transport in `fqlx`'s
PR #222, with OpenAI ChatGPT and Codex assistance. The coordinate chart,
its Jacobian and its equation remain application data.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Contraction is the companion to `piola_divergence`. -/
theorem piola_contraction (D E : ι → Derivation ℤ K K)
    (M N : Matrix ι ι K) (hNM : N*M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z) (u : ι → K) (f : K) :
    (∑ j, (∑ i, (u i/M.det)*M j i) * E j f) =
      (∑ i, u i * D i f) / M.det := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, column_directional D E M N hNM chain]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms piola_contraction

end HoldoutConstruction
