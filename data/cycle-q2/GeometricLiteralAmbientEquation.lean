import Proposal.GeometricSeedSmooth
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FinCases

/-! The four weight-one derivatives of the incidence threefold at the trace seed.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2LiteralAmbientEquation

open MvPolynomial CycleQ2IncidenceEquations CycleQ2GeometricSeedSmooth

/-- The incidence cubic at θ = 1 includes the `a ^ 3` term. -/
def cubic {R : Type*} [CommRing R] (a b c d : R) : R :=
  d^3 + c^3 + b*c*d + a*c*d + a*b^2 + a^3

/-- Four quintic derivatives of the sextic on the branch space. -/
def gradient {R : Type*} [CommRing R] (a b c d : R) : Fin 4 → R :=
  ![6*a^5 + 2*cubic a b c d*(c*d+b^2+3*a^2),
    6*b^5 + 3*(2-57^3)*b^2*d^3 + 2*cubic a b c d*(c*d+2*a*b),
    6*c^5 + 2*cubic a b c d*(3*c^2+b*d+a*d),
    6*d^5 + 3*(2-57^3)*b^3*d^2 + 2*cubic a b c d*(3*d^2+b*c+a*c)]

theorem gradient_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b c d : R) (j : Fin 4) :
    f (gradient a b c d j) = gradient (f a) (f b) (f c) (f d) j := by
  fin_cases j <;> simp [gradient, cubic, map_ofNat]

/-- The field-independent gradient expressions specialize to the derivatives of
 the defining polynomial of the literal incidence hypersurface. -/
theorem pderiv_incidence (j : Fin 4) :
    pderiv j.castSucc (smoothF (57 : ℂ) Complex.I) =
      gradient (X 0) (X 1) (X 2) (X 3) j := by
  rw [← seedFamily_at_incidence_seed, seedFamily_expanded]
  have h2 (k : Fin 5) : pderiv k (2 : SeedPolynomial) = 0 := by
    rw [← (map_ofNat (C : ℂ →+* SeedPolynomial) 2)]
    exact pderiv_C
  have h57 (k : Fin 5) : pderiv k (57 : SeedPolynomial) = 0 := by
    rw [← (map_ofNat (C : ℂ →+* SeedPolynomial) 57)]
    exact pderiv_C
  fin_cases j <;> simp [gradient, cubic, smoothB, Derivation.leibniz, map_ofNat, h2, h57] <;> ring

/-- A field-valued test for the four ordinary coordinates suffices on all four
normalized projective charts. The residue field can be transcendental over ℂ. -/
theorem ambient_prime_cover_of_gradient
    (test : ∀ {K : Type} [Field K] [CharZero K] (a b c d : K),
      (∀ j, gradient a b c d j = 0) → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)
    (J : Ideal SeedPolynomial) [J.IsPrime] (i : Fin 4)
    (hi : X i.castSucc - 1 ∈ J) (_hF : smoothF (57 : ℂ) Complex.I ∈ J) :
    ∃ j : Fin 5, pderiv j (smoothF (57 : ℂ) Complex.I) ∉ J := by
  by_contra! h
  let f := algebraMap SeedPolynomial J.ResidueField
  let : CharZero J.ResidueField := charZero_of_injective_ringHom (f.comp C).injective
  have hg (j : Fin 4) :
      gradient (f (X 0)) (f (X 1)) (f (X 2)) (f (X 3)) j = 0 := by
    rw [← gradient_map, ← pderiv_incidence]
    exact Ideal.algebraMap_residueField_eq_zero.mpr (h j.castSucc)
  obtain ⟨h0, h1, h2, h3⟩ := test _ _ _ _ hg
  have hz : f (X i.castSucc) = 0 := by fin_cases i <;> assumption
  have hu : f (X i.castSucc - 1) = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hi
  rw [map_sub, map_one, hz, zero_sub, neg_eq_zero] at hu
  exact one_ne_zero hu

end CycleQ2LiteralAmbientEquation
