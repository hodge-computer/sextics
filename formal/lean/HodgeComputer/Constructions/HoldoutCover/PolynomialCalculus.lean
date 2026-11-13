import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/- Source component: PolynomialPartials -/
section
/-! Ambient polynomial partial derivatives in the integer-linear interface
used by the residue and finite-field extension lemmas. -/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial

variable {R σ : Type*} [CommRing R]

theorem pderiv_commute (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    if_neg hij, if_neg (Ne.symm hij), add_zero]
  rw [show m+Finsupp.single i 1+Finsupp.single j 1 =
    m+Finsupp.single j 1+Finsupp.single i 1 by abel]
  ring

def integerPartial (i : σ) :
    Derivation ℤ (MvPolynomial σ R) (MvPolynomial σ R) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem integerPartial_apply (i : σ) (p : MvPolynomial σ R) :
    integerPartial i p = MvPolynomial.pderiv i p := rfl

@[simp] theorem integerPartial_C (i : σ) (r : R) :
    integerPartial i (MvPolynomial.C r) = 0 := by
  simp [integerPartial]

@[simp] theorem integerPartial_X_self (i : σ) :
    integerPartial i (MvPolynomial.X i : MvPolynomial σ R) = 1 := by
  simp

@[simp] theorem integerPartial_X_of_ne (i j : σ) (h : j ≠ i) :
    integerPartial i (MvPolynomial.X j : MvPolynomial σ R) = 0 := by
  simp [h]

theorem integerPartial_commute (i j : σ) (p : MvPolynomial σ R) :
    integerPartial i (integerPartial j p) = integerPartial j (integerPartial i p) :=
  pderiv_commute i j p

theorem integerPartials_commute (i j : σ) :
    Function.Commute (integerPartial (R := R) i) (integerPartial j) :=
  integerPartial_commute i j

end HoldoutConstruction

#print axioms HoldoutConstruction.pderiv_commute
#print axioms HoldoutConstruction.integerPartials_commute
end
end

/- Source component: PolynomialChainRule -/
section
/-!
The polynomial chain rule over a coefficient ring killed by an integer-
linear derivation. It applies to coordinates in arbitrary field extensions;
no independence of those coordinates is assumed.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

variable {R L σ : Type*} [CommRing R] [Field L] [Fintype σ] [DecidableEq σ]

theorem derivation_eval₂_chain
    (D : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r) = 0) (p : MvPolynomial σ R) :
    D (MvPolynomial.eval₂Hom φ x p) =
      ∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i) := by
  let θ := MvPolynomial.eval₂Hom φ x
  change D (θ p) = ∑ i, θ (MvPolynomial.pderiv i p)*D (x i)
  induction p using MvPolynomial.induction_on with
  | C r => simp [θ, hC]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz]
    simp only [θ, MvPolynomial.eval₂Hom_X', smul_eq_mul] at hp ⊢
    rw [hp]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval₂Hom_X',
      add_mul, Finset.sum_add_distrib]
    have hsum : (∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*
        x j*D (x i)) = x j*(∑ i, MvPolynomial.eval₂Hom φ x
          (MvPolynomial.pderiv i p)*D (x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hdelta : (∑ i, MvPolynomial.eval₂Hom φ x p *
        MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i (MvPolynomial.X j))*D (x i)) =
      MvPolynomial.eval₂Hom φ x p*D (x j) := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, ite_mul]
    rw [hdelta]
    ring

end HoldoutConstruction

#print axioms HoldoutConstruction.derivation_eval₂_chain
end
end
