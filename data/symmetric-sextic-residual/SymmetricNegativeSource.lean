import Proposal.WeightedFiberSmoothness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The exact negative weighted-sextic source space

The coordinates are `(a,b,c,d,u)`, with weights `(1,1,1,1,2)`.
The involution changes the signs of `c,d`.  This module defines the source
space by its actual monomial coefficients, not by an unbound matrix.
-/

noncomputable section

namespace SymmetricNegativeSource

open MvPolynomial
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Exponent := Fin 5 →₀ ℕ

def weightedDegree (e : Exponent) : ℕ :=
  e 0 + e 1 + e 2 + e 3 + 2 * e 4

def Allowed (e : Exponent) : Prop :=
  weightedDegree e = 6 ∧ (e 2 + e 3) % 2 = 1

instance : DecidablePred Allowed := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- All weighted sextics whose monomials are odd under `(c,d) ↦ (-c,-d)`. -/
def source : Submodule ℂ Poly :=
  AddMonoidAlgebra.supported ℂ ℂ {e | Allowed e}

theorem mem_source (p : Poly) :
    p ∈ source ↔ ∀ e, coeff e p ≠ 0 → Allowed e := by
  rw [source, AddMonoidAlgebra.mem_supported]
  constructor
  · intro hp e he
    exact hp (Finsupp.mem_support_iff.mpr he)
  · intro hp e he
    exact hp e (Finsupp.mem_support_iff.mp he)

/-- Write `c+d=2*k+1`, choose `u`, then choose `a` and `c`.
This enumerates sixty monomials directly, without a large ambient search. -/
abbrev Index := Σ k : Fin 3, Σ u : Fin (3 - k.val),
  Fin (6 - 2 * k.val - 2 * u.val) × Fin (2 * k.val + 2)

def indexExponent (j : Index) : Exponent :=
  Finsupp.equivFunOnFinite.symm
    ![j.2.2.1.val, 5 - 2 * j.1.val - 2 * j.2.1.val - j.2.2.1.val,
      j.2.2.2.val, 2 * j.1.val + 1 - j.2.2.2.val, j.2.1.val]

theorem index_allowed (j : Index) : Allowed (indexExponent j) := by
  rcases j with ⟨⟨k, hk⟩, ⟨u, hu⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩
  simp [Allowed, weightedDegree, indexExponent]
  dsimp at hu ha hc ⊢
  omega

def indexedMonomial (j : Index) : {e : Exponent // Allowed e} :=
  ⟨indexExponent j, index_allowed j⟩

theorem indexedMonomial_injective : Function.Injective indexedMonomial := by
  intro x y h
  rcases x with ⟨⟨k, hk⟩, ⟨u, hu⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩
  rcases y with ⟨⟨k', hk'⟩, ⟨u', hu'⟩, ⟨a', ha'⟩, ⟨c', hc'⟩⟩
  have he := congrArg Subtype.val h
  have h0 := congrArg (fun e : Exponent => e 0) he
  have h2 := congrArg (fun e : Exponent => e 2) he
  have h3 := congrArg (fun e : Exponent => e 3) he
  have h4 := congrArg (fun e : Exponent => e 4) he
  simp [indexedMonomial, indexExponent] at h0 h2 h3 h4
  dsimp at hu ha hc hu' ha' hc'
  have hkk : k = k' := by omega
  subst k'
  subst u'
  subst a'
  subst c'
  rfl

theorem indexedMonomial_surjective : Function.Surjective indexedMonomial := by
  rintro ⟨e, he⟩
  have hdeg := he.1
  have hodd := he.2
  unfold weightedDegree at hdeg
  let k := (e 2 + e 3) / 2
  have hk : k < 3 := by dsimp [k]; omega
  have hu : e 4 < 3 - k := by dsimp [k]; omega
  have ha : e 0 < 6 - 2 * k - 2 * e 4 := by dsimp [k]; omega
  have hc : e 2 < 2 * k + 2 := by dsimp [k]; omega
  refine ⟨⟨⟨k, hk⟩, ⟨e 4, hu⟩, ⟨e 0, ha⟩, ⟨e 2, hc⟩⟩, ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [indexedMonomial, indexExponent, k] <;> omega

def indexEquiv : Index ≃ {e : Exponent // Allowed e} :=
  Equiv.ofBijective indexedMonomial
    ⟨indexedMonomial_injective, indexedMonomial_surjective⟩

instance allowedFintype : Fintype {e : Exponent // Allowed e} :=
  Fintype.ofEquiv Index indexEquiv

theorem index_card : Fintype.card Index = 60 := by
  decide

theorem allowed_card : Fintype.card {e : Exponent // Allowed e} = 60 := by
  rw [← Fintype.card_congr indexEquiv, index_card]

def coefficientEquiv : source ≃ₗ[ℂ] ({e : Exponent // Allowed e} →₀ ℂ) :=
  AddMonoidAlgebra.supportedEquivFinsupp {e | Allowed e}

instance source_finiteDimensional : FiniteDimensional ℂ source :=
  coefficientEquiv.symm.finiteDimensional

theorem source_finrank : Module.finrank ℂ source = 60 := by
  rw [coefficientEquiv.finrank_eq, Module.finrank_finsupp, allowed_card]
  simp

#print axioms allowed_card
#print axioms source_finrank

end SymmetricNegativeSource
