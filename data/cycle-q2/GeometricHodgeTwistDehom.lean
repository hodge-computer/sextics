import Proposal.GeometricHodgeTwistCech
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Laurent normal forms in a weight-one chart

Fix an inverted coordinate xᵢ. Dehomogenizing forgets its Laurent exponent.
The twist and the power of w reconstruct that exponent uniquely. On a
single chart the three remaining exponents are nonnegative, giving exactly
three ordinary polynomial coefficients of the monic cubic power basis.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeTwistDehom
open CycleQ2HodgeTwistCech

abbrev Offset (i : Vertex) (S : Finset Vertex) :=
  {b : Fin 3 → ℤ // ∀ q, b q < 0 → i.succAbove q ∈ S}

/-- Exponents in normalized coordinates xₐ/xᵢ with xᵢ inverted. -/
def exponentEquiv (t : ℤ) (j : Fin 3) (i : Vertex) (S : Finset Vertex) (hi : i ∈ S) :
    {e : Exp // Allowed t S j e} ≃ Offset i S where
  toFun a := ⟨fun q => a.val (i.succAbove q), fun q h => a.property.2 _ h⟩
  invFun b := ⟨i.insertNth (t - 2 * (j.val : ℤ) - ∑ q, b.val q) b.val, by
    constructor
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
      simp only [Fin.insertNth_apply_succAbove]
      abel
    · intro a ha
      by_cases h : a = i
      · simpa [h] using hi
      · obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq h
        exact b.property q (by simpa using ha)⟩
  left_inv a := by
    apply Subtype.ext
    change i.insertNth (t - 2 * (j.val : ℤ) - ∑ q, a.val (i.succAbove q)) (fun q => a.val (i.succAbove q)) = a.val
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨?_, rfl⟩
    have hg := a.property.1
    rw [Fin.sum_univ_succAbove _ i] at hg
    omega
  right_inv b := by
    apply Subtype.ext
    funext q
    change (i.insertNth (α := fun _ => ℤ) (t - 2 * (j.val : ℤ) - ∑ q, b.val q) b.val) (i.succAbove q) = b.val q
    exact Fin.insertNth_apply_succAbove (α := fun _ => ℤ) i _ b.val q

variable {A : Type*} [AddCommGroup A]

/-- Extract the allowed monomial coefficients, with finite support in each power slot. -/
def rowCoordinates (t : ℤ) (S : Finset Vertex) : sections A t S ≃+
    ((j : Fin 3) → {e : Exp // Allowed t S j e} →₀ A) := by
  classical
  exact {
    toFun := fun p j => (p.val j).subtypeDomain (Allowed t S j)
    invFun := fun v => ⟨fun j => (v j).extendDomain, fun j e he => by simp [Finsupp.extendDomain_apply, he]⟩
    left_inv := fun p => Subtype.ext (funext fun j => Finsupp.extendDomain_subtypeDomain (p.val j) (by
      intro e he
      by_contra hn
      exact (Finsupp.mem_support_iff.mp he) (p.property j e hn)))
    right_inv := fun v => funext fun j => Finsupp.subtypeDomain_extendDomain (v j)
    map_add' := fun p q => funext fun j => Finsupp.subtypeDomain_add }

/-- The actual additive equivalence for any nonempty intersection of weight-one charts. -/
def chartCoordinates (t : ℤ) (i : Vertex) (S : Finset Vertex) (hi : i ∈ S) :
    sections A t S ≃+ (Fin 3 → (Offset i S →₀ A)) :=
  (rowCoordinates t S).trans (AddEquiv.piCongrRight fun j => Finsupp.domCongr (exponentEquiv t j i S hi))

/-- On a singleton no normalized coordinate remains inverted. -/
def singletonExp (i : Vertex) : Offset i {i} ≃ (Fin 3 →₀ ℕ) where
  toFun b := Finsupp.equivFunOnFinite.symm fun q => (b.val q).toNat
  invFun m := ⟨fun q => (m q : ℤ), fun q h => False.elim ((Int.natCast_nonneg (m q)).not_gt h)⟩
  left_inv b := by
    apply Subtype.ext
    funext q
    apply Int.toNat_of_nonneg
    by_contra! hn
    exact i.succAbove_ne q (Finset.mem_singleton.mp (b.property q hn))
  right_inv m := by
    ext q
    exact Int.toNat_natCast (m q)

/-- An integral twist has precisely three polynomial coefficient slots on a single chart. -/
def singletonChart (R : Type*) [CommRing R] (t : ℤ) (i : Vertex) :
    sections R t {i} ≃+ (Fin 3 → MvPolynomial (Fin 3) R) :=
  (chartCoordinates t i {i} (Finset.mem_singleton_self i)).trans
    (AddEquiv.piCongrRight fun _ => (Finsupp.domCongr (singletonExp i)).trans AddMonoidAlgebra.coeffAddEquiv.symm)

end CycleQ2HodgeTwistDehom
end

#print axioms CycleQ2HodgeTwistDehom.chartCoordinates
#print axioms CycleQ2HodgeTwistDehom.singletonChart
