import Proposal.GeometricSeedConeSection
import Mathlib.Data.Finsupp.Encodable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# An algebraically independent regular section of the seed surface

The associated primes of the nine pivot rings exclude finitely many proper
linear subspaces of coefficient triples. A linear equation containing each
subspace can be avoided along with all nonzero rational polynomial relations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2LiteralAbelJacobiIndependentRegular

open MvPolynomial
open CycleQ2SeedConeSection CycleQ2IncidenceImageLine CycleQ2UniversalCurveCartier
  CycleQ2RegularSeedSection CycleQ2SimultaneousRegularSection

private theorem separatingPolynomial (W : Submodule ℂ (Fin 3 → ℂ)) (v : Fin 3 → ℂ)
    (hv : v ∉ W) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ ∀ t ∈ W, eval t P = 0 := by
  have hn : W.mkQ v ≠ 0 := fun e => hv ((Submodule.Quotient.mk_eq_zero W).mp e)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hn
  let L := l.comp W.mkQ
  let P : MvPolynomial (Fin 3) ℂ := ∑ j, X j * C (L (Pi.single j 1))
  have he (t : Fin 3 → ℂ) : eval t P = L t := by
    simp only [P, map_sum, map_mul, eval_X, eval_C]
    calc
      ∑ j, t j * L (Pi.single j 1) = L (∑ j, t j • Pi.single j 1) := by simp
      _ = L t := by
        congr 1
        funext i
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
  refine ⟨P, fun h => hl ?_, fun t ht => ?_⟩
  · simpa only [L, LinearMap.comp_apply, h, map_zero] using (he v).symm
  · rw [he]
    change l (W.mkQ t) = 0
    rw [show W.mkQ t = 0 from (Submodule.Quotient.mk_eq_zero W).mpr ht, map_zero]

theorem independent_avoiding_subspaces {ι : Type*} [Countable ι]
    (bad : ι → Submodule ℂ (Fin 3 → ℂ)) (v : Fin 3 → ℂ) (hv : ∀ i, v ∉ bad i) :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ ∀ i, t ∉ bad i := by
  classical
  choose P hP hvan using fun i => separatingPolynomial (bad i) v (hv i)
  let : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let : Countable (MvPolynomial (Fin 3) ℚ) := Countable.of_equiv _ AddMonoidAlgebra.coeffEquiv.symm
  let Rel := {p : MvPolynomial (Fin 3) ℚ // p ≠ 0}
  let polys : Rel ⊕ ι → MvPolynomial (Fin 3) ℂ :=
    Sum.elim (fun p => MvPolynomial.map (algebraMap ℚ ℂ) p.val) P
  have hn (i : Rel ⊕ ι) : polys i ≠ 0 := by
    cases i with
    | inl p =>
      intro h
      apply p.property
      apply MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
      simpa only [polys, Sum.elim_inl, map_zero] using h
    | inr i => exact hP i
  obtain ⟨t, ht⟩ := CycleQ2VeryGeneral.exists_avoiding_polynomials 3 polys hn
  refine ⟨t, algebraicIndependent_iff.mpr ?_, fun i hi => ht (.inr i) (hvan i t hi)⟩
  intro p hp
  by_contra h
  apply ht (.inl ⟨p, h⟩)
  simpa only [polys, Sum.elim_inl, eval_map, aeval_def] using hp

/-- The same algebraically independent triple cuts a regular hypersurface
on every original matrix-pivot localization of the seed. -/
theorem exists_independent_regular :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ t ≠ 0 ∧
      ∀ p : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed p)
        (algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1)) := by
  classical
  obtain ⟨v, hv, hreg⟩ := exists_regular_ordinary_equations seed
  let A := fun p : CycleQ2SegreCech.Chart => CoefficientPivot seed p
  let : ∀ p, Fintype (associatedPrimes (A p) (A p)) :=
    fun p => (associatedPrimes.finite (A p) (A p)).fintype
  let Index := Σ p, associatedPrimes (A p) (A p)
  let bad : Option Index → Submodule ℂ (Fin 3 → ℂ) := fun i =>
    match i with
    | none => ⊥
    | some ⟨p, q⟩ => (q.val.restrictScalars ℂ).comap
        (coefficientCombination (localizedMatrix seed p p.1))
  have hvbad (i : Option Index) : v ∉ bad i := by
    cases i with
    | none => exact hv
    | some i =>
      intro hi
      have hm : (∑ j, v j • localizedMatrix seed i.1 i.1.1 j) ∈
          ⋃ q ∈ associatedPrimes (A i.1) (A i.1), (q : Set (A i.1)) :=
        Set.mem_iUnion.mpr ⟨i.2.val, Set.mem_iUnion.mpr ⟨i.2.property, hi⟩⟩
      rw [biUnion_associatedPrimes_eq_compl_regular (A i.1) (A i.1)] at hm
      exact hm ((constantEquation_localize seed v i.1) ▸ hreg i.1)
  obtain ⟨t, ht, hgood⟩ := independent_avoiding_subspaces bad v hvbad
  refine ⟨t, ht, hgood none, fun p => ?_⟩
  rw [constantEquation_localize]
  by_contra hn
  have hm : (∑ j, t j • localizedMatrix seed p p.1 j) ∈
      ⋃ q ∈ associatedPrimes (A p) (A p), (q : Set (A p)) := by
    rw [biUnion_associatedPrimes_eq_compl_regular (A p) (A p)]
    exact hn
  obtain ⟨q, hm⟩ := Set.mem_iUnion.mp hm
  obtain ⟨hq, hmem⟩ := Set.mem_iUnion.mp hm
  exact hgood (some ⟨p, ⟨q, hq⟩⟩) hmem

#print axioms exists_independent_regular

end CycleQ2LiteralAbelJacobiIndependentRegular
