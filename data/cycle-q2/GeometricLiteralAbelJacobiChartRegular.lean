import Proposal.GeometricLiteralAbelJacobiIndependentRegular
import Proposal.GeometricLiteralAbelJacobiSeedLiftConeRegular
import Proposal.GeometricSeedSectionAffineInjective

/-!
# One section vector for the linkage charts and the cone pivots

On the original sixty-three affine refinements, failure of regularity is
detected by finitely many associated primes. Avoiding the corresponding
linear subspaces together with rational polynomial relations gives a section
vector that meets the linkage regularity conditions and the homogeneous
pivot conditions at once.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiChartRegular

open Matrix
open CycleQ2SeedConeSection CycleQ2IncidenceImageLine CycleQ2UniversalCurveCartier
  CycleQ2RegularSeedSection CycleQ2SimultaneousRegularSection
  CycleQ2SeedSectionIdealComparison CycleQ2SeedSectionInverse CycleQ2FirstOrderCurveChartFlat
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralAbelJacobiIndependentRegular
  CycleQ2LiteralAbelJacobiSeedLiftConeRegular

/-- The same algebraically independent vector satisfies all 27 linkage
regularity conditions and all nine homogeneous cone regularity conditions. -/
theorem exists_independent_chartRegular :
    ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t ∧ t ≠ 0 ∧
      (∀ i : Fin 3, ChartRegular t i) ∧
      ∀ p : CycleQ2SegreCech.Chart, IsSMulRegular (CoefficientPivot seed p)
        (algebraMap (PointSurface seed) (CoefficientPivot seed p) (constantEquation seed t p.1)) := by
  classical
  obtain ⟨v, hv, hreg⟩ := exists_nonzero_simultaneous_regular (k := ℂ)
    RegularityRing regularityCoefficient regularityCoefficient_hasUnit
  let A := RegularityRing
  let : ∀ i, Fintype (associatedPrimes (A i) (A i)) :=
    fun i => (associatedPrimes.finite (A i) (A i)).fintype
  let Index := Σ i, associatedPrimes (A i) (A i)
  let bad : Option Index → Submodule ℂ (Fin 3 → ℂ) := fun i =>
    match i with
    | none => ⊥
    | some ⟨i, q⟩ => (q.val.restrictScalars ℂ).comap
        (coefficientCombination (regularityCoefficient i))
  have hvbad (i : Option Index) : v ∉ bad i := by
    cases i with
    | none => exact hv
    | some i =>
      intro hi
      have hm : (∑ j, v j • regularityCoefficient i.1 j) ∈
          ⋃ q ∈ associatedPrimes (A i.1) (A i.1), (q : Set (A i.1)) :=
        Set.mem_iUnion.mpr ⟨i.2.val, Set.mem_iUnion.mpr ⟨i.2.property, hi⟩⟩
      rw [biUnion_associatedPrimes_eq_compl_regular (A i.1) (A i.1)] at hm
      exact hm (hreg i.1)
  obtain ⟨t, ht, hgood⟩ := independent_avoiding_subspaces bad v hvbad
  have hregular (i : RegularityIndex) : IsSMulRegular (A i) (∑ j, t j • regularityCoefficient i j) := by
    by_contra hn
    have hm : (∑ j, t j • regularityCoefficient i j) ∈
        ⋃ q ∈ associatedPrimes (A i) (A i), (q : Set (A i)) := by
      rw [biUnion_associatedPrimes_eq_compl_regular (A i) (A i)]
      exact hn
    obtain ⟨q, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hq, hmem⟩ := Set.mem_iUnion.mp hm
    exact hgood (some ⟨i, ⟨q, hq⟩⟩) hmem
  refine ⟨t, ht, hgood none, ?_, ?_⟩
  · intro i p
    have he : ((refinedFactorData i p).matrix *ᵥ refinedVector t i p) p.1 =
        ∑ j, t j • (refinedFactorData i p).matrix p.1 j := by
      simp only [Matrix.mulVec, dotProduct, refinedVector, Algebra.smul_def]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    rw [he]
    exact hregular (.inr (i, p))
  · intro p
    apply coefficientPivot_regular_of_affine t p
    rw [seedRefinedEquation_eq_sum]
    exact hregular (.inl ((0 : Fin 3).succ, p))

end CycleQ2LiteralAbelJacobiChartRegular

end

#print axioms CycleQ2LiteralAbelJacobiChartRegular.exists_independent_chartRegular
