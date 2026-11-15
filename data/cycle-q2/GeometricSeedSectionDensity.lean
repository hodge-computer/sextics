import Proposal.GeometricSeedSectionIdealComparison
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Set.Finite.Lattice

/-!
# The original regular section parameters meet every principal open

The earlier associated-prime argument chooses one regular vector.  Here
the same actual regularity conditions can be imposed together with any
nonzero polynomial condition on the three section parameters.  This is
the algebraic density statement needed to intersect the regular-section
conditions with a later smooth-section open; no smoothness assertion is
assumed or deduced in this file.

The proof moves along an affine line in one already regular direction.
Each associated-prime obstruction excludes at most one scalar, while a
nonzero polynomial on the line has only finitely many roots.

Source-only draft: no Lean compilation or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md for
attribution and the unchanged protected exactness obligation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2RegularSectionDensity

universe u v w

variable {k : Type u} [Field k]

/-- A line in a direction outside a subspace meets it at most once. -/
theorem finite_bad_scalars {V : Type v} [AddCommGroup V] [Module k V]
    (W : Submodule k V) (v w : V) (hv : v ∉ W) :
    Set.Finite {a : k | w + a • v ∈ W} := by
  apply Set.Subsingleton.finite
  intro a ha b hb
  by_contra hab
  have hmem : (a - b) • v ∈ W := by
    simpa only [sub_smul, add_sub_add_left_eq_sub] using W.sub_mem ha hb
  have hmul := W.smul_mem (a - b)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] at hmul
  exact hv hmul

/-- Restriction of an actual multivariate polynomial to an affine line. -/
def linePolynomial {σ : Type v} (P : MvPolynomial σ k) (w v : σ → k) :
    Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun j => Polynomial.C (w j) + Polynomial.C (v j) * Polynomial.X) P

theorem linePolynomial_eval {σ : Type v} (P : MvPolynomial σ k)
    (w v : σ → k) (a : k) :
    (linePolynomial P w v).eval a = MvPolynomial.eval (w + a • v) P := by
  change (Polynomial.evalRingHom a)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun j => Polynomial.C (w j) + Polynomial.C (v j) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id k := by
    ext c
    simp
  rw [hC]
  apply congrArg (fun z : σ → k => MvPolynomial.eval₂Hom (RingHom.id k) z P)
  funext j
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Avoid finitely many subspaces and a prescribed polynomial zero set,
using one direction already outside every subspace. -/
theorem exists_avoiding_polynomial [Infinite k]
    {ι : Type v} [Finite ι] {σ : Type w}
    (bad : ι → Submodule k (σ → k)) (v : σ → k)
    (hv : ∀ i, v ∉ bad i) (P : MvPolynomial σ k) (hP : P ≠ 0) :
    ∃ t : σ → k, MvPolynomial.eval t P ≠ 0 ∧ ∀ i, t ∉ bad i := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : σ → k, MvPolynomial.eval w P ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.funext
    intro w
    simpa using h w
  let Q := linePolynomial P w v
  have hQ : Q ≠ 0 := by
    intro h
    apply hw
    calc
      MvPolynomial.eval w P = Q.eval 0 := by
        simpa only [Q, zero_smul, add_zero] using
          (linePolynomial_eval P w v 0).symm
      _ = 0 := by rw [h]; simp
  let forbidden : Set k :=
    (⋃ i, {a : k | w + a • v ∈ bad i}) ∪ {a : k | Q.IsRoot a}
  have hfinite : forbidden.Finite :=
    (Set.finite_iUnion (fun i => finite_bad_scalars (bad i) v w (hv i))).union
      (Polynomial.finite_setOfPred_isRoot hQ)
  obtain ⟨a, ha⟩ := hfinite.exists_notMem
  refine ⟨w + a • v, ?_, ?_⟩
  · intro hz
    apply ha
    right
    change Q.eval a = 0
    rw [show Q = linePolynomial P w v from rfl, linePolynomial_eval]
    exact hz
  · intro i hi
    apply ha
    left
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

open CycleQ2SimultaneousRegularSection

/-- Simultaneous regularity can be required inside every nonempty
principal open of the original three-dimensional coefficient space. -/
theorem exists_nonzero_simultaneous_regular_avoiding_polynomial [Infinite k]
    {ι : Type v} [Finite ι] (R : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    [∀ i, IsNoetherianRing (R i)] (c : ∀ i, Fin 3 → R i)
    (hunit : ∀ i, ∃ j, IsUnit (c i j))
    (P : MvPolynomial (Fin 3) k) (hP : P ≠ 0) :
    ∃ t : Fin 3 → k, MvPolynomial.eval t P ≠ 0 ∧ t ≠ 0 ∧
      ∀ i, IsSMulRegular (R i) (∑ j, t j • c i j) := by
  classical
  obtain ⟨v, hv, hreg⟩ := exists_nonzero_simultaneous_regular R c hunit
  letI : Fintype ι := Fintype.ofFinite ι
  letI : ∀ i, Fintype (associatedPrimes (R i) (R i)) :=
    fun i => (associatedPrimes.finite (R i) (R i)).fintype
  let Index := Σ i : ι, associatedPrimes (R i) (R i)
  let bad : Option Index → Subspace k (Fin 3 → k) := fun a =>
    match a with
    | none => ⊥
    | some a =>
      (a.2.val.restrictScalars k).comap (coefficientCombination (c a.1))
  have hvbad (a : Option Index) : v ∉ bad a := by
    cases a with
    | none => simpa only [bad, Submodule.mem_bot] using hv
    | some a =>
      intro hm
      have hmem : (∑ j, v j • c a.1 j) ∈
          ⋃ p ∈ associatedPrimes (R a.1) (R a.1), (p : Set (R a.1)) :=
        Set.mem_iUnion.mpr ⟨a.2.val,
          Set.mem_iUnion.mpr ⟨a.2.property, hm⟩⟩
      rw [biUnion_associatedPrimes_eq_compl_regular (R a.1) (R a.1)] at hmem
      exact hmem (hreg a.1)
  obtain ⟨t, htP, ht⟩ := exists_avoiding_polynomial bad v hvbad P hP
  refine ⟨t, htP, ?_, ?_⟩
  · simpa only [bad, Submodule.mem_bot] using ht none
  · intro i
    by_contra hregular
    have hmem : (∑ j, t j • c i j) ∈
        ⋃ p ∈ associatedPrimes (R i) (R i), (p : Set (R i)) := by
      rw [biUnion_associatedPrimes_eq_compl_regular (R i) (R i)]
      exact hregular
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hp, hpt⟩ := Set.mem_iUnion.mp hp
    exact ht (some ⟨i, ⟨p, hp⟩⟩) hpt

end CycleQ2RegularSectionDensity

namespace CycleQ2SeedSectionDensity

open CategoryTheory AlgebraicGeometry Matrix
open scoped DualNumber
open CycleQ2SeedSectionIdealComparison CycleQ2SeedSectionInverse
  CycleQ2FirstOrderCurveChartFlat CycleQ2FirstOrderCurvePivotCover
  CycleQ2FirstOrderCurveCharts CycleQ2FirstOrderCurve
  CycleQ2FirstOrderCurveSeedFiber CycleQ2SpecializedProjectiveCurve
  CycleQ2SeedSectionNonempty CycleQ2IncidencePolynomialJacobianBinding

attribute [local instance] CycleQ2IncidenceFirstOrder.firstOrderAlgebra

/-- The actual 63 regularity conditions meet any nonzero polynomial
condition; no independent section vector is substituted. -/
theorem exists_one_vector_regular_in_principal_open
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ t : Fin 3 → ℂ, MvPolynomial.eval t P ≠ 0 ∧ t ≠ 0 ∧
      (∀ (i : Fin 4) (p : Pivot),
        IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p)) ∧
      (∀ (i : Fin 3) (p : Pivot), IsSMulRegular (LinkageRefinement i p)
        (((refinedFactorData i p).matrix *ᵥ refinedVector t i p) p.1)) := by
  obtain ⟨t, htP, ht, hreg⟩ :=
    CycleQ2RegularSectionDensity.exists_nonzero_simultaneous_regular_avoiding_polynomial
      (k := ℂ) RegularityRing regularityCoefficient regularityCoefficient_hasUnit P hP
  refine ⟨t, htP, ht, ?_, ?_⟩
  · intro i p
    rw [seedRefinedEquation_eq_sum]
    exact hreg (.inl (i, p))
  · intro i p
    have h := hreg (.inr (i, p))
    change IsSMulRegular (LinkageRefinement i p)
      (∑ j, t j • (refinedFactorData i p).matrix p.1 j) at h
    have he : ((refinedFactorData i p).matrix *ᵥ refinedVector t i p) p.1 =
        ∑ j, t j • (refinedFactorData i p).matrix p.1 j := by
      simp only [Matrix.mulVec, dotProduct, refinedVector, Algebra.smul_def]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    rw [he]
    exact h

/-- CLOSED SOURCE-LEVEL ENDPOINT: the original proper flat nonempty
first-order curve and its original local ideal maps can use one parameter
inside any prescribed nonempty principal open. Smoothness of such an
open, and the global geometric trace, remain separate constructions. -/
theorem exists_nonempty_flat_curve_in_principal_open
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ∃ t : Fin 3 → ℂ, MvPolynomial.eval t P ≠ 0 ∧ t ≠ 0 ∧
      AlgebraicGeometry.Flat (firstOrderCurveToBase t) ∧
      AlgebraicGeometry.IsProper (firstOrderCurveToBase t) ∧
      Nonempty (specializedCurve
        (seedPoint (57 : ℂ) Complex.I) t ≅ FirstOrderCurveSeedFiber t) ∧
      Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t) ∧
      Nonempty (FirstOrderCurveSeedFiber t) ∧
      (∀ (i : Fin 4) (p : Pivot),
        IsSMulRegular (SeedRefinement i p) (seedRefinedEquation t i p)) ∧
      ∀ (i : Fin 3) (p : Pivot),
        IsSMulRegular (LinkageRefinement i p)
          (((refinedFactorData i p).matrix *ᵥ refinedVector t i p) p.1) ∧
        ∃ e : (refinedFactorData i p).leftIdeal ≃ₗ[LinkageRefinement i p]
            rowIdeal (refinedFactorData i p) (refinedVector t i p),
          ∀ x, (e x : LinkageRefinement i p) =
            sectionFunctional (refinedFactorData i p) (refinedVector t i p) x := by
  obtain ⟨t, htP, ht, hfirst, hlinkage⟩ :=
    exists_one_vector_regular_in_principal_open P hP
  have hflat (i : Fin 4) :
      Module.Flat (DualNumber ℂ) (CycleQ2FirstOrderChartReduction.FirstOrderCurveChart t i) :=
    curveChart_flat_of_refined t i (fun p => refinedCurveChart_flat t i p (hfirst i p))
  let e := firstOrderCurveSeedFiberIso t
  obtain ⟨x⟩ := seed_specializedCurve_nonempty t
  refine ⟨t, htP, ht, firstOrderCurveToBase_flat_of_affineCharts t hflat,
    firstOrderCurveToBase_proper t, ⟨e⟩, ⟨x⟩, ⟨e.hom x⟩, hfirst, ?_⟩
  intro i p
  exact ⟨hlinkage i p,
    sectionIdealEquiv (refinedFactorData i p) (refinedVector t i p)
      p.1 (hlinkage i p), fun x => rfl⟩

end CycleQ2SeedSectionDensity

end

#print axioms CycleQ2RegularSectionDensity.exists_avoiding_polynomial
#print axioms CycleQ2RegularSectionDensity.exists_nonzero_simultaneous_regular_avoiding_polynomial
#print axioms CycleQ2SeedSectionDensity.exists_nonempty_flat_curve_in_principal_open
