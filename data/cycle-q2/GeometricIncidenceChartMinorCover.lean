import Proposal.GeometricIncidenceChartDerivatives
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Euler elimination compares the actual affine and cone Jacobian covers

On Xi = 1 the weight-one coefficient of the omitted cone column is one.
The weighted Euler identities for the original equations F and h, of
degrees six and three, vanish in the original surface chart quotient.
They eliminate that column from every normalized cone determinant.
The retained columns are compared with the genuine affine derivatives
by the previously proved triangular chain rule.

Consequently every normalized cone minor belongs to the ideal generated
by the actual four-variable Jacobian minors. Whenever a normalized cone
minor avoids an ideal, an injective pair of genuine affine derivative
columns also has its determinant outside the same ideal. No field,
prime-ideal, smoothness, or seed-specialization premise is needed.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartMinorCover

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceChartDimension CycleQ2IncidenceChartDerivatives

variable {S : Type} [CommRing S] [Algebra ℂ S]

def normalizedDerivative (y : ParameterIndex → S) (i : Fin 4)
    (e : Fin 2) (j : Fin 5) : DehomogenizedRing y i :=
  dehomogenizedMap y i (dehomogenize i (pderiv j (equations y e)))

def weightedCoordinate (y : ParameterIndex → S) (i : Fin 4)
    (j : Fin 5) : DehomogenizedRing y i :=
  (geometricWeight j : DehomogenizedRing y i) *
    dehomogenizedMap y i (dehomogenize i (X j))

theorem weightedCoordinate_self (y : ParameterIndex → S) (i : Fin 4) :
    weightedCoordinate y i i.castSucc = 1 := by
  simp only [weightedCoordinate, weight_castSucc, Nat.cast_one,
    dehomogenize_self, map_one, mul_one]

/-- Weighted Euler for either original equation vanishes in the actual
dehomogenized surface quotient. -/
theorem weighted_derivative_sum (y : ParameterIndex → S) (i : Fin 4) (e : Fin 2) :
    ∑ j : Fin 5, weightedCoordinate y i j * normalizedDerivative y i e j = 0 := by
  have he : (equations y e).IsWeightedHomogeneous geometricWeight
      ((![6, 3] : Fin 2 → ℕ) e) := by
    fin_cases e
    · exact pointEquationF_homogeneous y
    · exact pointEquationH_homogeneous y
  have hz : dehomogenizedMap y i (dehomogenize i (equations y e)) = 0 := by
    fin_cases e
    · exact dehomogenizedMap_equation y i 0
    · exact dehomogenizedMap_equation y i 1
  have h := congrArg (fun p => dehomogenizedMap y i (dehomogenize i p))
    he.sum_weight_X_mul_pderiv
  simpa only [map_sum, map_nsmul, map_mul, hz, nsmul_zero,
    normalizedDerivative, weightedCoordinate, nsmul_eq_mul, mul_assoc] using h

theorem normalizedMinor_eq_derivatives (y : ParameterIndex → S) (i : Fin 4)
    (j k : Fin 5) :
    normalizedMinor y i j k =
      normalizedDerivative y i 0 j * normalizedDerivative y i 1 k -
        normalizedDerivative y i 0 k * normalizedDerivative y i 1 j := by
  simp only [normalizedMinor, surfaceMinor_eq, normalizedDerivative,
    equations, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_sub, map_mul]

theorem normalizedMinor_self (y : ParameterIndex → S) (i : Fin 4) (j : Fin 5) :
    normalizedMinor y i j j = 0 := by
  rw [normalizedMinor_eq_derivatives, sub_self]

theorem normalizedMinor_swap (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    normalizedMinor y i j k = -normalizedMinor y i k j := by
  simp only [normalizedMinor_eq_derivatives]
  ring

/-- The weighted linear relation also annihilates every row of minors. -/
theorem weighted_minor_sum (y : ParameterIndex → S) (i : Fin 4) (k : Fin 5) :
    ∑ j : Fin 5, weightedCoordinate y i j * normalizedMinor y i j k = 0 := by
  simp only [normalizedMinor_eq_derivatives]
  calc
    _ = ∑ j : Fin 5,
        (weightedCoordinate y i j * normalizedDerivative y i 0 j) *
            normalizedDerivative y i 1 k -
          normalizedDerivative y i 0 k *
            (weightedCoordinate y i j * normalizedDerivative y i 1 j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j : Fin 5, weightedCoordinate y i j * normalizedDerivative y i 0 j) *
          normalizedDerivative y i 1 k -
        normalizedDerivative y i 0 k *
          (∑ j : Fin 5, weightedCoordinate y i j * normalizedDerivative y i 1 j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = 0 := by rw [weighted_derivative_sum, weighted_derivative_sum]; ring

def chartJacobianIdeal (y : ParameterIndex → S) (i : Fin 4) :
    Ideal (DehomogenizedRing y i) :=
  Ideal.span (Set.range (chartMinor y i))

theorem chartMinor_mem (y : ParameterIndex → S) (i : Fin 4)
    (q : Fin 2 → Option (Fin 3)) : chartMinor y i q ∈ chartJacobianIdeal y i :=
  Ideal.subset_span ⟨q, rfl⟩

theorem normalizedMinor_retained_mem (y : ParameterIndex → S) (i : Fin 4)
    (j k : Fin 5) (hj : j ≠ i.castSucc) (hk : k ≠ i.castSucc) :
    normalizedMinor y i j k ∈ chartJacobianIdeal y i := by
  obtain ⟨a, rfl⟩ := exists_chartIndex_of_ne i j hj
  obtain ⟨b, rfl⟩ := exists_chartIndex_of_ne i k hk
  rw [normalizedMinor_chartIndex]
  exact (chartJacobianIdeal y i).add_mem
    ((chartJacobianIdeal y i).add_mem (chartMinor_mem y i ![a, b])
      ((chartJacobianIdeal y i).mul_mem_left _ (chartMinor_mem y i ![a, none])))
    ((chartJacobianIdeal y i).mul_mem_left _ (chartMinor_mem y i ![none, b]))

theorem normalizedMinor_omitted_mem (y : ParameterIndex → S) (i : Fin 4)
    (k : Fin 5) (hk : k ≠ i.castSucc) :
    normalizedMinor y i i.castSucc k ∈ chartJacobianIdeal y i := by
  let r : DehomogenizedRing y i :=
    ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i.castSucc,
      weightedCoordinate y i j * normalizedMinor y i j k
  have hr : r ∈ chartJacobianIdeal y i := by
    apply (chartJacobianIdeal y i).sum_mem
    intro j hj
    exact (chartJacobianIdeal y i).mul_mem_left _
      (normalizedMinor_retained_mem y i j k (Finset.mem_erase.mp hj).1 hk)
  have hsum : normalizedMinor y i i.castSucc k + r = 0 := by
    have h := (Finset.add_sum_erase (Finset.univ : Finset (Fin 5))
      (fun j => weightedCoordinate y i j * normalizedMinor y i j k)
      (Finset.mem_univ i.castSucc)).trans (weighted_minor_sum y i k)
    simpa only [weightedCoordinate_self, one_mul] using h
  have heq : normalizedMinor y i i.castSucc k = -r := by
    calc
      _ = (normalizedMinor y i i.castSucc k + r) - r := by ring
      _ = -r := by rw [hsum, zero_sub]
  rw [heq]
  exact (chartJacobianIdeal y i).neg_mem hr

/-- Every original normalized cone minor lies in the genuine affine
Jacobian ideal, including minors using the omitted coordinate. -/
theorem normalizedMinor_mem_chartJacobianIdeal (y : ParameterIndex → S) (i : Fin 4)
    (j k : Fin 5) : normalizedMinor y i j k ∈ chartJacobianIdeal y i := by
  by_cases hj : j = i.castSucc
  · subst j
    by_cases hk : k = i.castSucc
    · subst k
      rw [normalizedMinor_self]
      exact (chartJacobianIdeal y i).zero_mem
    · exact normalizedMinor_omitted_mem y i k hk
  · by_cases hk : k = i.castSucc
    · subst k
      rw [normalizedMinor_swap]
      exact (chartJacobianIdeal y i).neg_mem (normalizedMinor_omitted_mem y i j hj)
    · exact normalizedMinor_retained_mem y i j k hj hk

/-- A determinant escaping any ideal supplies a genuine two-column
Jacobian patch of relative dimension two. -/
theorem exists_chartMinor_not_mem (y : ParameterIndex → S) (i : Fin 4)
    (P : Ideal (DehomogenizedRing y i)) (j k : Fin 5)
    (h : normalizedMinor y i j k ∉ P) :
    ∃ (q : Fin 2 → Option (Fin 3)) (hq : Function.Injective q),
      chartMinor y i q ∉ P := by
  classical
  have hex : ∃ q : Fin 2 → Option (Fin 3), chartMinor y i q ∉ P := by
    by_contra hn
    push_neg at hn
    have hle : chartJacobianIdeal y i ≤ P := by
      apply Ideal.span_le.mpr
      rintro a ⟨q, rfl⟩
      exact hn q
    exact h (hle (normalizedMinor_mem_chartJacobianIdeal y i j k))
  obtain ⟨q, hq⟩ := hex
  have hne : q 0 ≠ q 1 := by
    intro he
    apply hq
    have hz : chartMinor y i q = 0 := by
      simp only [chartMinor, he, sub_self, map_zero]
    rw [hz]
    exact P.zero_mem
  have hi : Function.Injective q := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  exact ⟨q, hi, hq⟩

end CycleQ2IncidenceChartMinorCover

end

#print axioms CycleQ2IncidenceChartMinorCover.weighted_derivative_sum
#print axioms CycleQ2IncidenceChartMinorCover.normalizedMinor_mem_chartJacobianIdeal
#print axioms CycleQ2IncidenceChartMinorCover.exists_chartMinor_not_mem
