import Proposal.GeometricIncidenceChartDimension

/-!
# The chain rule for the actual shifted incidence charts

The affine coordinate named none is the original normal coordinate
X4 + X2^2 after Xi is set to one. The other three variables retain the
remaining weight-one coordinates. Their derivative matrix differs from
the retained four columns of the cone derivative matrix by an explicit
triangular column operation.

The identities below hold at every coefficient point and for every
polynomial. They compare the genuine dehomogenized Jacobian minors with
the normalized cone minors on these retained columns. Eliminating the
fifth cone column by weighted Euler is a separate step.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartDerivatives

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartMinor
  CycleQ2IncidenceChartDimension

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- The original geometric coordinate corresponding to an affine
variable before the triangular change of the normal coordinate. -/
def chartIndex (i : Fin 4) : Option (Fin 3) → Fin 5
  | none => Fin.last 4
  | some a => (i.succAbove a).castSucc

theorem chartIndex_injective (i : Fin 4) : Function.Injective (chartIndex i) := by
  fin_cases i <;> decide

theorem chartIndex_ne_self (i : Fin 4) (a : Option (Fin 3)) :
    chartIndex i a ≠ i.castSucc := by
  cases a with
  | none => fin_cases i <;> decide
  | some a => fin_cases i <;> fin_cases a <;> decide

theorem exists_chartIndex_of_ne (i : Fin 4) (j : Fin 5) (hj : j ≠ i.castSucc) :
    ∃ a : Option (Fin 3), chartIndex i a = j := by
  fin_cases i <;> fin_cases j
  all_goals first | exact (hj rfl).elim | decide

/-- The coefficient of the normal derivative in the triangular change. -/
def shiftDerivative (i : Fin 4) : Option (Fin 3) → ChartPolynomial S
  | none => 0
  | some a => pderiv (some a) (linearCoordinate i 2 ^ 2)

theorem pderiv_dehomogenize_X (i : Fin 4) (a : Option (Fin 3)) (j : Fin 5) :
    pderiv a (dehomogenize (S := S) i (X j)) =
      dehomogenize i (pderiv (chartIndex i a) (X j)) -
        shiftDerivative i a * dehomogenize i (pderiv (Fin.last 4) (X j)) := by
  have hnone (b : Fin 4) : pderiv none (linearCoordinate (S := S) i b) = 0 := by
    refine Fin.succAboveCases i ?_ (fun c => ?_) b <;> simp
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [dehomogenize_last]
    cases a with
    | none => simp [Pi.single_apply, chartIndex, shiftDerivative, pderiv_pow, hnone]
    | some a =>
      have hne : (4 : Fin 5) ≠ (i.succAbove a).castSucc :=
        (Fin.ne_of_lt (i.succAbove a).castSucc_lt_last).symm
      simp [Pi.single_apply, chartIndex, shiftDerivative, hne]
  · rw [dehomogenize_castSucc]
    refine Fin.succAboveCases i ?_ (fun b => ?_) j
    · cases a with
      | none =>
        have hne : i.castSucc ≠ (4 : Fin 5) := Fin.ne_of_lt i.castSucc_lt_last
        simp [Pi.single_apply, chartIndex, shiftDerivative, hne]
      | some a =>
        have hne : i.castSucc ≠ (i.succAbove a).castSucc := by
          exact fun h => Fin.succAbove_ne i a (Fin.castSucc_inj.mp h).symm
        have hlast : i.castSucc ≠ (4 : Fin 5) := Fin.ne_of_lt i.castSucc_lt_last
        simp [Pi.single_apply, chartIndex, shiftDerivative, hne, hlast]
    · cases a with
      | none =>
        have hne : (i.succAbove b).castSucc ≠ (4 : Fin 5) :=
          Fin.ne_of_lt (i.succAbove b).castSucc_lt_last
        simp [Pi.single_apply, chartIndex, shiftDerivative, hne]
      | some a =>
        have hne : (i.succAbove b).castSucc ≠ (4 : Fin 5) :=
          Fin.ne_of_lt (i.succAbove b).castSucc_lt_last
        simp [Pi.single_apply, chartIndex, shiftDerivative, hne]

/-- The polynomial chain rule includes the actual shift by X2^2. -/
theorem pderiv_dehomogenize (i : Fin 4) (a : Option (Fin 3))
    (p : MvPolynomial (Fin 5) S) :
    pderiv a (dehomogenize i p) =
      dehomogenize i (pderiv (chartIndex i a) p) -
        shiftDerivative i a * dehomogenize i (pderiv (Fin.last 4) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [dehomogenize, pderiv_C]
  | add p r hp hr =>
    simp only [map_add, hp, hr]
    ring
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, map_add, map_sub, hp, pderiv_dehomogenize_X]
    ring

theorem pderiv_dehomogenize_none (i : Fin 4) (p : MvPolynomial (Fin 5) S) :
    pderiv none (dehomogenize i p) = dehomogenize i (pderiv (Fin.last 4) p) := by
  simpa only [chartIndex, shiftDerivative, zero_mul, sub_zero] using
    pderiv_dehomogenize i none p

/-- The inverse triangular operation recovers each retained cone column. -/
theorem dehomogenize_pderiv_chartIndex (i : Fin 4) (a : Option (Fin 3))
    (p : MvPolynomial (Fin 5) S) :
    dehomogenize i (pderiv (chartIndex i a) p) =
      pderiv a (dehomogenize i p) +
        shiftDerivative i a * pderiv none (dehomogenize i p) := by
  have h := pderiv_dehomogenize i a p
  rw [← pderiv_dehomogenize_none i p] at h
  exact (eq_sub_iff_add_eq.mp h).symm

/-- Each normalized determinant on retained columns belongs to the
ideal generated by the actual four-variable Jacobian determinants. -/
theorem normalizedMinor_chartIndex (y : ParameterIndex → S) (i : Fin 4)
    (a b : Option (Fin 3)) :
    normalizedMinor y i (chartIndex i a) (chartIndex i b) =
      chartMinor y i ![a, b] +
        dehomogenizedMap y i (shiftDerivative i b) * chartMinor y i ![a, none] +
        dehomogenizedMap y i (shiftDerivative i a) * chartMinor y i ![none, b] := by
  simp only [normalizedMinor, surfaceMinor_eq, map_sub, map_mul,
    dehomogenize_pderiv_chartIndex, map_add, chartMinor, dehomogenizedEquations,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [map_sub, map_mul, pderiv_dehomogenize_none]
  ring

end CycleQ2IncidenceChartDerivatives

end

#print axioms CycleQ2IncidenceChartDerivatives.pderiv_dehomogenize
#print axioms CycleQ2IncidenceChartDerivatives.dehomogenize_pderiv_chartIndex
#print axioms CycleQ2IncidenceChartDerivatives.normalizedMinor_chartIndex
