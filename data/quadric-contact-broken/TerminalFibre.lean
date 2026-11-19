import Proposal.ActiveHomogeneousClearing
import Proposal.TargetDenominator

noncomputable section
namespace QuadricContactClearing
open MvPolynomial

def fiberValues : Fin 6 → Polynomial ℂ := ![Polynomial.X, 1, 1, 0, 1, 2]
def fiber : BasePoly →+* Polynomial ℂ :=
  eval₂Hom (Polynomial.C.comp (Rat.castHom ℂ)) fiberValues

@[simp] theorem fiber_C (q : ℚ) : fiber (C q) = Polynomial.C (q : ℂ) := by
  simp [fiber]
@[simp] theorem fiber_X (i : Fin 6) : fiber (X i) = fiberValues i := by
  simp [fiber]

theorem fiber_ratioBase (N : BasePoly) : fiber (ratioBase N) = fiber N := by
  induction N using MvPolynomial.induction_on with
  | C r => simp [ratioBase]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp]
      refine congrArg (fiber p * ·) ?_
      simp only [ratioBase, eval₂Hom_X', fiber_X]
      fin_cases j <;>
        norm_num [ratioValues, fiberValues, fiber, Matrix.cons_val, Fin.isValue, map_ofNat] <;> rfl

@[simp] theorem fiber_ac : fiber ac = 1 := by
  simp only [ac, map_mul, fiber_X]
  change (1 : Polynomial ℂ) * 1 = 1
  ring

theorem fiber_final_denominator (N : BasePoly) :
    fiber ((X 1^2 * X 2^2) * N) = fiber N := by
  simp only [map_mul, map_pow, fiber_X]
  change (1 : Polynomial ℂ)^2 * 1^2 * fiber N = fiber N
  ring

/-- Identifies the simple rational-polynomial fibre with the protected
complex-polynomial univariate-specialization pipeline. -/
theorem fiber_eq_protected (N : BasePoly) :
    fiber N =
      (QuadricContactDenominator.toUni (map (Rat.castHom ℂ) N)).map
        QuadricContactDenominator.specialize := by
  induction N using MvPolynomial.induction_on with
  | C r =>
      simp only [fiber_C, map_C,
        QuadricContactDenominator.toUni_C, Polynomial.map_C]
      simp [QuadricContactDenominator.specialize]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, Polynomial.map_mul, hp, map_X]
      congr 1
      fin_cases j <;>
        simp [fiber_X, fiberValues, QuadricContactDenominator.toUni_X0,
          QuadricContactDenominator.toUni_X1, QuadricContactDenominator.toUni_X2,
          QuadricContactDenominator.toUni_X3, QuadricContactDenominator.toUni_X4,
          QuadricContactDenominator.toUni_X5,
          QuadricContactDenominator.specialize, QuadricContactDenominator.point,
          Matrix.cons_val, Fin.isValue] <;> exact (Polynomial.C_ofNat 2).symm

theorem HomogeneousDatum.fiber {p : Parameters} {n : ℕ} {H : BasePoly}
    (hp : HomogeneousDatum p n H) :
    fiber H = Polynomial.C (goodParameters p : ℂ) := by
  rw [← fiber_ratioBase, hp.ratioBase]
  simp only [map_mul, fiber_C, map_pow, fiber_ac, one_pow, mul_one]

theorem fiber_activeFibre (v : Fin 4 → BasePoly) (P : ActivePoly) :
    fiber (activeFibre v P) =
      eval₂Hom (Polynomial.C.comp ((Rat.castHom ℂ).comp
        (RegularSpecialization.specialize goodParameters))) (fun j => fiber (v j)) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [activeFibre]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp]
      simp only [activeFibre, eval₂Hom_X', fiber_ratioBase]

theorem fiber_cleared (v : Fin 4 → BasePoly) (P : ActivePoly)
    (Q : BasePoly) (κ : ℚ) (n : ℕ)
    (hQ : ratioBase Q = C κ * ac^n * activeFibre v P) :
    fiber ((X 1^2 * X 2^2) * Q) =
      Polynomial.C (κ : ℂ) *
      eval₂Hom (Polynomial.C.comp ((Rat.castHom ℂ).comp
        (RegularSpecialization.specialize goodParameters))) (fun j => fiber (v j)) P := by
  rw [fiber_final_denominator, ← fiber_ratioBase Q, hQ]
  simp only [map_mul, fiber_C, map_pow, fiber_ac, one_pow, mul_one, fiber_activeFibre]

end QuadricContactClearing

#print axioms QuadricContactClearing.fiber_eq_protected
