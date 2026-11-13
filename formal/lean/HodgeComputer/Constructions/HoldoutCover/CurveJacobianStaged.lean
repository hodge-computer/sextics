import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Source component: CurveJacobianStaged -/
section
/-! Exact polynomial left-inverse certificates for the holdout conic Jacobian.
These intermediate lemmas do not assert a Hodge certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable section
namespace HoldoutConicJacobian
variable {K : Type*} [Field K]



def evenFactor (r : K) : K :=
  16*r^11 - 80*r^10 + 96*r^9 + 144*r^8 - 380*r^7 + 240*r^6 + 84*r^5 - 178*r^4 + 63*r^3 + 9*r^2 - 8*r + 1

def evenRaw (r z : K) : K :=
  z*(64*r^13 - 16*r^12*z^2 - 56*r^12 - 48*r^11*z^2 - 336*r^11 + 16*r^10*z^4 + 336*r^10*z^2 + 264*r^10 - 64*r^9*z^4 - 416*r^9*z^2 + 444*r^9 + 88*r^8*z^4 + 184*r^8*z^2 - 382*r^8 - 96*r^7*z^4 - 316*r^7*z^2 - 148*r^7 + 192*r^6*z^4 + 382*r^6*z^2 + 130*r^6 - 228*r^5*z^4 + 104*r^5*z^2 + 35*r^5 + 60*r^4*z^4 - 326*r^4*z^2 - 9*r^4 + 72*r^3*z^4 + 94*r^3*z^2 - 17*r^3 - 40*r^2*z^4 + 39*r^2*z^2 + 5*r^2 - 4*r*z^4 - 18*r*z^2 + 4*z^4 + z^2)


theorem even_raw_eq (r z : K)
    (hz : (r-1)*z^2 = r*(r^2+r-1)) :
    evenRaw r z = -r*(r-1)*z*evenFactor r := by
  have hc : evenRaw r z + r*(r-1)*z*evenFactor r =
      ((r-1)*z^2-r*(r^2+r-1))*(z*(-80*r^10 + 16*r^9*z^2 + 232*r^9 - 48*r^8*z^2 - 152*r^8 + 40*r^7*z^2 + 72*r^7 - 56*r^6*z^2 - 144*r^6 + 136*r^5*z^2 - 22*r^5 - 92*r^4*z^2 + 182*r^4 - 32*r^3*z^2 - 72*r^3 + 40*r^2*z^2 - 22*r^2 + 13*r - 4*z^2 - 1)) := by
    unfold evenRaw evenFactor
    ring
  rw [hz, sub_self, zero_mul] at hc
  linear_combination hc

#check even_raw_eq


private def evenMinor3 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![r*z - z, 2*r^2*z - 2*z, 2*r^2 - 1;
     r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor3_det (r z : K) : Matrix.det (evenMinor3 r z) = z*(-8*r^8 + 4*r^7*z^2 - 12*r^7 - 4*r^6*z^2 + 6*r^6 + 4*r^5*z^2 + 28*r^5 - 4*r^4*z^2 - 11*r^4 - 12*r^3*z^2 - 7*r^3 + 12*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r - 4*z^2 + 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor4 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor4_det (r z : K) : Matrix.det (evenMinor4 r z) = -r*(-4*r^8 + 4*r^7*z^2 - 16*r^7 - 4*r^6*z^2 - 8*r^6 - 2*r^5*z^2 + 20*r^5 + 32*r^4*z^2 + 15*r^4 - 48*r^3*z^2 - 8*r^3 - 2*r^2*z^2 - 7*r^2 + 32*r*z^2 + r - 12*z^2 + 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor4, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor5 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2*z - 2*z;
     r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1;
     r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z]

private theorem evenMinor5_det (r z : K) : Matrix.det (evenMinor5 r z) = z*(-2*r^9 + 2*r^8*z^2 - 8*r^8 - 4*r^7*z^2 - 3*r^7 + 12*r^6*z^2 + 3*r^6 - 18*r^5*z^2 + 17*r^5 + 18*r^4*z^2 - 18*r^4 - 16*r^3*z^2 + 15*r^3 - 11*r^2 + 10*r*z^2 + 3*r - 4*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor5, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor2 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2*z - 2*z, 2*r^2 - 1;
     r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     r*z - z, r^3 + r^2 - r, 0, 2*r*z - 2*z]

private theorem evenMinor2_det (r z : K) : Matrix.det (evenMinor2 r z) = 4*r^12 - 4*r^11*z^2 + 20*r^11 - 4*r^10*z^2 + 20*r^10 + 4*r^9*z^4 + 6*r^9*z^2 - 28*r^9 - 16*r^8*z^4 - 20*r^8*z^2 - 43*r^8 + 40*r^7*z^4 + 8*r^7*z^2 + 13*r^7 - 68*r^6*z^4 + 88*r^6*z^2 + 30*r^6 + 80*r^5*z^4 - 109*r^5*z^2 - 2*r^5 - 60*r^4*z^4 + 40*r^4*z^2 - 9*r^4 + 8*r^3*z^4 - 18*r^3*z^2 + 28*r^2*z^4 + 21*r^2*z^2 + r^2 - 20*r*z^4 - 9*r*z^2 + 4*z^4 + z^2 := by

  have h0 : (evenMinor2 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (0 : Fin 4)) =
      evenMinor3 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h1 : (evenMinor2 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (1 : Fin 4)) =
      evenMinor4 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenMinor2 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      evenMinor5 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor2 r z) =
      ∑ j : Fin 4, (-1 : K)^(3+j.val)*(evenMinor2 r z) 3 j *
        (![z*(-8*r^8 + 4*r^7*z^2 - 12*r^7 - 4*r^6*z^2 + 6*r^6 + 4*r^5*z^2 + 28*r^5 - 4*r^4*z^2 - 11*r^4 - 12*r^3*z^2 - 7*r^3 + 12*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r - 4*z^2 + 1), -r*(-4*r^8 + 4*r^7*z^2 - 16*r^7 - 4*r^6*z^2 - 8*r^6 - 2*r^5*z^2 + 20*r^5 + 32*r^4*z^2 + 15*r^4 - 48*r^3*z^2 - 8*r^3 - 2*r^2*z^2 - 7*r^2 + 32*r*z^2 + r - 12*z^2 + 1), 0, z*(-2*r^9 + 2*r^8*z^2 - 8*r^8 - 4*r^7*z^2 - 3*r^7 + 12*r^6*z^2 + 3*r^6 - 18*r^5*z^2 + 17*r^5 + 18*r^4*z^2 - 18*r^4 - 16*r^3*z^2 + 15*r^3 - 11*r^2 + 10*r*z^2 + 3*r - 4*z^2)] j) := by
    rw [Matrix.det_succ_row _ (3 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^3*(r*z - z)*
          Matrix.det ((evenMinor2 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (0 : Fin 4))) = (-1 : K)^3*(r*z - z)*(z*(-8*r^8 + 4*r^7*z^2 - 12*r^7 - 4*r^6*z^2 + 6*r^6 + 4*r^5*z^2 + 28*r^5 - 4*r^4*z^2 - 11*r^4 - 12*r^3*z^2 - 7*r^3 + 12*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r - 4*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^3*(r*z - z)*d)
        ((congrArg Matrix.det h0).trans (evenMinor3_det r z))

    · change (-1 : K)^4*(r^3 + r^2 - r)*
          Matrix.det ((evenMinor2 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (1 : Fin 4))) = (-1 : K)^4*(r^3 + r^2 - r)*(-r*(-4*r^8 + 4*r^7*z^2 - 16*r^7 - 4*r^6*z^2 - 8*r^6 - 2*r^5*z^2 + 20*r^5 + 32*r^4*z^2 + 15*r^4 - 48*r^3*z^2 - 8*r^3 - 2*r^2*z^2 - 7*r^2 + 32*r*z^2 + r - 12*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^4*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h1).trans (evenMinor4_det r z))

    · simp [evenMinor2]

    · change (-1 : K)^6*(2*r*z - 2*z)*
          Matrix.det ((evenMinor2 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^6*(2*r*z - 2*z)*(z*(-2*r^9 + 2*r^8*z^2 - 8*r^8 - 4*r^7*z^2 - 3*r^7 + 12*r^6*z^2 + 3*r^6 - 18*r^5*z^2 + 17*r^5 + 18*r^4*z^2 - 18*r^4 - 16*r^3*z^2 + 15*r^3 - 11*r^2 + 10*r*z^2 + 3*r - 4*z^2))
      exact congrArg (fun d : K => (-1 : K)^6*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h3).trans (evenMinor5_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^3*(r*z - z)*(z*(-8*r^8 + 4*r^7*z^2 - 12*r^7 - 4*r^6*z^2 + 6*r^6 + 4*r^5*z^2 + 28*r^5 - 4*r^4*z^2 - 11*r^4 - 12*r^3*z^2 - 7*r^3 + 12*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r - 4*z^2 + 1))+((-1 : K)^4*(r^3 + r^2 - r)*(-r*(-4*r^8 + 4*r^7*z^2 - 16*r^7 - 4*r^6*z^2 - 8*r^6 - 2*r^5*z^2 + 20*r^5 + 32*r^4*z^2 + 15*r^4 - 48*r^3*z^2 - 8*r^3 - 2*r^2*z^2 - 7*r^2 + 32*r*z^2 + r - 12*z^2 + 1))+((-1 : K)^5*(0)*(0)+((-1 : K)^6*(2*r*z - 2*z)*(z*(-2*r^9 + 2*r^8*z^2 - 8*r^8 - 4*r^7*z^2 - 3*r^7 + 12*r^6*z^2 + 3*r^6 - 18*r^5*z^2 + 17*r^5 + 18*r^4*z^2 - 18*r^4 - 16*r^3*z^2 + 15*r^3 - 11*r^2 + 10*r*z^2 + 3*r - 4*z^2))+0)))) = 4*r^12 - 4*r^11*z^2 + 20*r^11 - 4*r^10*z^2 + 20*r^10 + 4*r^9*z^4 + 6*r^9*z^2 - 28*r^9 - 16*r^8*z^4 - 20*r^8*z^2 - 43*r^8 + 40*r^7*z^4 + 8*r^7*z^2 + 13*r^7 - 68*r^6*z^4 + 88*r^6*z^2 + 30*r^6 + 80*r^5*z^4 - 109*r^5*z^2 - 2*r^5 - 60*r^4*z^4 + 40*r^4*z^2 - 9*r^4 + 8*r^3*z^4 - 18*r^3*z^2 + 28*r^2*z^4 + 21*r^2*z^2 + r^2 - 20*r*z^4 - 9*r*z^2 + 4*z^4 + z^2
  norm_num
  ring

private def evenMinor7 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor7_det (r z : K) : Matrix.det (evenMinor7 r z) = -3*r*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 8*z^2 - 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor7, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor8 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, r*z - z, 2*r^2*z - 2*z;
     6*r*z - 3*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1;
     0, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z]

private theorem evenMinor8_det (r z : K) : Matrix.det (evenMinor8 r z) = 3*z*(2*r - 1)*(-2*r^7 + 2*r^5*z^2 - r^5 - 2*r^4*z^2 + 2*r^4 + 4*r^3*z^2 - 4*r^3 - 4*r^2*z^2 + 5*r^2 - 2*r*z^2 - 2*r + 2*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor8, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor6 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![6*r^2 - 3*r, r*z - z, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, r^3 + r^2 - r, 0, 2*r*z - 2*z]

private theorem evenMinor6_det (r z : K) : Matrix.det (evenMinor6 r z) = 3*(2*r - 1)*(4*r^10 + 12*r^9 - 8*r^8*z^2 + 4*r^8 - 8*r^7*z^2 - 16*r^7 + 4*r^6*z^4 + 8*r^6*z^2 - 11*r^6 - 8*r^5*z^4 + 34*r^5*z^2 + 7*r^5 + 12*r^4*z^4 - 28*r^4*z^2 + 6*r^4 - 16*r^3*z^4 + 4*r^3*z^2 - r^3 + 4*r^2*z^4 - 6*r^2*z^2 - r^2 + 8*r*z^4 + 4*r*z^2 - 4*z^4) := by

  have h1 : (evenMinor6 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (1 : Fin 4)) =
      evenMinor7 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenMinor6 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      evenMinor8 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor6 r z) =
      ∑ j : Fin 4, (-1 : K)^(3+j.val)*(evenMinor6 r z) 3 j *
        (![0, -3*r*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 8*z^2 - 1), 0, 3*z*(2*r - 1)*(-2*r^7 + 2*r^5*z^2 - r^5 - 2*r^4*z^2 + 2*r^4 + 4*r^3*z^2 - 4*r^3 - 4*r^2*z^2 + 5*r^2 - 2*r*z^2 - 2*r + 2*z^2)] j) := by
    rw [Matrix.det_succ_row _ (3 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [evenMinor6]

    · change (-1 : K)^4*(r^3 + r^2 - r)*
          Matrix.det ((evenMinor6 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (1 : Fin 4))) = (-1 : K)^4*(r^3 + r^2 - r)*(-3*r*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 8*z^2 - 1))
      exact congrArg (fun d : K => (-1 : K)^4*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h1).trans (evenMinor7_det r z))

    · simp [evenMinor6]

    · change (-1 : K)^6*(2*r*z - 2*z)*
          Matrix.det ((evenMinor6 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^6*(2*r*z - 2*z)*(3*z*(2*r - 1)*(-2*r^7 + 2*r^5*z^2 - r^5 - 2*r^4*z^2 + 2*r^4 + 4*r^3*z^2 - 4*r^3 - 4*r^2*z^2 + 5*r^2 - 2*r*z^2 - 2*r + 2*z^2))
      exact congrArg (fun d : K => (-1 : K)^6*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h3).trans (evenMinor8_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^3*(0)*(0)+((-1 : K)^4*(r^3 + r^2 - r)*(-3*r*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 8*z^2 - 1))+((-1 : K)^5*(0)*(0)+((-1 : K)^6*(2*r*z - 2*z)*(3*z*(2*r - 1)*(-2*r^7 + 2*r^5*z^2 - r^5 - 2*r^4*z^2 + 2*r^4 + 4*r^3*z^2 - 4*r^3 - 4*r^2*z^2 + 5*r^2 - 2*r*z^2 - 2*r + 2*z^2))+0)))) = 3*(2*r - 1)*(4*r^10 + 12*r^9 - 8*r^8*z^2 + 4*r^8 - 8*r^7*z^2 - 16*r^7 + 4*r^6*z^4 + 8*r^6*z^2 - 11*r^6 - 8*r^5*z^4 + 34*r^5*z^2 + 7*r^5 + 12*r^4*z^4 - 28*r^4*z^2 + 6*r^4 - 16*r^3*z^4 + 4*r^3*z^2 - r^3 + 4*r^2*z^4 - 6*r^2*z^2 - r^2 + 8*r*z^4 + 4*r*z^2 - 4*z^4)
  norm_num
  ring

private def evenMinor10 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, r*z - z, 2*r^2 - 1;
     6*r*z - 3*z, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z;
     0, r^3 + r^2 - r, 2*r*z - 2*z]

private theorem evenMinor10_det (r z : K) : Matrix.det (evenMinor10 r z) = -3*z*(2*r - 1)*(2*r^6 - 2*r^5 - 10*r^4 + 11*r^3 + 2*r^2*z^2 - r^2 - 4*r*z^2 - r + 2*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor10, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor11 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, r^3 + 3*r^2 - 2*r, 2*r^2 - 1;
     6*r*z - 3*z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z;
     0, r*z - z, 2*r*z - 2*z]

private theorem evenMinor11_det (r z : K) : Matrix.det (evenMinor11 r z) = 3*z^2*(r - 1)*(2*r - 1)*(2*r^4 - 6*r^3 + 2*r^2 + 2*r - 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor11, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor12 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, r^3 + 3*r^2 - 2*r, r*z - z;
     6*r*z - 3*z, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r;
     0, r*z - z, r^3 + r^2 - r]

private theorem evenMinor12_det (r z : K) : Matrix.det (evenMinor12 r z) = 3*z*(2*r - 1)*(r^7 - r^6 - 4*r^5 + 5*r^3 + r^2*z^2 - 2*r^2 - 2*r*z^2 + z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor12, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor9 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![6*r^2 - 3*r, r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2 - 1;
     6*r*z - 3*z, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z;
     0, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, r*z - z, r^3 + r^2 - r, 2*r*z - 2*z]

private theorem evenMinor9_det (r z : K) : Matrix.det (evenMinor9 r z) = 3*z*(2*r - 1)*(-2*r^10 + 2*r^9 + 2*r^8*z^2 + 11*r^8 - 10*r^7*z^2 - 6*r^7 + 22*r^6*z^2 - 12*r^6 - 36*r^5*z^2 + 10*r^5 + 37*r^4*z^2 - 4*r^4 - 13*r^3*z^2 + 3*r^3 - 7*r^2*z^2 - r^2 + 6*r*z^2 - z^2) := by

  have h1 : (evenMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (1 : Fin 4)) =
      evenMinor10 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (evenMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      evenMinor11 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      evenMinor12 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor9 r z) =
      ∑ j : Fin 4, (-1 : K)^(2+j.val)*(evenMinor9 r z) 2 j *
        (![0, -3*z*(2*r - 1)*(2*r^6 - 2*r^5 - 10*r^4 + 11*r^3 + 2*r^2*z^2 - r^2 - 4*r*z^2 - r + 2*z^2), 3*z^2*(r - 1)*(2*r - 1)*(2*r^4 - 6*r^3 + 2*r^2 + 2*r - 1), 3*z*(2*r - 1)*(r^7 - r^6 - 4*r^5 + 5*r^3 + r^2*z^2 - 2*r^2 - 2*r*z^2 + z^2)] j) := by
    rw [Matrix.det_succ_row _ (2 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [evenMinor9]

    · change (-1 : K)^3*(r^3 + r^2 - r)*
          Matrix.det ((evenMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (1 : Fin 4))) = (-1 : K)^3*(r^3 + r^2 - r)*(-3*z*(2*r - 1)*(2*r^6 - 2*r^5 - 10*r^4 + 11*r^3 + 2*r^2*z^2 - r^2 - 4*r*z^2 - r + 2*z^2))
      exact congrArg (fun d : K => (-1 : K)^3*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h1).trans (evenMinor10_det r z))

    · change (-1 : K)^4*(r^3*z - r^2*z + 3*r*z - 2*z)*
          Matrix.det ((evenMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^4*(r^3*z - r^2*z + 3*r*z - 2*z)*(3*z^2*(r - 1)*(2*r - 1)*(2*r^4 - 6*r^3 + 2*r^2 + 2*r - 1))
      exact congrArg (fun d : K => (-1 : K)^4*(r^3*z - r^2*z + 3*r*z - 2*z)*d)
        ((congrArg Matrix.det h2).trans (evenMinor11_det r z))

    · change (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*
          Matrix.det ((evenMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(3*z*(2*r - 1)*(r^7 - r^6 - 4*r^5 + 5*r^3 + r^2*z^2 - 2*r^2 - 2*r*z^2 + z^2))
      exact congrArg (fun d : K => (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*d)
        ((congrArg Matrix.det h3).trans (evenMinor12_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^2*(0)*(0)+((-1 : K)^3*(r^3 + r^2 - r)*(-3*z*(2*r - 1)*(2*r^6 - 2*r^5 - 10*r^4 + 11*r^3 + 2*r^2*z^2 - r^2 - 4*r*z^2 - r + 2*z^2))+((-1 : K)^4*(r^3*z - r^2*z + 3*r*z - 2*z)*(3*z^2*(r - 1)*(2*r - 1)*(2*r^4 - 6*r^3 + 2*r^2 + 2*r - 1))+((-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(3*z*(2*r - 1)*(r^7 - r^6 - 4*r^5 + 5*r^3 + r^2*z^2 - 2*r^2 - 2*r*z^2 + z^2))+0)))) = 3*z*(2*r - 1)*(-2*r^10 + 2*r^9 + 2*r^8*z^2 + 11*r^8 - 10*r^7*z^2 - 6*r^7 + 22*r^6*z^2 - 12*r^6 - 36*r^5*z^2 + 10*r^5 + 37*r^4*z^2 - 4*r^4 - 13*r^3*z^2 + 3*r^3 - 7*r^2*z^2 - r^2 + 6*r*z^2 - z^2)
  norm_num
  ring

private def evenMinor1 (r z : K) : Matrix (Fin 5) (Fin 5) K :=
  !![2*r*z - 2*z, r*z - z, 0, 2*r^2 - 1, 0;
     6*r^2 - 3*r, r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, r*z - z, r^3 + r^2 - r, 0, 2*r*z - 2*z]

private theorem evenMinor1_det (r z : K) : Matrix.det (evenMinor1 r z) = z*(32*r^13 - 8*r^12*z^2 - 28*r^12 - 24*r^11*z^2 - 168*r^11 + 8*r^10*z^4 + 200*r^10*z^2 + 132*r^10 - 40*r^9*z^4 - 388*r^9*z^2 + 234*r^9 + 88*r^8*z^4 + 458*r^8*z^2 - 239*r^8 - 132*r^7*z^4 - 446*r^7*z^2 - 5*r^7 + 140*r^6*z^4 + 152*r^6*z^2 + 32*r^6 - 52*r^5*z^4 + 256*r^5*z^2 + r^5 - 68*r^4*z^4 - 263*r^4*z^2 + 21*r^4 + 76*r^3*z^4 + 33*r^3*z^2 - 19*r^3 - 12*r^2*z^4 + 45*r^2*z^2 + 4*r^2 - 12*r*z^4 - 16*r*z^2 + 4*z^4 + z^2) := by

  have h0 : (evenMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      evenMinor2 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h1 : (evenMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      evenMinor6 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      evenMinor9 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor1 r z) =
      ∑ j : Fin 5, (-1 : K)^(0+j.val)*(evenMinor1 r z) 0 j *
        (![4*r^12 - 4*r^11*z^2 + 20*r^11 - 4*r^10*z^2 + 20*r^10 + 4*r^9*z^4 + 6*r^9*z^2 - 28*r^9 - 16*r^8*z^4 - 20*r^8*z^2 - 43*r^8 + 40*r^7*z^4 + 8*r^7*z^2 + 13*r^7 - 68*r^6*z^4 + 88*r^6*z^2 + 30*r^6 + 80*r^5*z^4 - 109*r^5*z^2 - 2*r^5 - 60*r^4*z^4 + 40*r^4*z^2 - 9*r^4 + 8*r^3*z^4 - 18*r^3*z^2 + 28*r^2*z^4 + 21*r^2*z^2 + r^2 - 20*r*z^4 - 9*r*z^2 + 4*z^4 + z^2, 3*(2*r - 1)*(4*r^10 + 12*r^9 - 8*r^8*z^2 + 4*r^8 - 8*r^7*z^2 - 16*r^7 + 4*r^6*z^4 + 8*r^6*z^2 - 11*r^6 - 8*r^5*z^4 + 34*r^5*z^2 + 7*r^5 + 12*r^4*z^4 - 28*r^4*z^2 + 6*r^4 - 16*r^3*z^4 + 4*r^3*z^2 - r^3 + 4*r^2*z^4 - 6*r^2*z^2 - r^2 + 8*r*z^4 + 4*r*z^2 - 4*z^4), 0, 3*z*(2*r - 1)*(-2*r^10 + 2*r^9 + 2*r^8*z^2 + 11*r^8 - 10*r^7*z^2 - 6*r^7 + 22*r^6*z^2 - 12*r^6 - 36*r^5*z^2 + 10*r^5 + 37*r^4*z^2 - 4*r^4 - 13*r^3*z^2 + 3*r^3 - 7*r^2*z^2 - r^2 + 6*r*z^2 - z^2), 0] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 5)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^0*(2*r*z - 2*z)*
          Matrix.det ((evenMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (0 : Fin 5))) = (-1 : K)^0*(2*r*z - 2*z)*(4*r^12 - 4*r^11*z^2 + 20*r^11 - 4*r^10*z^2 + 20*r^10 + 4*r^9*z^4 + 6*r^9*z^2 - 28*r^9 - 16*r^8*z^4 - 20*r^8*z^2 - 43*r^8 + 40*r^7*z^4 + 8*r^7*z^2 + 13*r^7 - 68*r^6*z^4 + 88*r^6*z^2 + 30*r^6 + 80*r^5*z^4 - 109*r^5*z^2 - 2*r^5 - 60*r^4*z^4 + 40*r^4*z^2 - 9*r^4 + 8*r^3*z^4 - 18*r^3*z^2 + 28*r^2*z^4 + 21*r^2*z^2 + r^2 - 20*r*z^4 - 9*r*z^2 + 4*z^4 + z^2)
      exact congrArg (fun d : K => (-1 : K)^0*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h0).trans (evenMinor2_det r z))

    · change (-1 : K)^1*(r*z - z)*
          Matrix.det ((evenMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (1 : Fin 5))) = (-1 : K)^1*(r*z - z)*(3*(2*r - 1)*(4*r^10 + 12*r^9 - 8*r^8*z^2 + 4*r^8 - 8*r^7*z^2 - 16*r^7 + 4*r^6*z^4 + 8*r^6*z^2 - 11*r^6 - 8*r^5*z^4 + 34*r^5*z^2 + 7*r^5 + 12*r^4*z^4 - 28*r^4*z^2 + 6*r^4 - 16*r^3*z^4 + 4*r^3*z^2 - r^3 + 4*r^2*z^4 - 6*r^2*z^2 - r^2 + 8*r*z^4 + 4*r*z^2 - 4*z^4))
      exact congrArg (fun d : K => (-1 : K)^1*(r*z - z)*d)
        ((congrArg Matrix.det h1).trans (evenMinor6_det r z))

    · simp [evenMinor1]

    · change (-1 : K)^3*(2*r^2 - 1)*
          Matrix.det ((evenMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (3 : Fin 5))) = (-1 : K)^3*(2*r^2 - 1)*(3*z*(2*r - 1)*(-2*r^10 + 2*r^9 + 2*r^8*z^2 + 11*r^8 - 10*r^7*z^2 - 6*r^7 + 22*r^6*z^2 - 12*r^6 - 36*r^5*z^2 + 10*r^5 + 37*r^4*z^2 - 4*r^4 - 13*r^3*z^2 + 3*r^3 - 7*r^2*z^2 - r^2 + 6*r*z^2 - z^2))
      exact congrArg (fun d : K => (-1 : K)^3*(2*r^2 - 1)*d)
        ((congrArg Matrix.det h3).trans (evenMinor9_det r z))

    · simp [evenMinor1]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(2*r*z - 2*z)*(4*r^12 - 4*r^11*z^2 + 20*r^11 - 4*r^10*z^2 + 20*r^10 + 4*r^9*z^4 + 6*r^9*z^2 - 28*r^9 - 16*r^8*z^4 - 20*r^8*z^2 - 43*r^8 + 40*r^7*z^4 + 8*r^7*z^2 + 13*r^7 - 68*r^6*z^4 + 88*r^6*z^2 + 30*r^6 + 80*r^5*z^4 - 109*r^5*z^2 - 2*r^5 - 60*r^4*z^4 + 40*r^4*z^2 - 9*r^4 + 8*r^3*z^4 - 18*r^3*z^2 + 28*r^2*z^4 + 21*r^2*z^2 + r^2 - 20*r*z^4 - 9*r*z^2 + 4*z^4 + z^2)+((-1 : K)^1*(r*z - z)*(3*(2*r - 1)*(4*r^10 + 12*r^9 - 8*r^8*z^2 + 4*r^8 - 8*r^7*z^2 - 16*r^7 + 4*r^6*z^4 + 8*r^6*z^2 - 11*r^6 - 8*r^5*z^4 + 34*r^5*z^2 + 7*r^5 + 12*r^4*z^4 - 28*r^4*z^2 + 6*r^4 - 16*r^3*z^4 + 4*r^3*z^2 - r^3 + 4*r^2*z^4 - 6*r^2*z^2 - r^2 + 8*r*z^4 + 4*r*z^2 - 4*z^4))+((-1 : K)^2*(0)*(0)+((-1 : K)^3*(2*r^2 - 1)*(3*z*(2*r - 1)*(-2*r^10 + 2*r^9 + 2*r^8*z^2 + 11*r^8 - 10*r^7*z^2 - 6*r^7 + 22*r^6*z^2 - 12*r^6 - 36*r^5*z^2 + 10*r^5 + 37*r^4*z^2 - 4*r^4 - 13*r^3*z^2 + 3*r^3 - 7*r^2*z^2 - r^2 + 6*r*z^2 - z^2))+((-1 : K)^4*(0)*(0)+0))))) = z*(32*r^13 - 8*r^12*z^2 - 28*r^12 - 24*r^11*z^2 - 168*r^11 + 8*r^10*z^4 + 200*r^10*z^2 + 132*r^10 - 40*r^9*z^4 - 388*r^9*z^2 + 234*r^9 + 88*r^8*z^4 + 458*r^8*z^2 - 239*r^8 - 132*r^7*z^4 - 446*r^7*z^2 - 5*r^7 + 140*r^6*z^4 + 152*r^6*z^2 + 32*r^6 - 52*r^5*z^4 + 256*r^5*z^2 + r^5 - 68*r^4*z^4 - 263*r^4*z^2 + 21*r^4 + 76*r^3*z^4 + 33*r^3*z^2 - 19*r^3 - 12*r^2*z^4 + 45*r^2*z^2 + 4*r^2 - 12*r*z^4 - 16*r*z^2 + 4*z^4 + z^2)
  norm_num
  ring

private def evenMinor15 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 2*r^2*z - 2*z, 2*r^2 - 1;
     -2*r^3 + 3*r^2 - r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     -2*r^2*z + 3*r*z - z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor15_det (r z : K) : Matrix.det (evenMinor15 r z) = -z*(r - 1)*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 6*r^4 + 6*r^3 - 8*r^2*z^2 - r + 4*z^2 - 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor15, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor16 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, 0, 2*r^2 - 1;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^2*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor16_det (r z : K) : Matrix.det (evenMinor16 r z) = 3*(r - 1)*(2*r - 1)^2*(-2*r^5 - 2*r^4 + 2*r^3*z^2 + r^3 - 2*r^2*z^2 + r^2 - 2*r*z^2 + z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor16, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor14 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![2*r*z - 2*z, 0, 2*r^2 - 1, 0;
     6*r^2 - 3*r, 0, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem evenMinor14_det (r z : K) : Matrix.det (evenMinor14 r z) = -(r - 1)*(2*r - 1)*(24*r^8 - 8*r^7*z^2 + 12*r^7 - 32*r^6*z^2 - 36*r^6 + 8*r^5*z^4 + 64*r^5*z^2 - 12*r^5 - 8*r^4*z^4 + 24*r^4*z^2 + 18*r^4 - 16*r^3*z^4 - 54*r^3*z^2 + 3*r^3 + 16*r^2*z^4 - 2*r^2*z^2 - 3*r^2 + 8*r*z^4 + 12*r*z^2 - 8*z^4 - z^2) := by

  have h0 : (evenMinor14 r z).submatrix
      (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (0 : Fin 4)) =
      evenMinor15 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (evenMinor14 r z).submatrix
      (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      evenMinor16 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor14 r z) =
      ∑ j : Fin 4, (-1 : K)^(0+j.val)*(evenMinor14 r z) 0 j *
        (![-z*(r - 1)*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 6*r^4 + 6*r^3 - 8*r^2*z^2 - r + 4*z^2 - 1), 0, 3*(r - 1)*(2*r - 1)^2*(-2*r^5 - 2*r^4 + 2*r^3*z^2 + r^3 - 2*r^2*z^2 + r^2 - 2*r*z^2 + z^2), 0] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^0*(2*r*z - 2*z)*
          Matrix.det ((evenMinor14 r z).submatrix (Fin.succAbove (0 : Fin 4))
            (Fin.succAbove (0 : Fin 4))) = (-1 : K)^0*(2*r*z - 2*z)*(-z*(r - 1)*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 6*r^4 + 6*r^3 - 8*r^2*z^2 - r + 4*z^2 - 1))
      exact congrArg (fun d : K => (-1 : K)^0*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h0).trans (evenMinor15_det r z))

    · simp [evenMinor14]

    · change (-1 : K)^2*(2*r^2 - 1)*
          Matrix.det ((evenMinor14 r z).submatrix (Fin.succAbove (0 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^2*(2*r^2 - 1)*(3*(r - 1)*(2*r - 1)^2*(-2*r^5 - 2*r^4 + 2*r^3*z^2 + r^3 - 2*r^2*z^2 + r^2 - 2*r*z^2 + z^2))
      exact congrArg (fun d : K => (-1 : K)^2*(2*r^2 - 1)*d)
        ((congrArg Matrix.det h2).trans (evenMinor16_det r z))

    · simp [evenMinor14]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(2*r*z - 2*z)*(-z*(r - 1)*(2*r - 1)*(-4*r^6 - 8*r^5 + 4*r^4*z^2 + 6*r^4 + 6*r^3 - 8*r^2*z^2 - r + 4*z^2 - 1))+((-1 : K)^1*(0)*(0)+((-1 : K)^2*(2*r^2 - 1)*(3*(r - 1)*(2*r - 1)^2*(-2*r^5 - 2*r^4 + 2*r^3*z^2 + r^3 - 2*r^2*z^2 + r^2 - 2*r*z^2 + z^2))+((-1 : K)^3*(0)*(0)+0)))) = -(r - 1)*(2*r - 1)*(24*r^8 - 8*r^7*z^2 + 12*r^7 - 32*r^6*z^2 - 36*r^6 + 8*r^5*z^4 + 64*r^5*z^2 - 12*r^5 - 8*r^4*z^4 + 24*r^4*z^2 + 18*r^4 - 16*r^3*z^4 - 54*r^3*z^2 + 3*r^3 + 16*r^2*z^4 - 2*r^2*z^2 - 3*r^2 + 8*r*z^4 + 12*r*z^2 - 8*z^4 - z^2)
  norm_num
  ring

private def evenMinor18 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z;
     -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r*z - 2*z]

private theorem evenMinor18_det (r z : K) : Matrix.det (evenMinor18 r z) = z*(r - 1)*(2*r - 1)*(-4*r^6 + 2*r^5*z^2 - 8*r^5 - 2*r^4*z^2 + 7*r^4 + 4*r^3*z^2 - 2*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 4*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor18, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor19 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, 0, 2*r^2*z - 2*z;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^3 + 2*r^2 - r - 1;
     0, -2*r^2*z + 3*r*z - z, 2*r*z - 2*z]

private theorem evenMinor19_det (r z : K) : Matrix.det (evenMinor19 r z) = -3*z*(r - 1)*(2*r - 1)^2*(-2*r^4 + 2*r^2*z^2 - r^2 + r - 2*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor19, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor20 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r^2 - 3*r, 0, r^3 + 3*r^2 - 2*r;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, r^3 + r^2 - r]

private theorem evenMinor20_det (r z : K) : Matrix.det (evenMinor20 r z) = 3*r^3*(r - 1)*(2*r - 1)^2*(-r^2 + r*z^2 - r - 2*z^2 + 1) := by

  rw [Matrix.det_fin_three]
  simp only [evenMinor20, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def evenMinor17 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![2*r*z - 2*z, 0, r*z - z, 2*r^2 - 1;
     6*r^2 - 3*r, 0, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r*z - 2*z]

private theorem evenMinor17_det (r z : K) : Matrix.det (evenMinor17 r z) = (r - 1)*(2*r - 1)*(12*r^8 - 20*r^7*z^2 + 6*r^7 + 4*r^6*z^4 + 34*r^6*z^2 - 24*r^6 - 8*r^5*z^4 + 6*r^5*z^2 + 3*r^5 - 17*r^4*z^2 + 9*r^4 + 6*r^3*z^4 - 3*r^3*z^2 - 3*r^3 - 2*r^2*z^4 + 2*r^2*z^2 + 2*r*z^4 + r*z^2 - 2*z^4) := by

  have h0 : (evenMinor17 r z).submatrix
      (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (0 : Fin 4)) =
      evenMinor18 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (evenMinor17 r z).submatrix
      (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      evenMinor19 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenMinor17 r z).submatrix
      (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      evenMinor20 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor17 r z) =
      ∑ j : Fin 4, (-1 : K)^(0+j.val)*(evenMinor17 r z) 0 j *
        (![z*(r - 1)*(2*r - 1)*(-4*r^6 + 2*r^5*z^2 - 8*r^5 - 2*r^4*z^2 + 7*r^4 + 4*r^3*z^2 - 2*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 4*z^2), 0, -3*z*(r - 1)*(2*r - 1)^2*(-2*r^4 + 2*r^2*z^2 - r^2 + r - 2*z^2), 3*r^3*(r - 1)*(2*r - 1)^2*(-r^2 + r*z^2 - r - 2*z^2 + 1)] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^0*(2*r*z - 2*z)*
          Matrix.det ((evenMinor17 r z).submatrix (Fin.succAbove (0 : Fin 4))
            (Fin.succAbove (0 : Fin 4))) = (-1 : K)^0*(2*r*z - 2*z)*(z*(r - 1)*(2*r - 1)*(-4*r^6 + 2*r^5*z^2 - 8*r^5 - 2*r^4*z^2 + 7*r^4 + 4*r^3*z^2 - 2*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 4*z^2))
      exact congrArg (fun d : K => (-1 : K)^0*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h0).trans (evenMinor18_det r z))

    · simp [evenMinor17]

    · change (-1 : K)^2*(r*z - z)*
          Matrix.det ((evenMinor17 r z).submatrix (Fin.succAbove (0 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^2*(r*z - z)*(-3*z*(r - 1)*(2*r - 1)^2*(-2*r^4 + 2*r^2*z^2 - r^2 + r - 2*z^2))
      exact congrArg (fun d : K => (-1 : K)^2*(r*z - z)*d)
        ((congrArg Matrix.det h2).trans (evenMinor19_det r z))

    · change (-1 : K)^3*(2*r^2 - 1)*
          Matrix.det ((evenMinor17 r z).submatrix (Fin.succAbove (0 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^3*(2*r^2 - 1)*(3*r^3*(r - 1)*(2*r - 1)^2*(-r^2 + r*z^2 - r - 2*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^3*(2*r^2 - 1)*d)
        ((congrArg Matrix.det h3).trans (evenMinor20_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(2*r*z - 2*z)*(z*(r - 1)*(2*r - 1)*(-4*r^6 + 2*r^5*z^2 - 8*r^5 - 2*r^4*z^2 + 7*r^4 + 4*r^3*z^2 - 2*r^2*z^2 + 3*r^2 - 6*r*z^2 - 2*r + 4*z^2))+((-1 : K)^1*(0)*(0)+((-1 : K)^2*(r*z - z)*(-3*z*(r - 1)*(2*r - 1)^2*(-2*r^4 + 2*r^2*z^2 - r^2 + r - 2*z^2))+((-1 : K)^3*(2*r^2 - 1)*(3*r^3*(r - 1)*(2*r - 1)^2*(-r^2 + r*z^2 - r - 2*z^2 + 1))+0)))) = (r - 1)*(2*r - 1)*(12*r^8 - 20*r^7*z^2 + 6*r^7 + 4*r^6*z^4 + 34*r^6*z^2 - 24*r^6 - 8*r^5*z^4 + 6*r^5*z^2 + 3*r^5 - 17*r^4*z^2 + 9*r^4 + 6*r^3*z^4 - 3*r^3*z^2 - 3*r^3 - 2*r^2*z^4 + 2*r^2*z^2 + 2*r*z^4 + r*z^2 - 2*z^4)
  norm_num
  ring

private def evenMinor13 (r z : K) : Matrix (Fin 5) (Fin 5) K :=
  !![2*r*z - 2*z, 0, r*z - z, 2*r^2 - 1, 0;
     6*r^2 - 3*r, 0, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, 0, r*z - z, 0, 2*r*z - 2*z]

private theorem evenMinor13_det (r z : K) : Matrix.det (evenMinor13 r z) = z*(r - 1)^2*(2*r - 1)*(-32*r^7*z^2 + 8*r^6*z^4 + 100*r^6*z^2 - 12*r^6 - 24*r^5*z^4 - 52*r^5*z^2 + 18*r^5 + 8*r^4*z^4 - 58*r^4*z^2 + 28*r^3*z^4 + 48*r^3*z^2 - 9*r^3 - 20*r^2*z^4 + 6*r^2*z^2 + 3*r^2 - 4*r*z^4 - 10*r*z^2 + 4*z^4 + z^2) := by

  have h2 : (evenMinor13 r z).submatrix
      (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      evenMinor14 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h4 : (evenMinor13 r z).submatrix
      (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      evenMinor17 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenMinor13 r z) =
      ∑ j : Fin 5, (-1 : K)^(4+j.val)*(evenMinor13 r z) 4 j *
        (![0, 0, -(r - 1)*(2*r - 1)*(24*r^8 - 8*r^7*z^2 + 12*r^7 - 32*r^6*z^2 - 36*r^6 + 8*r^5*z^4 + 64*r^5*z^2 - 12*r^5 - 8*r^4*z^4 + 24*r^4*z^2 + 18*r^4 - 16*r^3*z^4 - 54*r^3*z^2 + 3*r^3 + 16*r^2*z^4 - 2*r^2*z^2 - 3*r^2 + 8*r*z^4 + 12*r*z^2 - 8*z^4 - z^2), 0, (r - 1)*(2*r - 1)*(12*r^8 - 20*r^7*z^2 + 6*r^7 + 4*r^6*z^4 + 34*r^6*z^2 - 24*r^6 - 8*r^5*z^4 + 6*r^5*z^2 + 3*r^5 - 17*r^4*z^2 + 9*r^4 + 6*r^3*z^4 - 3*r^3*z^2 - 3*r^3 - 2*r^2*z^4 + 2*r^2*z^2 + 2*r*z^4 + r*z^2 - 2*z^4)] j) := by
    rw [Matrix.det_succ_row _ (4 : Fin 5)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [evenMinor13]

    · simp [evenMinor13]

    · change (-1 : K)^6*(r*z - z)*
          Matrix.det ((evenMinor13 r z).submatrix (Fin.succAbove (4 : Fin 5))
            (Fin.succAbove (2 : Fin 5))) = (-1 : K)^6*(r*z - z)*(-(r - 1)*(2*r - 1)*(24*r^8 - 8*r^7*z^2 + 12*r^7 - 32*r^6*z^2 - 36*r^6 + 8*r^5*z^4 + 64*r^5*z^2 - 12*r^5 - 8*r^4*z^4 + 24*r^4*z^2 + 18*r^4 - 16*r^3*z^4 - 54*r^3*z^2 + 3*r^3 + 16*r^2*z^4 - 2*r^2*z^2 - 3*r^2 + 8*r*z^4 + 12*r*z^2 - 8*z^4 - z^2))
      exact congrArg (fun d : K => (-1 : K)^6*(r*z - z)*d)
        ((congrArg Matrix.det h2).trans (evenMinor14_det r z))

    · simp [evenMinor13]

    · change (-1 : K)^8*(2*r*z - 2*z)*
          Matrix.det ((evenMinor13 r z).submatrix (Fin.succAbove (4 : Fin 5))
            (Fin.succAbove (4 : Fin 5))) = (-1 : K)^8*(2*r*z - 2*z)*((r - 1)*(2*r - 1)*(12*r^8 - 20*r^7*z^2 + 6*r^7 + 4*r^6*z^4 + 34*r^6*z^2 - 24*r^6 - 8*r^5*z^4 + 6*r^5*z^2 + 3*r^5 - 17*r^4*z^2 + 9*r^4 + 6*r^3*z^4 - 3*r^3*z^2 - 3*r^3 - 2*r^2*z^4 + 2*r^2*z^2 + 2*r*z^4 + r*z^2 - 2*z^4))
      exact congrArg (fun d : K => (-1 : K)^8*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h4).trans (evenMinor17_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^4*(0)*(0)+((-1 : K)^5*(0)*(0)+((-1 : K)^6*(r*z - z)*(-(r - 1)*(2*r - 1)*(24*r^8 - 8*r^7*z^2 + 12*r^7 - 32*r^6*z^2 - 36*r^6 + 8*r^5*z^4 + 64*r^5*z^2 - 12*r^5 - 8*r^4*z^4 + 24*r^4*z^2 + 18*r^4 - 16*r^3*z^4 - 54*r^3*z^2 + 3*r^3 + 16*r^2*z^4 - 2*r^2*z^2 - 3*r^2 + 8*r*z^4 + 12*r*z^2 - 8*z^4 - z^2))+((-1 : K)^7*(0)*(0)+((-1 : K)^8*(2*r*z - 2*z)*((r - 1)*(2*r - 1)*(12*r^8 - 20*r^7*z^2 + 6*r^7 + 4*r^6*z^4 + 34*r^6*z^2 - 24*r^6 - 8*r^5*z^4 + 6*r^5*z^2 + 3*r^5 - 17*r^4*z^2 + 9*r^4 + 6*r^3*z^4 - 3*r^3*z^2 - 3*r^3 - 2*r^2*z^4 + 2*r^2*z^2 + 2*r*z^4 + r*z^2 - 2*z^4))+0))))) = z*(r - 1)^2*(2*r - 1)*(-32*r^7*z^2 + 8*r^6*z^4 + 100*r^6*z^2 - 12*r^6 - 24*r^5*z^4 - 52*r^5*z^2 + 18*r^5 + 8*r^4*z^4 - 58*r^4*z^2 + 28*r^3*z^4 + 48*r^3*z^2 - 9*r^3 - 20*r^2*z^4 + 6*r^2*z^2 + 3*r^2 - 4*r*z^4 - 10*r*z^2 + 4*z^4 + z^2)
  norm_num
  ring

def evenCore (r z : K) : Matrix (Fin 6) (Fin 6) K :=
  !![2*r*z - 2*z, 0, r*z - z, 0, 2*r^2 - 1, 0;
     6*r^2 - 3*r, 0, r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2*z - 2*z, 2*r^2 - 1;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, 0, r*z - z, r^3 + r^2 - r, 0, 2*r*z - 2*z;
     0, 2, 0, 1, 0, 0]

theorem evenCore_det (r z : K) : Matrix.det (evenCore r z) = z*(64*r^13 - 16*r^12*z^2 - 56*r^12 - 48*r^11*z^2 - 336*r^11 + 16*r^10*z^4 + 336*r^10*z^2 + 264*r^10 - 64*r^9*z^4 - 416*r^9*z^2 + 444*r^9 + 88*r^8*z^4 + 184*r^8*z^2 - 382*r^8 - 96*r^7*z^4 - 316*r^7*z^2 - 148*r^7 + 192*r^6*z^4 + 382*r^6*z^2 + 130*r^6 - 228*r^5*z^4 + 104*r^5*z^2 + 35*r^5 + 60*r^4*z^4 - 326*r^4*z^2 - 9*r^4 + 72*r^3*z^4 + 94*r^3*z^2 - 17*r^3 - 40*r^2*z^4 + 39*r^2*z^2 + 5*r^2 - 4*r*z^4 - 18*r*z^2 + 4*z^4 + z^2) := by

  have h1 : (evenCore r z).submatrix
      (Fin.succAbove (5 : Fin 6)) (Fin.succAbove (1 : Fin 6)) =
      evenMinor1 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (evenCore r z).submatrix
      (Fin.succAbove (5 : Fin 6)) (Fin.succAbove (3 : Fin 6)) =
      evenMinor13 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (evenCore r z) =
      ∑ j : Fin 6, (-1 : K)^(5+j.val)*(evenCore r z) 5 j *
        (![0, z*(32*r^13 - 8*r^12*z^2 - 28*r^12 - 24*r^11*z^2 - 168*r^11 + 8*r^10*z^4 + 200*r^10*z^2 + 132*r^10 - 40*r^9*z^4 - 388*r^9*z^2 + 234*r^9 + 88*r^8*z^4 + 458*r^8*z^2 - 239*r^8 - 132*r^7*z^4 - 446*r^7*z^2 - 5*r^7 + 140*r^6*z^4 + 152*r^6*z^2 + 32*r^6 - 52*r^5*z^4 + 256*r^5*z^2 + r^5 - 68*r^4*z^4 - 263*r^4*z^2 + 21*r^4 + 76*r^3*z^4 + 33*r^3*z^2 - 19*r^3 - 12*r^2*z^4 + 45*r^2*z^2 + 4*r^2 - 12*r*z^4 - 16*r*z^2 + 4*z^4 + z^2), 0, z*(r - 1)^2*(2*r - 1)*(-32*r^7*z^2 + 8*r^6*z^4 + 100*r^6*z^2 - 12*r^6 - 24*r^5*z^4 - 52*r^5*z^2 + 18*r^5 + 8*r^4*z^4 - 58*r^4*z^2 + 28*r^3*z^4 + 48*r^3*z^2 - 9*r^3 - 20*r^2*z^4 + 6*r^2*z^2 + 3*r^2 - 4*r*z^4 - 10*r*z^2 + 4*z^4 + z^2), 0, 0] j) := by
    rw [Matrix.det_succ_row _ (5 : Fin 6)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [evenCore]

    · change (-1 : K)^6*(2)*
          Matrix.det ((evenCore r z).submatrix (Fin.succAbove (5 : Fin 6))
            (Fin.succAbove (1 : Fin 6))) = (-1 : K)^6*(2)*(z*(32*r^13 - 8*r^12*z^2 - 28*r^12 - 24*r^11*z^2 - 168*r^11 + 8*r^10*z^4 + 200*r^10*z^2 + 132*r^10 - 40*r^9*z^4 - 388*r^9*z^2 + 234*r^9 + 88*r^8*z^4 + 458*r^8*z^2 - 239*r^8 - 132*r^7*z^4 - 446*r^7*z^2 - 5*r^7 + 140*r^6*z^4 + 152*r^6*z^2 + 32*r^6 - 52*r^5*z^4 + 256*r^5*z^2 + r^5 - 68*r^4*z^4 - 263*r^4*z^2 + 21*r^4 + 76*r^3*z^4 + 33*r^3*z^2 - 19*r^3 - 12*r^2*z^4 + 45*r^2*z^2 + 4*r^2 - 12*r*z^4 - 16*r*z^2 + 4*z^4 + z^2))
      exact congrArg (fun d : K => (-1 : K)^6*(2)*d)
        ((congrArg Matrix.det h1).trans (evenMinor1_det r z))

    · simp [evenCore]

    · change (-1 : K)^8*(1)*
          Matrix.det ((evenCore r z).submatrix (Fin.succAbove (5 : Fin 6))
            (Fin.succAbove (3 : Fin 6))) = (-1 : K)^8*(1)*(z*(r - 1)^2*(2*r - 1)*(-32*r^7*z^2 + 8*r^6*z^4 + 100*r^6*z^2 - 12*r^6 - 24*r^5*z^4 - 52*r^5*z^2 + 18*r^5 + 8*r^4*z^4 - 58*r^4*z^2 + 28*r^3*z^4 + 48*r^3*z^2 - 9*r^3 - 20*r^2*z^4 + 6*r^2*z^2 + 3*r^2 - 4*r*z^4 - 10*r*z^2 + 4*z^4 + z^2))
      exact congrArg (fun d : K => (-1 : K)^8*(1)*d)
        ((congrArg Matrix.det h3).trans (evenMinor13_det r z))

    · simp [evenCore]

    · simp [evenCore]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^5*(0)*(0)+((-1 : K)^6*(2)*(z*(32*r^13 - 8*r^12*z^2 - 28*r^12 - 24*r^11*z^2 - 168*r^11 + 8*r^10*z^4 + 200*r^10*z^2 + 132*r^10 - 40*r^9*z^4 - 388*r^9*z^2 + 234*r^9 + 88*r^8*z^4 + 458*r^8*z^2 - 239*r^8 - 132*r^7*z^4 - 446*r^7*z^2 - 5*r^7 + 140*r^6*z^4 + 152*r^6*z^2 + 32*r^6 - 52*r^5*z^4 + 256*r^5*z^2 + r^5 - 68*r^4*z^4 - 263*r^4*z^2 + 21*r^4 + 76*r^3*z^4 + 33*r^3*z^2 - 19*r^3 - 12*r^2*z^4 + 45*r^2*z^2 + 4*r^2 - 12*r*z^4 - 16*r*z^2 + 4*z^4 + z^2))+((-1 : K)^7*(0)*(0)+((-1 : K)^8*(1)*(z*(r - 1)^2*(2*r - 1)*(-32*r^7*z^2 + 8*r^6*z^4 + 100*r^6*z^2 - 12*r^6 - 24*r^5*z^4 - 52*r^5*z^2 + 18*r^5 + 8*r^4*z^4 - 58*r^4*z^2 + 28*r^3*z^4 + 48*r^3*z^2 - 9*r^3 - 20*r^2*z^4 + 6*r^2*z^2 + 3*r^2 - 4*r*z^4 - 10*r*z^2 + 4*z^4 + z^2))+((-1 : K)^9*(0)*(0)+((-1 : K)^10*(0)*(0)+0)))))) = z*(64*r^13 - 16*r^12*z^2 - 56*r^12 - 48*r^11*z^2 - 336*r^11 + 16*r^10*z^4 + 336*r^10*z^2 + 264*r^10 - 64*r^9*z^4 - 416*r^9*z^2 + 444*r^9 + 88*r^8*z^4 + 184*r^8*z^2 - 382*r^8 - 96*r^7*z^4 - 316*r^7*z^2 - 148*r^7 + 192*r^6*z^4 + 382*r^6*z^2 + 130*r^6 - 228*r^5*z^4 + 104*r^5*z^2 + 35*r^5 + 60*r^4*z^4 - 326*r^4*z^2 - 9*r^4 + 72*r^3*z^4 + 94*r^3*z^2 - 17*r^3 - 40*r^2*z^4 + 39*r^2*z^2 + 5*r^2 - 4*r*z^4 - 18*r*z^2 + 4*z^4 + z^2)
  norm_num
  ring

theorem even_core_det (r z : K) :
    Matrix.det (evenCore r z) = evenRaw r z := by
  rw [evenCore_det]
  unfold evenRaw
  ring

#check even_core_det

def oddFactor (r : K) : K :=
  8*r^11 - 48*r^10 + 112*r^9 - 16*r^8 - 224*r^7 + 352*r^6 - 275*r^5 + 101*r^4 + 11*r^3 - 24*r^2 + 8*r - 1

def oddRaw (r z : K) : K :=
  16*r^12 + 48*r^11 - 16*r^10*z^2 - 32*r^10 - 56*r^9*z^2 - 148*r^9 + 224*r^8*z^2 + 52*r^8 + 32*r^7*z^4 - 132*r^7*z^2 + 156*r^7 - 152*r^6*z^4 - 132*r^6*z^2 - 74*r^6 + 248*r^5*z^4 + 36*r^5*z^2 - 45*r^5 - 136*r^4*z^4 + 158*r^4*z^2 + 29*r^4 - 36*r^3*z^4 - 84*r^3*z^2 - r^3 + 52*r^2*z^4 - 13*r^2*z^2 - r^2 - 4*r*z^4 + 12*r*z^2 - 4*z^4 - z^2


theorem odd_raw_eq (r z : K)
    (hz : (r-1)*z^2 = r*(r^2+r-1)) :
    (r-1)*oddRaw r z = -r*oddFactor r := by
  have hc : (r-1)*oddRaw r z + r*oddFactor r =
      ((r-1)*z^2-r*(r^2+r-1))*(-16*r^10 - 24*r^9 + 136*r^8 + 32*r^7*z^2 - 156*r^7 - 152*r^6*z^2 + 108*r^6 + 248*r^5*z^2 - 144*r^5 - 136*r^4*z^2 + 130*r^4 - 36*r^3*z^2 - 28*r^3 + 52*r^2*z^2 - 17*r^2 - 4*r*z^2 + 8*r - 4*z^2 - 1) := by
    unfold oddRaw oddFactor
    ring
  rw [hz, sub_self, zero_mul] at hc
  linear_combination hc

#check odd_raw_eq


private def oddMinor3 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, 2*r^2*z - 2*z, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     2, 0, 2]

private theorem oddMinor3_det (r z : K) : Matrix.det (oddMinor3 r z) = 2*(r + 1)*(-4*r^5 + 2*r^4 + 8*r^3*z^2 - 14*r^2*z^2 + r^2 + 4*r*z^2 + r + 2*z^2 - 1) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor4 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z;
     2, 1, 2]

private theorem oddMinor4_det (r z : K) : Matrix.det (oddMinor4 r z) = -z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor4, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor5 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z;
     -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     2, 1, 0]

private theorem oddMinor5_det (r z : K) : Matrix.det (oddMinor5 r z) = -(r + 1)*(-8*r^5 + 4*r^4*z^2 - 6*r^4 - 4*r^3*z^2 + 10*r^3 + 6*r^2*z^2 + 3*r^2 - 12*r*z^2 - 3*r + 6*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor5, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor2 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![-2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     2, 1, 0, 2]

private theorem oddMinor2_det (r z : K) : Matrix.det (oddMinor2 r z) = r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1) := by

  have h1 : (oddMinor2 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (1 : Fin 4)) =
      oddMinor3 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (oddMinor2 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      oddMinor4 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor2 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      oddMinor5 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor2 r z) =
      ∑ j : Fin 4, (-1 : K)^(2+j.val)*(oddMinor2 r z) 2 j *
        (![0, 2*(r + 1)*(-4*r^5 + 2*r^4 + 8*r^3*z^2 - 14*r^2*z^2 + r^2 + 4*r*z^2 + r + 2*z^2 - 1), -z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3), -(r + 1)*(-8*r^5 + 4*r^4*z^2 - 6*r^4 - 4*r^3*z^2 + 10*r^3 + 6*r^2*z^2 + 3*r^2 - 12*r*z^2 - 3*r + 6*z^2)] j) := by
    rw [Matrix.det_succ_row _ (2 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [oddMinor2]

    · change (-1 : K)^3*(r^3 + r^2 - r)*
          Matrix.det ((oddMinor2 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (1 : Fin 4))) = (-1 : K)^3*(r^3 + r^2 - r)*(2*(r + 1)*(-4*r^5 + 2*r^4 + 8*r^3*z^2 - 14*r^2*z^2 + r^2 + 4*r*z^2 + r + 2*z^2 - 1))
      exact congrArg (fun d : K => (-1 : K)^3*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h1).trans (oddMinor3_det r z))

    · change (-1 : K)^4*(2*r*z - 2*z)*
          Matrix.det ((oddMinor2 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^4*(2*r*z - 2*z)*(-z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3))
      exact congrArg (fun d : K => (-1 : K)^4*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h2).trans (oddMinor4_det r z))

    · change (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*
          Matrix.det ((oddMinor2 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-(r + 1)*(-8*r^5 + 4*r^4*z^2 - 6*r^4 - 4*r^3*z^2 + 10*r^3 + 6*r^2*z^2 + 3*r^2 - 12*r*z^2 - 3*r + 6*z^2))
      exact congrArg (fun d : K => (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor5_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^2*(0)*(0)+((-1 : K)^3*(r^3 + r^2 - r)*(2*(r + 1)*(-4*r^5 + 2*r^4 + 8*r^3*z^2 - 14*r^2*z^2 + r^2 + 4*r*z^2 + r + 2*z^2 - 1))+((-1 : K)^4*(2*r*z - 2*z)*(-z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3))+((-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-(r + 1)*(-8*r^5 + 4*r^4*z^2 - 6*r^4 - 4*r^3*z^2 + 10*r^3 + 6*r^2*z^2 + 3*r^2 - 12*r*z^2 - 3*r + 6*z^2))+0)))) = r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1)
  norm_num
  ring

private def oddMinor7 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z, 2*r^2 - 1;
     r^3 + r^2 - r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     r*z - z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1]

private theorem oddMinor7_det (r z : K) : Matrix.det (oddMinor7 r z) = -z*(-4*r^9 + 4*r^7 + 4*r^6*z^2 - 14*r^6 - 12*r^5*z^2 - 5*r^5 + 16*r^4*z^2 + 23*r^4 - 4*r^3*z^2 - 16*r^2*z^2 - 10*r^2 + 16*r*z^2 + r - 4*z^2 + 1) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor7, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor8 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r^3 + 2*r^2 - r - 1;
     0, r*z - z, 2*r*z - 2*z]

private theorem oddMinor8_det (r z : K) : Matrix.det (oddMinor8 r z) = z*(r - 1)^2*(2*r - 1)*(2*r^3*z^2 - 4*r^2*z^2 + r^2 + 6*r*z^2 - r - 2*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor8, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor6 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![-2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, r*z - z, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     2, 0, 0, 2]

private theorem oddMinor6_det (r z : K) : Matrix.det (oddMinor6 r z) = 2*z*(-4*r^9 + 4*r^7 + 8*r^6*z^2 - 14*r^6 - 30*r^5*z^2 - 3*r^5 + 56*r^4*z^2 + 16*r^4 - 56*r^3*z^2 + 9*r^3 + 22*r^2*z^2 - 15*r^2 + 2*r*z^2 + 2*r - 2*z^2 + 1) := by

  have h0 : (oddMinor6 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (0 : Fin 4)) =
      oddMinor7 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor6 r z).submatrix
      (Fin.succAbove (3 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      oddMinor8 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor6 r z) =
      ∑ j : Fin 4, (-1 : K)^(3+j.val)*(oddMinor6 r z) 3 j *
        (![-z*(-4*r^9 + 4*r^7 + 4*r^6*z^2 - 14*r^6 - 12*r^5*z^2 - 5*r^5 + 16*r^4*z^2 + 23*r^4 - 4*r^3*z^2 - 16*r^2*z^2 - 10*r^2 + 16*r*z^2 + r - 4*z^2 + 1), 0, 0, z*(r - 1)^2*(2*r - 1)*(2*r^3*z^2 - 4*r^2*z^2 + r^2 + 6*r*z^2 - r - 2*z^2)] j) := by
    rw [Matrix.det_succ_row _ (3 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^3*(2)*
          Matrix.det ((oddMinor6 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (0 : Fin 4))) = (-1 : K)^3*(2)*(-z*(-4*r^9 + 4*r^7 + 4*r^6*z^2 - 14*r^6 - 12*r^5*z^2 - 5*r^5 + 16*r^4*z^2 + 23*r^4 - 4*r^3*z^2 - 16*r^2*z^2 - 10*r^2 + 16*r*z^2 + r - 4*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^3*(2)*d)
        ((congrArg Matrix.det h0).trans (oddMinor7_det r z))

    · simp [oddMinor6]

    · simp [oddMinor6]

    · change (-1 : K)^6*(2)*
          Matrix.det ((oddMinor6 r z).submatrix (Fin.succAbove (3 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^6*(2)*(z*(r - 1)^2*(2*r - 1)*(2*r^3*z^2 - 4*r^2*z^2 + r^2 + 6*r*z^2 - r - 2*z^2))
      exact congrArg (fun d : K => (-1 : K)^6*(2)*d)
        ((congrArg Matrix.det h3).trans (oddMinor8_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^3*(2)*(-z*(-4*r^9 + 4*r^7 + 4*r^6*z^2 - 14*r^6 - 12*r^5*z^2 - 5*r^5 + 16*r^4*z^2 + 23*r^4 - 4*r^3*z^2 - 16*r^2*z^2 - 10*r^2 + 16*r*z^2 + r - 4*z^2 + 1))+((-1 : K)^4*(0)*(0)+((-1 : K)^5*(0)*(0)+((-1 : K)^6*(2)*(z*(r - 1)^2*(2*r - 1)*(2*r^3*z^2 - 4*r^2*z^2 + r^2 + 6*r*z^2 - r - 2*z^2))+0)))) = 2*z*(-4*r^9 + 4*r^7 + 8*r^6*z^2 - 14*r^6 - 30*r^5*z^2 - 3*r^5 + 56*r^4*z^2 + 16*r^4 - 56*r^3*z^2 + 9*r^3 + 22*r^2*z^2 - 15*r^2 + 2*r*z^2 + 2*r - 2*z^2 + 1)
  norm_num
  ring

private def oddMinor10 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, 2*r^2*z - 2*z;
     2, 0, 2]

private theorem oddMinor10_det (r z : K) : Matrix.det (oddMinor10 r z) = 2*(-2*r^6 + 4*r^5*z^2 - r^5 - 7*r^4*z^2 + 2*r^4 + 14*r^3*z^2 - r^3 - 16*r^2*z^2 + 2*r^2 + 3*r*z^2 - r + 2*z^2) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor10, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor11 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z;
     2, 0, 1]

private theorem oddMinor11_det (r z : K) : Matrix.det (oddMinor11 r z) = 2*r^6*z^2 - 4*r^6 - 2*r^5*z^2 - 7*r^5 + 9*r^4*z^2 + 4*r^4 - 10*r^3*z^2 + 6*r^3 + 12*r^2*z^2 - 3*r^2 - 15*r*z^2 + 6*z^2 := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor11, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor9 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![-2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z;
     0, r*z - z, r^3 + r^2 - r, 2*r^3 + 2*r^2 - r - 1;
     2, 0, 1, 2]

private theorem oddMinor9_det (r z : K) : Matrix.det (oddMinor9 r z) = -4*r^9*z^2 + 4*r^9 + 8*r^8*z^2 + 16*r^8 - 14*r^7*z^2 + 8*r^7 - 14*r^6*z^2 - 27*r^6 + 39*r^5*z^2 - 11*r^5 - 43*r^4*z^2 + 20*r^4 + 48*r^3*z^2 - 3*r^3 - 26*r^2*z^2 - r^2 - r*z^2 + 3*z^2 := by

  have h1 : (oddMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (1 : Fin 4)) =
      oddMinor4 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (oddMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      oddMinor10 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor9 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      oddMinor11 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor9 r z) =
      ∑ j : Fin 4, (-1 : K)^(2+j.val)*(oddMinor9 r z) 2 j *
        (![0, -z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3), 2*(-2*r^6 + 4*r^5*z^2 - r^5 - 7*r^4*z^2 + 2*r^4 + 14*r^3*z^2 - r^3 - 16*r^2*z^2 + 2*r^2 + 3*r*z^2 - r + 2*z^2), 2*r^6*z^2 - 4*r^6 - 2*r^5*z^2 - 7*r^5 + 9*r^4*z^2 + 4*r^4 - 10*r^3*z^2 + 6*r^3 + 12*r^2*z^2 - 3*r^2 - 15*r*z^2 + 6*z^2] j) := by
    rw [Matrix.det_succ_row _ (2 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [oddMinor9]

    · change (-1 : K)^3*(r*z - z)*
          Matrix.det ((oddMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (1 : Fin 4))) = (-1 : K)^3*(r*z - z)*(-z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3))
      exact congrArg (fun d : K => (-1 : K)^3*(r*z - z)*d)
        ((congrArg Matrix.det h1).trans (oddMinor4_det r z))

    · change (-1 : K)^4*(r^3 + r^2 - r)*
          Matrix.det ((oddMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^4*(r^3 + r^2 - r)*(2*(-2*r^6 + 4*r^5*z^2 - r^5 - 7*r^4*z^2 + 2*r^4 + 14*r^3*z^2 - r^3 - 16*r^2*z^2 + 2*r^2 + 3*r*z^2 - r + 2*z^2))
      exact congrArg (fun d : K => (-1 : K)^4*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h2).trans (oddMinor10_det r z))

    · change (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*
          Matrix.det ((oddMinor9 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(2*r^6*z^2 - 4*r^6 - 2*r^5*z^2 - 7*r^5 + 9*r^4*z^2 + 4*r^4 - 10*r^3*z^2 + 6*r^3 + 12*r^2*z^2 - 3*r^2 - 15*r*z^2 + 6*z^2)
      exact congrArg (fun d : K => (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor11_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^2*(0)*(0)+((-1 : K)^3*(r*z - z)*(-z*(4*r^6 - 18*r^5 + 8*r^4 + 14*r^3 - 9*r + 3))+((-1 : K)^4*(r^3 + r^2 - r)*(2*(-2*r^6 + 4*r^5*z^2 - r^5 - 7*r^4*z^2 + 2*r^4 + 14*r^3*z^2 - r^3 - 16*r^2*z^2 + 2*r^2 + 3*r*z^2 - r + 2*z^2))+((-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(2*r^6*z^2 - 4*r^6 - 2*r^5*z^2 - 7*r^5 + 9*r^4*z^2 + 4*r^4 - 10*r^3*z^2 + 6*r^3 + 12*r^2*z^2 - 3*r^2 - 15*r*z^2 + 6*z^2)+0)))) = -4*r^9*z^2 + 4*r^9 + 8*r^8*z^2 + 16*r^8 - 14*r^7*z^2 + 8*r^7 - 14*r^6*z^2 - 27*r^6 + 39*r^5*z^2 - 11*r^5 - 43*r^4*z^2 + 20*r^4 + 48*r^3*z^2 - 3*r^3 - 26*r^2*z^2 - r^2 - r*z^2 + 3*z^2
  norm_num
  ring

private def oddMinor1 (r z : K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2 - 1, 0;
     -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, r*z - z, r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     2, 0, 1, 0, 2]

private theorem oddMinor1_det (r z : K) : Matrix.det (oddMinor1 r z) = 8*r^12 + 48*r^11 - 32*r^10*z^2 + 68*r^10 + 56*r^9*z^2 - 62*r^9 - 92*r^8*z^2 - 142*r^8 + 16*r^7*z^4 + 42*r^7*z^2 + 45*r^7 - 76*r^6*z^4 + 192*r^6*z^2 + 89*r^6 + 172*r^5*z^4 - 141*r^5*z^2 - 21*r^5 - 224*r^4*z^4 - 143*r^4*z^2 - 20*r^4 + 156*r^3*z^4 + 162*r^3*z^2 + 4*r^3 - 40*r^2*z^4 - 38*r^2*z^2 + r^2 - 8*r*z^4 - 3*r*z^2 + 4*z^4 + z^2 := by

  have h1 : (oddMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      oddMinor2 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (oddMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      oddMinor6 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor1 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      oddMinor9 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor1 r z) =
      ∑ j : Fin 5, (-1 : K)^(0+j.val)*(oddMinor1 r z) 0 j *
        (![0, r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1), 2*z*(-4*r^9 + 4*r^7 + 8*r^6*z^2 - 14*r^6 - 30*r^5*z^2 - 3*r^5 + 56*r^4*z^2 + 16*r^4 - 56*r^3*z^2 + 9*r^3 + 22*r^2*z^2 - 15*r^2 + 2*r*z^2 + 2*r - 2*z^2 + 1), -4*r^9*z^2 + 4*r^9 + 8*r^8*z^2 + 16*r^8 - 14*r^7*z^2 + 8*r^7 - 14*r^6*z^2 - 27*r^6 + 39*r^5*z^2 - 11*r^5 - 43*r^4*z^2 + 20*r^4 + 48*r^3*z^2 - 3*r^3 - 26*r^2*z^2 - r^2 - r*z^2 + 3*z^2, 0] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 5)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [oddMinor1]

    · change (-1 : K)^1*(r^3 + 3*r^2 - 2*r)*
          Matrix.det ((oddMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (1 : Fin 5))) = (-1 : K)^1*(r^3 + 3*r^2 - 2*r)*(r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^1*(r^3 + 3*r^2 - 2*r)*d)
        ((congrArg Matrix.det h1).trans (oddMinor2_det r z))

    · change (-1 : K)^2*(r*z - z)*
          Matrix.det ((oddMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (2 : Fin 5))) = (-1 : K)^2*(r*z - z)*(2*z*(-4*r^9 + 4*r^7 + 8*r^6*z^2 - 14*r^6 - 30*r^5*z^2 - 3*r^5 + 56*r^4*z^2 + 16*r^4 - 56*r^3*z^2 + 9*r^3 + 22*r^2*z^2 - 15*r^2 + 2*r*z^2 + 2*r - 2*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^2*(r*z - z)*d)
        ((congrArg Matrix.det h2).trans (oddMinor6_det r z))

    · change (-1 : K)^3*(2*r^2 - 1)*
          Matrix.det ((oddMinor1 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (3 : Fin 5))) = (-1 : K)^3*(2*r^2 - 1)*(-4*r^9*z^2 + 4*r^9 + 8*r^8*z^2 + 16*r^8 - 14*r^7*z^2 + 8*r^7 - 14*r^6*z^2 - 27*r^6 + 39*r^5*z^2 - 11*r^5 - 43*r^4*z^2 + 20*r^4 + 48*r^3*z^2 - 3*r^3 - 26*r^2*z^2 - r^2 - r*z^2 + 3*z^2)
      exact congrArg (fun d : K => (-1 : K)^3*(2*r^2 - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor9_det r z))

    · simp [oddMinor1]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(0)*(0)+((-1 : K)^1*(r^3 + 3*r^2 - 2*r)*(r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1))+((-1 : K)^2*(r*z - z)*(2*z*(-4*r^9 + 4*r^7 + 8*r^6*z^2 - 14*r^6 - 30*r^5*z^2 - 3*r^5 + 56*r^4*z^2 + 16*r^4 - 56*r^3*z^2 + 9*r^3 + 22*r^2*z^2 - 15*r^2 + 2*r*z^2 + 2*r - 2*z^2 + 1))+((-1 : K)^3*(2*r^2 - 1)*(-4*r^9*z^2 + 4*r^9 + 8*r^8*z^2 + 16*r^8 - 14*r^7*z^2 + 8*r^7 - 14*r^6*z^2 - 27*r^6 + 39*r^5*z^2 - 11*r^5 - 43*r^4*z^2 + 20*r^4 + 48*r^3*z^2 - 3*r^3 - 26*r^2*z^2 - r^2 - r*z^2 + 3*z^2)+((-1 : K)^4*(0)*(0)+0))))) = 8*r^12 + 48*r^11 - 32*r^10*z^2 + 68*r^10 + 56*r^9*z^2 - 62*r^9 - 92*r^8*z^2 - 142*r^8 + 16*r^7*z^4 + 42*r^7*z^2 + 45*r^7 - 76*r^6*z^4 + 192*r^6*z^2 + 89*r^6 + 172*r^5*z^4 - 141*r^5*z^2 - 21*r^5 - 224*r^4*z^4 - 143*r^4*z^2 - 20*r^4 + 156*r^3*z^4 + 162*r^3*z^2 + 4*r^3 - 40*r^2*z^4 - 38*r^2*z^2 + r^2 - 8*r*z^4 - 3*r*z^2 + 4*z^4 + z^2
  norm_num
  ring

private def oddMinor14 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^2 - 1;
     0, -2*r^2*z + 3*r*z - z, 2*r^2*z - 2*z;
     0, 2, 2]

private theorem oddMinor14_det (r z : K) : Matrix.det (oddMinor14 r z) = -6*z^2*(r - 1)*(2*r - 1)*(4*r + 1) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor14, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor15 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^2*z - 2*z;
     0, -2*r^2*z + 3*r*z - z, 2*r^3 + 2*r^2 - r - 1;
     0, 2, 0]

private theorem oddMinor15_det (r z : K) : Matrix.det (oddMinor15 r z) = -6*z*(r + 1)*(2*r - 1)*(2*r^2 - 1) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor15, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor13 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![6*r*z - 3*z, -2*r^3 + 3*r^2 - r, 2*r^2*z - 2*z, 2*r^2 - 1;
     0, -2*r^2*z + 3*r*z - z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, 0, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, 2, 0, 2]

private theorem oddMinor13_det (r z : K) : Matrix.det (oddMinor13 r z) = -6*z*(2*r - 1)*(-4*r^6 - 8*r^5 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r + 2*z^2 - 1) := by

  have h2 : (oddMinor13 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      oddMinor14 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor13 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      oddMinor15 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor13 r z) =
      ∑ j : Fin 4, (-1 : K)^(2+j.val)*(oddMinor13 r z) 2 j *
        (![0, 0, -6*z^2*(r - 1)*(2*r - 1)*(4*r + 1), -6*z*(r + 1)*(2*r - 1)*(2*r^2 - 1)] j) := by
    rw [Matrix.det_succ_row _ (2 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [oddMinor13]

    · simp [oddMinor13]

    · change (-1 : K)^4*(2*r*z - 2*z)*
          Matrix.det ((oddMinor13 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^4*(2*r*z - 2*z)*(-6*z^2*(r - 1)*(2*r - 1)*(4*r + 1))
      exact congrArg (fun d : K => (-1 : K)^4*(2*r*z - 2*z)*d)
        ((congrArg Matrix.det h2).trans (oddMinor14_det r z))

    · change (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*
          Matrix.det ((oddMinor13 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-6*z*(r + 1)*(2*r - 1)*(2*r^2 - 1))
      exact congrArg (fun d : K => (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor15_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^2*(0)*(0)+((-1 : K)^3*(0)*(0)+((-1 : K)^4*(2*r*z - 2*z)*(-6*z^2*(r - 1)*(2*r - 1)*(4*r + 1))+((-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-6*z*(r + 1)*(2*r - 1)*(2*r^2 - 1))+0)))) = -6*z*(2*r - 1)*(-4*r^6 - 8*r^5 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r + 2*z^2 - 1)
  norm_num
  ring

private def oddMinor17 (r z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r;
     0, -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z;
     0, 2, 1]

private theorem oddMinor17_det (r z : K) : Matrix.det (oddMinor17 r z) = -3*z^2*(2*r - 1)*(2*r^3 + 3*r - 3) := by

  rw [Matrix.det_fin_three]
  simp only [oddMinor17, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def oddMinor16 (r z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r, 2*r^2 - 1;
     0, -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^2*z - 2*z;
     0, 0, r^3 + r^2 - r, 2*r^3 + 2*r^2 - r - 1;
     0, 2, 1, 2]

private theorem oddMinor16_det (r z : K) : Matrix.det (oddMinor16 r z) = 3*z^2*(2*r - 1)*(4*r^6 - 4*r^5 + 2*r^4 + 14*r^3 - 13*r^2 - 2*r + 3) := by

  have h2 : (oddMinor16 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      oddMinor14 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor16 r z).submatrix
      (Fin.succAbove (2 : Fin 4)) (Fin.succAbove (3 : Fin 4)) =
      oddMinor17 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor16 r z) =
      ∑ j : Fin 4, (-1 : K)^(2+j.val)*(oddMinor16 r z) 2 j *
        (![0, 0, -6*z^2*(r - 1)*(2*r - 1)*(4*r + 1), -3*z^2*(2*r - 1)*(2*r^3 + 3*r - 3)] j) := by
    rw [Matrix.det_succ_row _ (2 : Fin 4)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · simp [oddMinor16]

    · simp [oddMinor16]

    · change (-1 : K)^4*(r^3 + r^2 - r)*
          Matrix.det ((oddMinor16 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (2 : Fin 4))) = (-1 : K)^4*(r^3 + r^2 - r)*(-6*z^2*(r - 1)*(2*r - 1)*(4*r + 1))
      exact congrArg (fun d : K => (-1 : K)^4*(r^3 + r^2 - r)*d)
        ((congrArg Matrix.det h2).trans (oddMinor14_det r z))

    · change (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*
          Matrix.det ((oddMinor16 r z).submatrix (Fin.succAbove (2 : Fin 4))
            (Fin.succAbove (3 : Fin 4))) = (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-3*z^2*(2*r - 1)*(2*r^3 + 3*r - 3))
      exact congrArg (fun d : K => (-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor17_det r z))

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^2*(0)*(0)+((-1 : K)^3*(0)*(0)+((-1 : K)^4*(r^3 + r^2 - r)*(-6*z^2*(r - 1)*(2*r - 1)*(4*r + 1))+((-1 : K)^5*(2*r^3 + 2*r^2 - r - 1)*(-3*z^2*(2*r - 1)*(2*r^3 + 3*r - 3))+0)))) = 3*z^2*(2*r - 1)*(4*r^6 - 4*r^5 + 2*r^4 + 14*r^3 - 13*r^2 - 2*r + 3)
  norm_num
  ring

private def oddMinor12 (r z : K) : Matrix (Fin 5) (Fin 5) K :=
  !![6*r^2 - 3*r, 0, r*z - z, 2*r^2 - 1, 0;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     0, -2*r^2*z + 3*r*z - z, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, 0, r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, 2, 1, 0, 2]

private theorem oddMinor12_det (r z : K) : Matrix.det (oddMinor12 r z) = -3*(2*r - 1)*(8*r^10 - 8*r^9*z^2 + 32*r^9 + 24*r^8*z^2 + 20*r^8 - 56*r^7*z^2 - 46*r^7 + 8*r^6*z^2 - 34*r^6 + 90*r^5*z^2 + 25*r^5 + 16*r^4*z^4 - 8*r^4*z^2 + 13*r^4 - 44*r^3*z^4 - 78*r^3*z^2 - 5*r^3 + 36*r^2*z^4 + 29*r^2*z^2 - r^2 - 4*r*z^4 + 4*r*z^2 - 4*z^4 - z^2) := by

  have h0 : (oddMinor12 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      oddMinor2 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (oddMinor12 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      oddMinor13 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h3 : (oddMinor12 r z).submatrix
      (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      oddMinor16 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddMinor12 r z) =
      ∑ j : Fin 5, (-1 : K)^(0+j.val)*(oddMinor12 r z) 0 j *
        (![r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1), 0, -6*z*(2*r - 1)*(-4*r^6 - 8*r^5 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r + 2*z^2 - 1), 3*z^2*(2*r - 1)*(4*r^6 - 4*r^5 + 2*r^4 + 14*r^3 - 13*r^2 - 2*r + 3), 0] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 5)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^0*(6*r^2 - 3*r)*
          Matrix.det ((oddMinor12 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (0 : Fin 5))) = (-1 : K)^0*(6*r^2 - 3*r)*(r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1))
      exact congrArg (fun d : K => (-1 : K)^0*(6*r^2 - 3*r)*d)
        ((congrArg Matrix.det h0).trans (oddMinor2_det r z))

    · simp [oddMinor12]

    · change (-1 : K)^2*(r*z - z)*
          Matrix.det ((oddMinor12 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (2 : Fin 5))) = (-1 : K)^2*(r*z - z)*(-6*z*(2*r - 1)*(-4*r^6 - 8*r^5 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r + 2*z^2 - 1))
      exact congrArg (fun d : K => (-1 : K)^2*(r*z - z)*d)
        ((congrArg Matrix.det h2).trans (oddMinor13_det r z))

    · change (-1 : K)^3*(2*r^2 - 1)*
          Matrix.det ((oddMinor12 r z).submatrix (Fin.succAbove (0 : Fin 5))
            (Fin.succAbove (3 : Fin 5))) = (-1 : K)^3*(2*r^2 - 1)*(3*z^2*(2*r - 1)*(4*r^6 - 4*r^5 + 2*r^4 + 14*r^3 - 13*r^2 - 2*r + 3))
      exact congrArg (fun d : K => (-1 : K)^3*(2*r^2 - 1)*d)
        ((congrArg Matrix.det h3).trans (oddMinor16_det r z))

    · simp [oddMinor12]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(6*r^2 - 3*r)*(r*(-8*r^8 + 8*r^7*z^2 - 32*r^7 - 16*r^6*z^2 - 20*r^6 + 40*r^5*z^2 + 46*r^5 - 16*r^4*z^2 + 34*r^4 - 42*r^3*z^2 - 25*r^3 - 4*r^2*z^2 - 13*r^2 + 50*r*z^2 + 5*r - 20*z^2 + 1))+((-1 : K)^1*(0)*(0)+((-1 : K)^2*(r*z - z)*(-6*z*(2*r - 1)*(-4*r^6 - 8*r^5 + 8*r^3*z^2 + 8*r^3 - 14*r^2*z^2 + 3*r^2 + 4*r*z^2 - 2*r + 2*z^2 - 1))+((-1 : K)^3*(2*r^2 - 1)*(3*z^2*(2*r - 1)*(4*r^6 - 4*r^5 + 2*r^4 + 14*r^3 - 13*r^2 - 2*r + 3))+((-1 : K)^4*(0)*(0)+0))))) = -3*(2*r - 1)*(8*r^10 - 8*r^9*z^2 + 32*r^9 + 24*r^8*z^2 + 20*r^8 - 56*r^7*z^2 - 46*r^7 + 8*r^6*z^2 - 34*r^6 + 90*r^5*z^2 + 25*r^5 + 16*r^4*z^4 - 8*r^4*z^2 + 13*r^4 - 44*r^3*z^4 - 78*r^3*z^2 - 5*r^3 + 36*r^2*z^4 + 29*r^2*z^2 - r^2 - 4*r*z^4 + 4*r*z^2 - 4*z^4 - z^2)
  norm_num
  ring

def oddCore (r z : K) : Matrix (Fin 6) (Fin 6) K :=
  !![2, 0, 1, 0, 0, 0;
     6*r^2 - 3*r, 0, r^3 + 3*r^2 - 2*r, r*z - z, 2*r^2 - 1, 0;
     6*r*z - 3*z, -2*r^3 + 3*r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, r^3 + 3*r^2 - 2*r, 2*r^2*z - 2*z, 2*r^2 - 1;
     0, -2*r^2*z + 3*r*z - z, r^3 + r^2 - r, r^3*z - r^2*z + 3*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1, 2*r^2*z - 2*z;
     0, 0, r*z - z, r^3 + r^2 - r, 2*r*z - 2*z, 2*r^3 + 2*r^2 - r - 1;
     0, 2, 0, 1, 0, 2]

theorem oddCore_det (r z : K) : Matrix.det (oddCore r z) = 16*r^12 + 48*r^11 - 16*r^10*z^2 - 32*r^10 - 56*r^9*z^2 - 148*r^9 + 224*r^8*z^2 + 52*r^8 + 32*r^7*z^4 - 132*r^7*z^2 + 156*r^7 - 152*r^6*z^4 - 132*r^6*z^2 - 74*r^6 + 248*r^5*z^4 + 36*r^5*z^2 - 45*r^5 - 136*r^4*z^4 + 158*r^4*z^2 + 29*r^4 - 36*r^3*z^4 - 84*r^3*z^2 - r^3 + 52*r^2*z^4 - 13*r^2*z^2 - r^2 - 4*r*z^4 + 12*r*z^2 - 4*z^4 - z^2 := by

  have h0 : (oddCore r z).submatrix
      (Fin.succAbove (0 : Fin 6)) (Fin.succAbove (0 : Fin 6)) =
      oddMinor1 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : (oddCore r z).submatrix
      (Fin.succAbove (0 : Fin 6)) (Fin.succAbove (2 : Fin 6)) =
      oddMinor12 r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have he : Matrix.det (oddCore r z) =
      ∑ j : Fin 6, (-1 : K)^(0+j.val)*(oddCore r z) 0 j *
        (![8*r^12 + 48*r^11 - 32*r^10*z^2 + 68*r^10 + 56*r^9*z^2 - 62*r^9 - 92*r^8*z^2 - 142*r^8 + 16*r^7*z^4 + 42*r^7*z^2 + 45*r^7 - 76*r^6*z^4 + 192*r^6*z^2 + 89*r^6 + 172*r^5*z^4 - 141*r^5*z^2 - 21*r^5 - 224*r^4*z^4 - 143*r^4*z^2 - 20*r^4 + 156*r^3*z^4 + 162*r^3*z^2 + 4*r^3 - 40*r^2*z^4 - 38*r^2*z^2 + r^2 - 8*r*z^4 - 3*r*z^2 + 4*z^4 + z^2, 0, -3*(2*r - 1)*(8*r^10 - 8*r^9*z^2 + 32*r^9 + 24*r^8*z^2 + 20*r^8 - 56*r^7*z^2 - 46*r^7 + 8*r^6*z^2 - 34*r^6 + 90*r^5*z^2 + 25*r^5 + 16*r^4*z^4 - 8*r^4*z^2 + 13*r^4 - 44*r^3*z^4 - 78*r^3*z^2 - 5*r^3 + 36*r^2*z^4 + 29*r^2*z^2 - r^2 - 4*r*z^4 + 4*r*z^2 - 4*z^4 - z^2), 0, 0, 0] j) := by
    rw [Matrix.det_succ_row _ (0 : Fin 6)]
    apply Finset.sum_congr rfl
    intro j _
    fin_cases j

    · change (-1 : K)^0*(2)*
          Matrix.det ((oddCore r z).submatrix (Fin.succAbove (0 : Fin 6))
            (Fin.succAbove (0 : Fin 6))) = (-1 : K)^0*(2)*(8*r^12 + 48*r^11 - 32*r^10*z^2 + 68*r^10 + 56*r^9*z^2 - 62*r^9 - 92*r^8*z^2 - 142*r^8 + 16*r^7*z^4 + 42*r^7*z^2 + 45*r^7 - 76*r^6*z^4 + 192*r^6*z^2 + 89*r^6 + 172*r^5*z^4 - 141*r^5*z^2 - 21*r^5 - 224*r^4*z^4 - 143*r^4*z^2 - 20*r^4 + 156*r^3*z^4 + 162*r^3*z^2 + 4*r^3 - 40*r^2*z^4 - 38*r^2*z^2 + r^2 - 8*r*z^4 - 3*r*z^2 + 4*z^4 + z^2)
      exact congrArg (fun d : K => (-1 : K)^0*(2)*d)
        ((congrArg Matrix.det h0).trans (oddMinor1_det r z))

    · simp [oddCore]

    · change (-1 : K)^2*(1)*
          Matrix.det ((oddCore r z).submatrix (Fin.succAbove (0 : Fin 6))
            (Fin.succAbove (2 : Fin 6))) = (-1 : K)^2*(1)*(-3*(2*r - 1)*(8*r^10 - 8*r^9*z^2 + 32*r^9 + 24*r^8*z^2 + 20*r^8 - 56*r^7*z^2 - 46*r^7 + 8*r^6*z^2 - 34*r^6 + 90*r^5*z^2 + 25*r^5 + 16*r^4*z^4 - 8*r^4*z^2 + 13*r^4 - 44*r^3*z^4 - 78*r^3*z^2 - 5*r^3 + 36*r^2*z^4 + 29*r^2*z^2 - r^2 - 4*r*z^4 + 4*r*z^2 - 4*z^4 - z^2))
      exact congrArg (fun d : K => (-1 : K)^2*(1)*d)
        ((congrArg Matrix.det h2).trans (oddMinor12_det r z))

    · simp [oddCore]

    · simp [oddCore]

    · simp [oddCore]

  rw [he]
  simp only [Fin.sum_univ_succ]
  change ((-1 : K)^0*(2)*(8*r^12 + 48*r^11 - 32*r^10*z^2 + 68*r^10 + 56*r^9*z^2 - 62*r^9 - 92*r^8*z^2 - 142*r^8 + 16*r^7*z^4 + 42*r^7*z^2 + 45*r^7 - 76*r^6*z^4 + 192*r^6*z^2 + 89*r^6 + 172*r^5*z^4 - 141*r^5*z^2 - 21*r^5 - 224*r^4*z^4 - 143*r^4*z^2 - 20*r^4 + 156*r^3*z^4 + 162*r^3*z^2 + 4*r^3 - 40*r^2*z^4 - 38*r^2*z^2 + r^2 - 8*r*z^4 - 3*r*z^2 + 4*z^4 + z^2)+((-1 : K)^1*(0)*(0)+((-1 : K)^2*(1)*(-3*(2*r - 1)*(8*r^10 - 8*r^9*z^2 + 32*r^9 + 24*r^8*z^2 + 20*r^8 - 56*r^7*z^2 - 46*r^7 + 8*r^6*z^2 - 34*r^6 + 90*r^5*z^2 + 25*r^5 + 16*r^4*z^4 - 8*r^4*z^2 + 13*r^4 - 44*r^3*z^4 - 78*r^3*z^2 - 5*r^3 + 36*r^2*z^4 + 29*r^2*z^2 - r^2 - 4*r*z^4 + 4*r*z^2 - 4*z^4 - z^2))+((-1 : K)^3*(0)*(0)+((-1 : K)^4*(0)*(0)+((-1 : K)^5*(0)*(0)+0)))))) = 16*r^12 + 48*r^11 - 16*r^10*z^2 - 32*r^10 - 56*r^9*z^2 - 148*r^9 + 224*r^8*z^2 + 52*r^8 + 32*r^7*z^4 - 132*r^7*z^2 + 156*r^7 - 152*r^6*z^4 - 132*r^6*z^2 - 74*r^6 + 248*r^5*z^4 + 36*r^5*z^2 - 45*r^5 - 136*r^4*z^4 + 158*r^4*z^2 + 29*r^4 - 36*r^3*z^4 - 84*r^3*z^2 - r^3 + 52*r^2*z^4 - 13*r^2*z^2 - r^2 - 4*r*z^4 + 12*r*z^2 - 4*z^4 - z^2
  norm_num
  ring

theorem odd_core_det (r z : K) :
    Matrix.det (oddCore r z) = oddRaw r z := by
  rw [oddCore_det]
  unfold oddRaw
  ring

#check odd_core_det

theorem even_core_nonsingular (r z : K)
    (hr : r ≠ 0) (hr1 : r-1 ≠ 0) (hz0 : z ≠ 0)
    (hg : evenFactor r ≠ 0) (hz : (r-1)*z^2 = r*(r^2+r-1)) :
    Matrix.det (evenCore r z) ≠ 0 := by
  rw [even_core_det, even_raw_eq r z hz]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hr) hr1) hz0) hg

theorem odd_core_nonsingular (r z : K)
    (hr : r ≠ 0) (hg : oddFactor r ≠ 0)
    (hz : (r-1)*z^2 = r*(r^2+r-1)) :
    Matrix.det (oddCore r z) ≠ 0 := by
  rw [odd_core_det]
  intro he
  have h := odd_raw_eq r z hz
  rw [he, mul_zero] at h
  exact (mul_ne_zero (neg_ne_zero.mpr hr) hg) h.symm


end HoldoutConicJacobian
end
end
