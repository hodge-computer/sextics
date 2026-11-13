import HodgeComputer.Constructions.HoldoutCover.CurveFamily
import HodgeComputer.Constructions.HoldoutCover.CurveJacobianScaling

/- Source component: CurveGradientBlocks -/
section
/-! The coefficient Jacobian at the conic seed splits into two sparse
six by six blocks. This calculation is generic over a field. -/

noncomputable section

namespace HoldoutConicIncidence

variable {R : Type*} [CommRing R]

/-- The four gradient entries which can vary when the X1 polynomial is fixed. -/
def sparseGradient (q u v a : R) : Fin 5 → Polynomial R :=
  ![6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4,
    0,
    Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10,
    3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8,
    Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7]

section Blocks

variable {K : Type*} [Field K]

def gradientCoefficientMatrix (q u v a : K) : Matrix Index Index K :=
  fun i j => (sparseGradient q u v a (coefficientCoordinate j) *
    Polynomial.X^coefficientDegree j).coeff (equationDegree i)

theorem gradientCoefficientMatrix_blocks (q u v a : K) :
    gradientCoefficientMatrix q u v a = Matrix.fromBlocks
      (HoldoutConicJacobian.originalEven q u v a) 0 0
      (HoldoutConicJacobian.originalOdd q u v a) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 2 = 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 2 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 2 = 6*a + u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 4 = 3*a*u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 4 = -3*a^2 + 6*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 4 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 4 = 6*a*q^2 + 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 4 = 6*a + u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 6 = 3*q*u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 6 = a*v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 6 = -6*a*q + 3*q^4 + 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 6 = -3*a^2 + 6*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 6 = 6*a + 6*q^3 + v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 6 = 6*a*q^2 + 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 8 = q*v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 8 = 3*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 8 = -6*a*q + 3*q^4 + 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 8 = 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 8 = 6*a + 6*q^3 + v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 10 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 10 = 3*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 10 = 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 12 = 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 12 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 2 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 4 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 6 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 8 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 10 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 12 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 5 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^2).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^2).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^2).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^4).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^1).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^3).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 1 = 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 1 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 1 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 3 = 3*a*u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 3 = -3*a^2 + 6*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 3 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 3 = 6*a + u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 3 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 5 = 3*q*u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 5 = a*v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 5 = -6*a*q + 3*q^4 + 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 5 = -3*a^2 + 6*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 5 = 6*a*q^2 + 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 5 = 6*a + u
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 7 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 7 = q*v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 7 = 3*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 7 = -6*a*q + 3*q^4 + 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 7 = 6*a + 6*q^3 + v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 7 = 6*a*q^2 + 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 9 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 9 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 9 = 3*q^2
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 9 = 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 9 = 6*a + 6*q^3 + v
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

  · change ((6 + Polynomial.C (3*u*a)*Polynomial.X^2 + Polynomial.C (3*u*q)*Polynomial.X^4)*Polynomial.X^1).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (v*a)*Polynomial.X^4 + Polynomial.C (v*q)*Polynomial.X^6 + 6*Polynomial.X^10)*Polynomial.X^1).coeff 11 = 6
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^1).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((3 + Polynomial.C (6*q^2-3*a^2)*Polynomial.X^2 +
      Polynomial.C (3*q^4+6-6*a*q)*Polynomial.X^4 +
      Polynomial.C (3*q^2)*Polynomial.X^6 + 3*Polynomial.X^8)*Polynomial.X^3).coeff 11 = 3
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^2).coeff 11 = 0
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]

  · change ((Polynomial.C (u+6*a)*Polynomial.X + Polynomial.C (6*q+6*a*q^2)*Polynomial.X^3 +
      Polynomial.C (v+6*a+6*q^3)*Polynomial.X^5 + Polynomial.C (6*q)*Polynomial.X^7)*Polynomial.X^4).coeff 11 = 6*q
    norm_num only [Polynomial.coeff_mul_X_pow', Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ,
      Polynomial.coeff_C, ite_true, ite_false]
    ring

end Blocks

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.gradientCoefficientMatrix_blocks
end
end
