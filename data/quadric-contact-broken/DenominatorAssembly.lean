import Proposal.TargetDenominator
import Proposal.MatrixBezout

noncomputable section
namespace QuadricContactDenominator
open MvPolynomial HodgeComputer

/-- Final denominator check from a small cubic inverse certificate at the
single auxiliary parameter point. There is no expanded determinant hypothesis. -/
theorem denominator_legal_of_matrix_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (D : Poly) (M K : Matrix n n (Polynomial ℂ)) (κ : ℂ)
    (hκ : κ ≠ 0)
    (hK : (M ^ 3 + (140 : Polynomial ℂ) • M +
      (536 : Polynomial ℂ) • (1 : Matrix n n (Polynomial ℂ))) * K = 1)
    (hD : (toUni D).map specialize = Polynomial.C κ *
      ((2 * Polynomial.X ^ 2 : Polynomial ℂ) • (1 : Matrix n n (Polynomial ℂ)) - M).det) :
    IsRelPrime targetF D := by
  apply denominator_legal D
  rw [hD]
  apply IsRelPrime.mul_right
  · exact ((isUnit_iff_ne_zero.mpr hκ).map Polynomial.C).isRelPrime_right
  · have h := QuadricContactMatrixBezout.relPrime_cubic_det
      (2 * Polynomial.X ^ 2 : Polynomial ℂ) 140 536 M K hK
    apply h.of_dvd_left
    refine ⟨8, ?_⟩
    unfold fFiber
    ring

end QuadricContactDenominator

#print axioms QuadricContactDenominator.denominator_legal_of_matrix_inverse
