import Proposal.RatioMatrixInverse
import Proposal.GenericSpecialization

noncomputable section
namespace QuadricContactRatioDataLink
open Polynomial QuadricContactRatioInverse

theorem polynomial_cast :
    GenericSpecialization.P.map (Rat.castHom ℂ) = linePolynomial := by
  apply Polynomial.funext
  intro z
  simp only [GenericSpecialization.P, linePolynomial, Polynomial.eval_map,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval_one, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem sum_cast :
    (GenericSpecialization.line_x + GenericSpecialization.line_y).map (Rat.castHom ℂ) = lineSum := by
  apply Polynomial.funext
  intro z
  simp only [GenericSpecialization.line_x, GenericSpecialization.line_y, lineSum,
    Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval_one, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    map_neg, map_div₀, map_ofNat, map_one]
  ring

end QuadricContactRatioDataLink

#print axioms QuadricContactRatioDataLink.polynomial_cast
#print axioms QuadricContactRatioDataLink.sum_cast
