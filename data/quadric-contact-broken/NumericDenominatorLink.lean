import Proposal.RatioDataLink
import Proposal.RatioDenominatorLink
import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootSpecialization

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
namespace QuadricContactNumericDenominator
open Polynomial

/-- A version of the matrix specialization theorem with the target polynomial
identified by an equality, avoiding dependent casts in all consumers. -/
theorem map_leftMulMatrix_target {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
    {n : ℕ} (hn : p.natDegree = n) (hm : q.natDegree = n)
    (he : p.map f = q) (x : AdjoinRoot p) :
    (Algebra.leftMulMatrix (AdjoinRootSpecialization.basis p hp hn) x).map f =
      Algebra.leftMulMatrix (AdjoinRootSpecialization.basis q hq hm)
        (AdjoinRoot.map f p q (he ▸ dvd_refl q) x) := by
  subst q
  exact AdjoinRootSpecialization.map_leftMulMatrix f p hp hn hm x

open QuadricContactRatioInverse QuadricContactRatioDenominator

/-- The rational-to-complex map on the concrete 27-line algebra. -/
def numericToComplex : AdjoinRoot GenericSpecialization.P →+* Auxiliary :=
  AdjoinRoot.map (Rat.castHom ℂ) GenericSpecialization.P linePolynomial
    (QuadricContactRatioDataLink.polynomial_cast ▸ dvd_refl linePolynomial)

theorem numericToComplex_mk (g : Polynomial ℚ) :
    numericToComplex (AdjoinRoot.mk GenericSpecialization.P g) =
      AdjoinRoot.mk linePolynomial (g.map (Rat.castHom ℂ)) := by
  simp only [numericToComplex, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.eval₂_map]
  rfl

theorem rational_monic : GenericSpecialization.P.Monic := by
  apply Polynomial.monic_of_injective (Rat.castHom ℂ).injective
  rw [QuadricContactRatioDataLink.polynomial_cast]
  exact polynomial_monic

theorem rational_degree : GenericSpecialization.P.natDegree = 27 := by
  rw [← Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℂ).injective,
    QuadricContactRatioDataLink.polynomial_cast]
  exact polynomial_degree

def rationalSumMatrix : Matrix (Fin 27) (Fin 27) ℚ :=
  Algebra.leftMulMatrix
    (AdjoinRootSpecialization.basis GenericSpecialization.P rational_monic rational_degree)
    (AdjoinRoot.mk GenericSpecialization.P
      (GenericSpecialization.line_x + GenericSpecialization.line_y))

theorem rational_matrix_specializes :
    rationalSumMatrix.map (Rat.castHom ℂ) = sumMatrix := by
  have h := map_leftMulMatrix_target (Rat.castHom ℂ) GenericSpecialization.P linePolynomial
    rational_monic polynomial_monic rational_degree polynomial_degree
    QuadricContactRatioDataLink.polynomial_cast
    (AdjoinRoot.mk GenericSpecialization.P
      (GenericSpecialization.line_x + GenericSpecialization.line_y))
  change rationalSumMatrix.map (Rat.castHom ℂ) =
    Algebra.leftMulMatrix basis (numericToComplex (AdjoinRoot.mk GenericSpecialization.P
      (GenericSpecialization.line_x + GenericSpecialization.line_y))) at h
  rw [numericToComplex_mk, QuadricContactRatioDataLink.sum_cast,
    ← AdjoinRoot.aeval_eq] at h
  exact h

end QuadricContactNumericDenominator

#print axioms QuadricContactNumericDenominator.rational_matrix_specializes
