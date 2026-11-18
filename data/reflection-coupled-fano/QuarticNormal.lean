import Proposal.QuarticIncidence
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal

/-!
An exact polynomial normal vector for the weighted quartic incidence.
This instantiates the shared positive-coefficient linear algebra with all
24 positive coefficients and the exact six-coordinate quotient gradient.
No power-series or approximate normal vector is used.
-/

noncomputable section
namespace ReflectionCoupledFano
open Polynomial HoldoutConstruction
open scoped BigOperators

variable {R : Type*} [Field R]

def coordinateVariation (j : Index) : Fin 6 → Polynomial R :=
  Pi.single j.1 (Polynomial.X^(j.2.val+1))

def constantNormal (c : R) (x : Fin 6 → R) : Fin 6 → Polynomial R :=
  Pi.single 0 (Polynomial.C ((gradient c x 0)⁻¹))

private theorem pairing_single (G : Fin 6 → Polynomial R)
    (i : Fin 6) (p : Polynomial R) :
    polynomialPairing G (Pi.single i p) = G i*p := by
  simp [polynomialPairing, Pi.single_apply]

theorem coordinateVariation_pairing (G : Fin 6 → Polynomial R) (j : Index) :
    polynomialPairing G (coordinateVariation j) = G j.1*Polynomial.X^(j.2.val+1) :=
  pairing_single G _ _

theorem coordinateVariation_constant (j : Index) (i : Fin 6) :
    (coordinateVariation (R := R) j i).coeff 0 = 0 := by
  by_cases hi : i = j.1
  · simp [coordinateVariation, hi, Polynomial.coeff_X_pow]
  · simp [coordinateVariation, hi]

theorem coordinateVariation_pairing_constant (G : Fin 6 → Polynomial R) (j : Index) :
    (polynomialPairing G (coordinateVariation j)).coeff 0 = 0 := by
  simp only [polynomialPairing, Polynomial.finsetSum_coeff, Polynomial.mul_coeff_zero,
    coordinateVariation_constant, mul_zero, Finset.sum_const_zero]

theorem exists_polynomial_normal (c : R) (x : Fin 6 → R) (v : Index → R)
    (hg : gradient c x 0 ≠ 0)
    (hj : IsUnit (Matrix.det (fun i j : Index =>
      MvPolynomial.eval₂Hom (RingHom.id R) v (MvPolynomial.pderiv j (equations c x i))))) :
    ∃ psi : Fin 6 → Polynomial R,
      polynomialPairing (gradient (Polynomial.C c) (valueCurve x v)) psi = 1 ∧
      ∀ i, (psi i).coeff 0 = if i = 0 then (gradient c x 0)⁻¹ else 0 := by
  let G := gradient (Polynomial.C c) (valueCurve x v)
  let b := constantNormal c x
  have hconstant : (polynomialPairing G b).coeff 0 = 1 := by
    rw [show b = Pi.single (0 : Fin 6) (Polynomial.C ((gradient c x 0)⁻¹)) from rfl,
      pairing_single, Polynomial.coeff_mul_C]
    rw [gradient_constant c x v 0, mul_inv_cancel₀ hg]
  have hbaseBound : (polynomialPairing G b).natDegree ≤ 24 := by
    rw [show b = Pi.single (0 : Fin 6) (Polynomial.C ((gradient c x 0)⁻¹)) from rfl,
      pairing_single]
    exact (Polynomial.natDegree_mul_C_le _ _).trans (gradient_degree_le c x v 0)
  have hvariationBound (j : Index) :
      (polynomialPairing G (coordinateVariation j)).natDegree ≤ 24 := by
    rw [coordinateVariation_pairing]
    exact gradientVariation_degree_le c x v j
  have hmatrix : positiveCoefficientMatrix equationDegree
      (fun j => polynomialPairing G (coordinateVariation j)) =
      fun i j : Index => MvPolynomial.eval₂Hom (RingHom.id R) v
        (MvPolynomial.pderiv j (equations c x i)) := by
    ext i j
    rw [positiveCoefficientMatrix, coordinateVariation_pairing]
    exact (equations_pderiv_eval₂ (RingHom.id R) c x v i j).symm
  have hinvertible : IsUnit (positiveCoefficientMatrix equationDegree
      (fun j => polynomialPairing G (coordinateVariation j))).det := by
    rwa [hmatrix]
  obtain ⟨u, hu⟩ := polynomial_normal_from_coefficients G b coordinateVariation
    equationDegree 24 (fun n hn h24 => equationDegree_covers (n := n) hn h24) hconstant
    (coordinateVariation_pairing_constant G) hbaseBound hvariationBound hinvertible
  let psi : Fin 6 → Polynomial R :=
    fun i => b i + ∑ j, Polynomial.C (u j)*coordinateVariation j i
  refine ⟨psi, hu, ?_⟩
  intro i
  simp only [psi, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, coordinateVariation_constant, mul_zero,
    Finset.sum_const_zero, add_zero]
  by_cases hi : i = 0 <;> simp [b, constantNormal, hi]

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.exists_polynomial_normal
