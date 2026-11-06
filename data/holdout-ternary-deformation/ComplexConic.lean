import Proposal.DeformedConic
import HodgeComputer.Constructions.PolynomialCurves.ComplexPoint

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace DeformedConic
open HoldoutConstruction
local instance complexConic_local_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

def integerParameters : Fin 3 → ℤ := ![4,4,4]
lemma integerParameters_cast : (fun j => (Int.castRingHom K) (integerParameters j))=parameters := by
  funext j
  fin_cases j <;> norm_num [integerParameters,parameters]
def integerEquations : Fin 13 → MvPolynomial (Fin 13) ℤ :=
  equations 1 0 integerParameters

lemma integer_seed_eval (P : MvPolynomial (Fin 13) ℤ) :
    MvPolynomial.aeval seed P =
      MvPolynomial.eval₂Hom (RingHom.id K) seed (MvPolynomial.map (Int.castRingHom K) P) := by
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl
lemma integer_seed_equations (i : Fin 13) :
    MvPolynomial.aeval seed (integerEquations i)=0 := by
  rw [integer_seed_eval,integerEquations,equations_map]
  simpa only [map_one,map_zero,integerParameters_cast] using seed_equations i
lemma integer_seed_jacobian : IsUnit (Matrix.det (fun i j =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (integerEquations j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integerEquations j)))=seedJacobian.transpose := by
    funext i j
    rw [integer_seed_eval,integerEquations,equations_pderiv_map]
    simp only [map_one,map_zero,integerParameters_cast,seedJacobian,Matrix.transpose_apply]
  rw [hm,Matrix.det_transpose]
  exact seed_jacobian_unit

instance integer_incidence_nontrivial : Nontrivial (SquareEtaleRing integerEquations) :=
  square_system_jacobian_nontrivial integerEquations seed
    integer_seed_equations integer_seed_jacobian

theorem exists_complex_conic_coefficients :
    ∃ v : Fin 13 → ℂ, (∀ i, MvPolynomial.aeval v (integerEquations i)=0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval v
        (MvPolynomial.pderiv i (integerEquations j)))) :=
  complex_point_of_etale_nontrivial integerEquations

open Polynomial
def complexCurve (v : Fin 13 → ℂ) : Fin 5 → Polynomial ℂ :=
  curveEval integerParameters (Int.castRingHom ℂ) v

def complexJacobian (v : Fin 13 → ℂ) : Matrix (Fin 13) (Fin 13) ℂ := fun i j =>
  (gradient 1 0 (complexCurve v) (slotCoordinate j)*X^slotDegree j).coeff i.val

theorem exists_complex_conic : ∃ v : Fin 13 → ℂ,
    H 1 0 (complexCurve v)=0 ∧ IsUnit (complexJacobian v).det := by
  obtain ⟨v,hv,hj⟩ := exists_complex_conic_coefficients
  refine ⟨v,?_,?_⟩
  · ext n
    rw [Polynomial.coeff_zero]
    by_cases hn : n<13
    · have h := hv ⟨n,hn⟩
      change MvPolynomial.eval₂Hom (Int.castRingHom ℂ) v
        (equations 1 0 integerParameters ⟨n,hn⟩)=0 at h
      rw [equations_eval] at h
      simpa only [map_one,map_zero,complexCurve] using h
    · have hb : (H (1 : Polynomial ℂ) 0 (complexCurve v)).natDegree ≤ 12 := by
        simpa only [map_one,map_zero,complexCurve] using
          H_eval_natDegree_le (Int.castRingHom ℂ) 1 0 integerParameters v
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hb (by omega))
  · have he : (fun i j : Fin 13 => MvPolynomial.aeval v
        (MvPolynomial.pderiv i (integerEquations j)))=(complexJacobian v).transpose := by
      funext i j
      change MvPolynomial.eval₂Hom (Int.castRingHom ℂ) v
        (MvPolynomial.pderiv i (equations 1 0 integerParameters j)) = _
      rw [equations_pderiv_eval]
      simp only [map_one,map_zero,complexJacobian,complexCurve,Matrix.transpose_apply]
    rw [he,Matrix.det_transpose] at hj
    exact hj

#print axioms exists_complex_conic_coefficients
#print axioms exists_complex_conic
end DeformedConic
