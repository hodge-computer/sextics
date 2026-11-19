import Proposal.GenericConic
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal

/-!
The nonsingular full coefficient matrix produces a polynomial normal vector.
This is the full-coefficient counterpart of fqlx's shared polynomial-normal
lemma, as also used in 1337isnot1337's accepted crossed-ternary construction.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open Polynomial HoldoutConstruction
open scoped BigOperators

theorem full_polynomial_combination_one {R : Type*} [CommRing R] {n : ℕ} (hn : 0<n)
    (Q : Fin n → Polynomial R) (bound : ∀ j, (Q j).natDegree < n)
    (hunit : IsUnit (Matrix.det (fun i j : Fin n => (Q j).coeff i.val))) :
    ∃ u : Fin n → R, ∑ j, C (u j)*Q j=1 := by
  let J : Matrix (Fin n) (Fin n) R := fun i j => (Q j).coeff i.val
  let e : Fin n → R := Pi.single ⟨0,hn⟩ 1
  let u := J⁻¹.mulVec e
  have hu : J.mulVec u=e := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv J hunit,Matrix.one_mulVec]
  refine ⟨u,?_⟩
  ext k
  by_cases hk : k<n
  · have h := congrFun hu ⟨k,hk⟩
    simp only [Matrix.mulVec,dotProduct,J,e,Pi.single_apply] at h
    rw [show (∑ j, (Q j).coeff k*u j) = ∑ j, u j*(Q j).coeff k by
      apply Finset.sum_congr rfl
      intro j _
      ring] at h
    simpa [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_one,
      Fin.ext_iff] using h
  · have hQ (j : Fin n) : (Q j).coeff k=0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (bound j) (Nat.le_of_not_gt hk))
    have hk0 : k ≠ 0 := by omega
    simp [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,hQ,Polynomial.coeff_one,hk0]

def conicGradient : Fin 5 → Polynomial CoefficientField :=
  gradient (C conicAlpha) (C conicBeta) conicCurve

lemma conicGradient_column_bound (j : Fin 13) :
    (conicGradient (slotCoordinate j)*X^slotDegree j).natDegree < 13 := by
  unfold conicGradient conicCurve
  rw [curveEval_eq_valueCurve]
  fin_cases j <;> dsimp [slotCoordinate,slotDegree,gradient,valueCurve]
  all_goals compute_degree <;> norm_num

theorem conicNormal_exists : ∃ N : Fin 5 → Polynomial CoefficientField,
    polynomialPairing conicGradient N=1 ∧ ∀ i, i ≠ 0 → (N i).coeff 0=0 := by
  obtain ⟨u,hu⟩ := full_polynomial_combination_one (by decide : 0<13)
    (fun j => conicGradient (slotCoordinate j)*X^slotDegree j)
    conicGradient_column_bound conic_jacobian_unit
  let v : Fin 13 → Fin 5 → Polynomial CoefficientField :=
    fun j => Pi.single (slotCoordinate j) (X^slotDegree j)
  have hp (j : Fin 13) : polynomialPairing conicGradient (v j)=
      conicGradient (slotCoordinate j)*X^slotDegree j := by
    simp [v,polynomialPairing,Pi.single_apply]
  refine ⟨fun i => 0+∑ j, C (u j)*v j i,?_,?_⟩
  · rw [polynomialPairing_affine]
    have hz : polynomialPairing conicGradient (fun _ : Fin 5 => 0)=0 := by
      simp [polynomialPairing]
    rw [hz,zero_add]
    simpa only [hp] using hu
  · intro i hi
    have hz (j : Fin 13) : (C (u j)*v j i).coeff 0=0 := by
      fin_cases j <;> fin_cases i <;> simp_all [v,slotCoordinate,slotDegree,Pi.single_apply,
        Polynomial.coeff_C_mul,Polynomial.coeff_X_pow]
    simp [Polynomial.finsetSum_coeff,hz]

def conicNormal : Fin 5 → Polynomial CoefficientField := Classical.choose conicNormal_exists
lemma conicNormal_pairing : polynomialPairing conicGradient conicNormal=1 :=
  (Classical.choose_spec conicNormal_exists).1
lemma conicNormal_constant_zero (i : Fin 5) (hi : i ≠ 0) :
    (conicNormal i).coeff 0=0 := (Classical.choose_spec conicNormal_exists).2 i hi

lemma conicNormal_constant_nonzero : (conicNormal 0).coeff 0 ≠ 0 := by
  have hp := congrArg (Polynomial.constantCoeff : Polynomial CoefficientField →+* CoefficientField)
    conicNormal_pairing
  unfold polynomialPairing at hp
  rw [map_sum,map_one] at hp
  simp only [map_mul,Polynomial.constantCoeff_apply] at hp
  rw [Fin.sum_univ_succ] at hp
  have hz (i : Fin 4) : (conicNormal i.succ).coeff 0=0 :=
    conicNormal_constant_zero i.succ (Fin.succ_ne_zero i)
  simp only [hz,mul_zero,Finset.sum_const_zero,add_zero] at hp
  intro h
  rw [h,mul_zero] at hp
  exact zero_ne_one hp

#print axioms conicNormal_pairing
end DeformedConic
