import Proposal.BundleNormal

/-! A conic with an actual finite coefficient solution, its polynomial
equation, and its polynomial normal. The coefficient field is kept explicit.
This packages the target-specific incidence without assuming a certificate. -/

noncomputable section

namespace HoldoutBundle
open Polynomial HoldoutConstruction

variable {E : Type*} [Field E] [CharZero E]

structure ConicFamily (a b : E) (k : Fin 4 → E) where
  coefficients : Fin 12 → E
  endpoint_relation : endpoint a b k = 0
  endpoint_nonzero : k 0 ≠ 0
  equations : ∀ i : Fin 12,
    MvPolynomial.eval₂Hom (RingHom.id E) coefficients
      (HoldoutBundle.equations a b k i) = 0
  jacobian : IsUnit (Matrix.det (fun i j : Fin 12 =>
    MvPolynomial.eval₂Hom (RingHom.id E) coefficients
      (MvPolynomial.pderiv j (HoldoutBundle.equations a b k i))))

namespace ConicFamily
variable {a b : E} {k : Fin 4 → E} (p : ConicFamily a b k)

def curve : Fin 5 → Polynomial E := valueCurve k p.coefficients

theorem curve_constant (i : Fin 5) :
    (p.curve i).coeff 0 = ![k 0, 0, k 1, k 2, k 3] i :=
  valueCurve_constant k p.coefficients i

theorem curve_endpoint (i : Fin 3) : (p.curve i.succ.succ).coeff 0 = k i.succ := by
  rw [curve_constant]
  fin_cases i <;> rfl

@[simp] theorem curve_time : p.curve 1 = X := rfl

theorem curve_equation : K (C a) (C b) p.curve = 0 := by
  have hdeg : (K (C a) (C b) p.curve).natDegree ≤ 12 := by
    have h := K_eval_natDegree_le (RingHom.id E) a b k p.coefficients
    rw [curveEval_eq_valueCurve] at h
    exact h
  have hc : (K (C a) (C b) p.curve).coeff 0 = 0 := by
    change Polynomial.constantCoeff (K (C a) (C b) p.curve) = 0
    rw [K_map]
    simpa [Polynomial.constantCoeff_apply, curve_constant, K, endpoint] using
      p.endpoint_relation
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n = 0
  · simpa [hn] using hc
  · by_cases hb : n ≤ 12
    · have he := p.equations ⟨n-1, by omega⟩
      rw [equations_eval, curveEval_eq_valueCurve] at he
      have hn' : n-1+1=n := by omega
      simpa only [RingHom.id_apply, hn', curve] using he
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hdeg (by omega))

theorem exists_normal : ∃ psi : Fin 5 → Polynomial E,
    polynomialPairing (gradient (C a) (C b) p.curve) psi = 1 ∧
    ∀ i, (psi i).coeff 0 = if i = 0 then (6 * k 0 ^ 5)⁻¹ else 0 :=
  exists_polynomial_normal a b k p.coefficients p.endpoint_nonzero p.jacobian

def normal : Fin 5 → Polynomial E := Classical.choose p.exists_normal

theorem normal_pairing : polynomialPairing (gradient (C a) (C b) p.curve) p.normal = 1 :=
  (Classical.choose_spec p.exists_normal).1

theorem normal_constant (i : Fin 5) :
    (p.normal i).coeff 0 = if i = 0 then (6 * k 0 ^ 5)⁻¹ else 0 :=
  (Classical.choose_spec p.exists_normal).2 i

include p in
theorem normal_endpoint_nonzero : (6 : E) * k 0 ^ 5 ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero 5 p.endpoint_nonzero)

end ConicFamily
end HoldoutBundle

#print axioms HoldoutBundle.ConicFamily.curve_equation
#print axioms HoldoutBundle.ConicFamily.normal_pairing
